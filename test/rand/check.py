#!/usr/bin/env python3
"""gen.pyの文書を調べる．使い方: check.py basename
1行で結果を出す：OK/NG，問題の一覧，網羅の印．"""
import json, re, subprocess, sys
from collections import Counter, defaultdict

base = sys.argv[1]
meta = json.load(open(base + '.json'))
log = open(base + '.log', encoding='utf-8', errors='replace').read()
prob = []
cover = set()
limits = set()

# ---- ログ
if re.search(r'^! ', log, re.M):
    prob.append('tex-error:' + re.search(r'^! (.*)$', log, re.M).group(1)[:40])
if 'Float(s) lost' in log:
    prob.append('float-lost')
ov = re.findall(r'Overfull \\vbox \(([\d.]+)pt too high\)', log)
# LaTeXが通常どおり組んだ段（\@makecol）のはみ出し：evenendが印を付けて出す．
# jlreqで脚注と上下のフロート・段抜きのフロートが入ると，evenendがなくても起きる
latex = len(re.findall(r'overfull column built by LaTeX', log))
if latex:
    limits.add('latex-column-overfull')
if len(ov) - latex > 0:
    prob.append(f'overfull-vbox:{len(ov) - latex}')
m = re.search(r'LAYOUT left=([\d.]+) width=([\d.]+) sep=([\d.]+) bottom=([\d.]+) bs=([\d.]+)', log.replace('\n', ''))
if not m:
    print('NG no-layout'); sys.exit()
left, width, sep, bottom, bs = map(float, m.groups())
flat = log.replace('\n', '')
warn = re.findall(r'Package evenend Warning: ([^.]*)', flat)
for w in warn:
    if w.startswith('Could not balance'):
        # 材料（分割しない脚注など）がページの残りに入り切らず，LaTeXの組み方に戻した
        limits.add('could-not-balance')
    else:
        prob.append('warn:' + w[:30])

# 箱の中の段組：最右段など以外の段の下端がそろったか
for m in re.finditer(r'box column (\d+): ([\d.]+)pt \(no stretch\)', flat):
    limits.add('box-nostretch')  # 伸ばせるグルーがない（行送りにそろわない中身）
if 'box balanced' in flat:
    cover.add('box-columns')
if 'lowered by the heading space' in flat:
    cover.add('heading-lowered')  # headingskip=block：段組を見出しの上アキの分だけ下げた

# 揃えた段組ごとの下端（blockcheck.pyと同じ）
for bm in re.finditer(r'evenend: balanced at ([\d.]+)pt(.*?)(?=evenend: balanced at|$)', flat):
    h = float(bm.group(1))
    pl = re.findall(r'column \d+ placed ([\d.]+)pt(?: \(([^)]*)\))?', bm.group(2))
    cols = [None if t in ('pushed', 'floats only') else float(a) for a, t in pl]
    for i, v in enumerate(cols[:-1]):
        t = pl[i][1]
        # 中身のある最後の段（後の段がすべて空）は短くてよい
        rest_empty = all(c is not None and c == 0 for c in cols[i + 1:])
        if v is not None and v > 0 and abs(v - h) > 0.5 and not (t == 'ragged' and rest_empty):
            if t == 'no stretch' and meta['class'] != 'jlreq':
                limits.add('nostretch')  # 行送りにそろわない組版で伸ばせるグルーがない
            elif t == 'no stretch' and not meta['floatgrid'] and not meta['gyoudori']:
                limits.add('nofloatgrid')  # floatgrid=falseで，フロートの後の行が行送りからずれる
            elif t == 'no stretch' and 'retrying (without floatgrid)' in flat:
                limits.add('floatgrid-dropped')  # floatgridのままでは入り切らなかった
            elif t == 'column break':
                cover.add('column-break')  # \columnbreakで終わる段（下を空ける）
            elif t == 'blocked':
                limits.add('blocked')  # 次の段の先頭の材料（本文中の図，長い脚注の付いた行）が入らない
            else:
                prob.append(f'bottom:{v:.1f}/{h:.1f}' + (f'({t})' if t else ''))
    if cols and cols[-1] is not None and cols[-1] > h + 0.01:
        prob.append(f'last-taller:{cols[-1]:.1f}/{h:.1f}')

# ---- PDF
xml = subprocess.run(['pdftotext', '-bbox', base + '.pdf', '-'], capture_output=True, text=True).stdout
pages = []
for pg in re.findall(r'<page[^>]*>(.*?)</page>', xml, re.S):
    pages.append([(float(a), float(b), float(c), float(d), t) for a, b, c, d, t in
                  re.findall(r'<word xMin="([\d.]+)" yMin="([\d.]+)" xMax="([\d.]+)" yMax="([\d.]+)">([^<]*)</word>', pg)])
occ = defaultdict(list)  # (種類, 番号, 端) -> [(ページ, 語)]
for pno, W in enumerate(pages, 1):
    for w in W:
        for k, n, e in re.findall(r'Z([BERNFWCD])(\d+)([LR]?)Z', w[4]):
            occ[(k, int(n), e)].append((pno, w))

blk_of = {}
for j, b in enumerate(meta['blocks']):
    for p in b['paras']: blk_of[('B', p)] = j; blk_of[('E', p)] = j
    for f in b['fns']: blk_of[('R', f)] = j; blk_of[('N', f)] = j
    for f in b['floats']: blk_of[('F', f['id'])] = j
    for f in b['dbl']: blk_of[('W', f)] = j
last = len(meta['blocks']) - 1

# 材料がちょうど1回ずつ
for j, b in enumerate(meta['blocks']):
    keys = [('B', p, '') for p in b['paras']] + [('E', p, '') for p in b['paras']] \
         + [('R', f, '') for f in b['fns']] + [('N', f, '') for f in b['fns']] \
         + [('F', f['id'], e) for f in b['floats'] for e in 'LR'] \
         + [('W', f, e) for f in b['dbl'] for e in 'LR']
    for k in keys:
        if len(occ[k]) != 1:
            prob.append(f'count:{k[0]}{k[1]}{k[2]}={len(occ[k])}')

# 段組ごとの段間（\evenendcolumns[columnsep=...]で変えたブロックはjsonにbp単位である）
def bsep(j):
    v = meta['blocks'][j].get('sep')
    return sep if v is None else v
def cw(N, s=None):
    s = sep if s is None else s
    return (width - (N - 1) * s) / N
def col(x, N, s=None):
    s = sep if s is None else s
    # 段間が0のとき，段の先頭の語が境界ちょうどにあるので，少し余裕を持たせる
    c = int((x - left + s / 2 + 0.5) // (cw(N, s) + s))
    return max(0, min(N - 1, c))
def blockwords(pno, j):
    """ページpnoにあるブロックjの本文の目印"""
    return [w for (k, n, e), L in occ.items() if k in 'BE' and blk_of.get((k, n)) == j
            for (p, w) in L if p == pno]

# ページpnにあるブロックjを，evenendが揃えたか．ページの最後のブロックは，そのページに
# 最終ページとしての揃えの記録があるか，ブロックとしての揃えの記録がページのブロックの
# 数だけあるときに揃えたとみなす（\columnbreakでページが埋まった後に文書が終わるなど，
# LaTeXがそのまま組んだページもある）．それより前のブロックは揃えて積んである
def block_balanced(pno, j):
    # ページにあるブロック（本文だけでなく，脚注・図の目印でも数える）
    J = sorted(set(blk_of[(k, nn)] for (k, nn, e), L in occ.items() if (k, nn) in blk_of
                   for (pp, w) in L if pp == pno) | {j})
    if j != J[-1]:
        return True
    final = re.search(r'Page %d: columns balanced at [\d.]+pt on' % pno, flat)
    nblk = len(re.findall(r'Page %d: columns balanced at [\d.]+pt \(block\)' % pno, flat))
    return bool(final) or nblk >= len(J)

# 本文の字の高さ（本文の目印の語から）
bodyh = Counter(round(w[3] - w[1], 1) for (k, n, e), L in occ.items() if k in 'BE' for p, w in L)
bodyh = bodyh.most_common(1)[0][0] if bodyh else 10

# ---- 脚注
for j, b in enumerate(meta['blocks']):
    N = b['N']
    for f in b['fns']:
        if len(occ[('R', f, '')]) != 1 or len(occ[('N', f, '')]) != 1: continue
        (pr, r), = occ[('R', f, '')]
        (pn, t), = occ[('N', f, '')]
        if pr != pn:
            cover.add('fn-next-page'); continue
        c = col(t[0], N, bsep(j))
        # evenendが揃えたページだけ（LaTeXが組んだページでは，入り切らない脚注を
        # TeXが次の段へ送ることがある）
        if col(r[0], N, bsep(j)) != c and block_balanced(pn, j):
            prob.append(f'fn{f}-column')
        W = pages[pn - 1]
        # 同じブロックの本文・図が脚注より下にない（同じ段）
        for w in blockwords(pn, j):
            if col(w[0], N, bsep(j)) == c and w[1] > t[3] + 0.5:
                prob.append(f'fn{f}-text-below'); break
        # 後のブロックの本文が脚注より上にない
        for jj in range(j + 1, len(meta['blocks'])):
            if any(w[3] < t[1] - 0.5 for w in blockwords(pn, jj)):
                prob.append(f'fn{f}-above-later-block'); break
        # footnote=pageの最後の段組では版面の下端（evenendが組んだページだけ．
        # LaTeXが通常どおり組んだページの脚注はLaTeXの担当）
        balanced_pages = set(int(x) for x in re.findall(r'Page (\d+): columns balanced at [\d.]+pt on', flat))
        if meta['footnote'] == 'page' and j == last and pn in balanced_pages:
            fl = [w for w in W if w[1] >= t[1] - 0.5 and col(w[0], N, bsep(j)) == c
                  and abs(w[0] - t[0]) < cw(N, bsep(j)) and w[3] < bottom + 5]
            fb = max([w[3] for w in fl] or [t[3]])
            if abs(fb - bottom) > 4:
                if fb > bottom and limits & {'latex-column-overfull'}:
                    limits.add('fn-pushed-by-latex-overfull')  # LaTeXが組んだ段のはみ出しで押し出された
                else:
                    prob.append(f'fn{f}-not-at-bottom:{fb:.1f}/{bottom:.1f}')
        # 同じ段に同じブロックの図があるか（網羅の印）
        for g in b['floats']:
            L = occ[('F', g['id'], 'L')]
            if L and L[0][0] == pn and col(L[0][1][0], N, bsep(j)) == c:
                cover.add('float+fn-same-column')

# ---- 図：幅と，ブロックの範囲に収まっているか
for j, b in enumerate(meta['blocks']):
    for kind, ids, N in (('F', [g['id'] for g in b['floats']], b['N']), ('W', b['dbl'], 1)):
        for g in ids:
            L, Rr = occ[(kind, g, 'L')], occ[(kind, g, 'R')]
            if len(L) != 1 or len(Rr) != 1: continue
            (pl, wl), (_, wr) = L[0], Rr[0]
            span = wr[2] - wl[0]
            if kind == 'F' and span > cw(b['N'], bsep(j)) + 1:
                prob.append(f'{kind}{g}-too-wide')
            for jj in range(len(meta['blocks'])):
                if jj == j: continue
                bw = blockwords(pl, jj)
                if jj < j and any(w[1] > wl[3] + 0.5 for w in bw):
                    prob.append(f'{kind}{g}-above-block{jj+1}'); break
                if jj > j and any(w[3] < wl[1] - 0.5 for w in bw):
                    prob.append(f'{kind}{g}-below-block{jj+1}'); break

# ---- 行送りの位置（jlreqでfloatgridのとき．evenendが全体を組んだページだけ．
#      段抜きの図のあるページは除く）
if meta['class'] == 'jlreq' and (meta['floatgrid'] or meta['gyoudori']):
    full = set(int(p) for p in re.findall(r'Page (\d+): columns balanced at [\d.]+pt on', flat))
    for pno in sorted(full):
        if pno > len(pages): continue
        W = pages[pno - 1]
        if any(re.search(r'ZW\d+', w[4]) for w in W): continue
        caps = set(round(w[3], 1) for w in W if re.search(r'Z[CF]\d+', w[4]))
        ys = sorted(set(round(w[3], 2) for w in W if abs((w[3] - w[1]) - bodyh) < 0.2
                        and round(w[3], 1) not in caps and w[3] < bottom + 1))
        if not ys: continue
        y0 = ys[0]
        off = [y for y in ys if min((y - y0) % bs, bs - (y - y0) % bs) > 0.2]
        if off:
            if 'retrying (without floatgrid)' in flat:
                limits.add('floatgrid-dropped')  # floatgridのままでは入り切らなかった（満杯のページ）
            elif not meta['floatgrid']:
                limits.add('nofloatgrid')  # gyoudoriはtcolorboxなどの箱を行ドリしない
            else:
                prob.append(f'grid-p{pno}:{len(off)}')
        cover.add('grid-checked')

tags = [meta['class'], 'N0=%d' % meta['N0'], meta['footnote'], 'fg' if meta['floatgrid'] else 'nofg',
        'gy' if meta['gyoudori'] else '-', 'blocks=%d' % len(meta['blocks'])]
prob = [re.sub(r'\s+', '_', x) for x in prob]
print(('OK ' if not prob else 'NG ') + ' '.join(tags) + ' | ' + ' '.join(sorted(set(prob))) + ' | '
      + ' '.join(sorted(cover)) + ' | ' + ' '.join('limit:' + l for l in sorted(limits)))
