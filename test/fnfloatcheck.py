#!/usr/bin/env python3
"""フロートと脚注が同じ段に入るときの配置を調べる（fnfloat.shの文書用）．
各ページについて，
・字が重なっていないか
・脚注（FNTEXT）が参照位置（FNREF）と同じ段にあり，その段の中で一番下にあるか
  （本文や図（FIGMARK，図の見出し）より下．段数の切り換えの後の段組（ONECOL以降）は除く）
・フロートと脚注が同じ段にあるか（網羅の確認）
を調べる．・footnote=pageで，脚注が最後の段組にあれば，版面の下端（ログのTEXTBOTTOM）にあるか
使い方: fnfloatcheck.py file.pdf 段数 [page|column file.log]"""
import re, subprocess, sys
pdf, N = sys.argv[1], int(sys.argv[2])
fnmode = sys.argv[3] if len(sys.argv) > 3 else None
tb = None
if len(sys.argv) > 4:
    m = re.search(r'TEXTBOTTOM ([\d.]+)', open(sys.argv[4], errors='replace').read())
    tb = float(m.group(1)) if m else None
pages = int(re.search(r'Pages:\s+(\d+)', subprocess.run(['pdfinfo', pdf], capture_output=True, text=True).stdout).group(1))
problems, together = [], 0
# ONECOL（切り換えの後の段組）が現れるページ：それより前のページの段組は途中のブロック
onecol_pages = [pg for pg in range(1, pages + 1)
                if 'ONECOL' in subprocess.run(['pdftotext', '-f', str(pg), '-l', str(pg), pdf, '-'],
                                              capture_output=True, text=True).stdout]
# 版面の左右の端：全ページの字の左端の最小値と右端の最大値
allw = subprocess.run(['pdftotext', '-bbox', pdf, '-'], capture_output=True, text=True).stdout
LO = min(float(x) for x in re.findall(r'xMin="([\d.]+)"', allw))
HI = max(float(x) for x in re.findall(r'xMax="([\d.]+)"', allw))
for pg in range(1, pages + 1):
    out = subprocess.run(['pdftotext', '-bbox', '-f', str(pg), '-l', str(pg), pdf, '-'], capture_output=True, text=True).stdout
    W = [(float(a), float(b), float(c), float(d), t) for a, b, c, d, t in
         re.findall(r'<word xMin="([\d.]+)" yMin="([\d.]+)" xMax="([\d.]+)" yMax="([\d.]+)">([^<]*)</word>', out)]
    if not W: continue
    # 重なり
    for i in range(len(W)):
        for j in range(i + 1, len(W)):
            a, b = W[i], W[j]
            # 約物の詰め（脚注記号の括弧など）による小さな重なりは数えない
            if min(a[2], b[2]) - max(a[0], b[0]) > 3 and min(a[3], b[3]) - max(a[1], b[1]) > 0.5:
                problems.append(f'p{pg}: overlap "{a[4][:10]}" / "{b[4][:10]}"')
    # 切り換えの後の段組（ONECOLから下）と，切り換えの前の段組（TWOCOLより上）は除く
    cut = min([w[1] for w in W if 'ONECOL' in w[4]] or [1e9])
    top = min([w[1] for w in W if 'TWOCOL' in w[4]] or [-1])
    lastblock = not any(q >= pg for q in onecol_pages)  # 最後の段組か
    W = [w for w in W if w[3] <= cut + 0.1 and w[1] >= top - 0.1 and not w[4].isdigit()]
    if not W: continue
    # 段の境目は版面から決める（版面は紙面の中央にあるとし，左右の端は全ページの
    # 本文の字から求める）
    lo, hi = LO, HI
    cw = (hi - lo) / N
    if N == 2:
        # 2段組では，字の中央が紙面の中央より左か右かで段を決める
        pw = float(re.search(r'<page width="([\d.]+)"', out).group(1))
        col = lambda w: 0 if (w[0] + w[2]) / 2 < pw / 2 else 1
    else:
        col = lambda w: min(N - 1, int((w[0] + 1 - lo) / cw))
    fn = [w for w in W if 'FNTEXT' in w[4]]
    ref = [w for w in W if 'FNREF' in w[4]]
    figs = [w for w in W if 'FIGMARK' in w[4]]
    for f in fn:
        c = col(f)
        if ref and all(col(r) != c for r in ref):
            problems.append(f'p{pg}: footnote in column {c+1} but reference elsewhere')
        # 脚注の段で，脚注より下に脚注以外の字があってはならない
        fnlines = [w for w in W if col(w) == c and abs(w[0] - f[0]) < cw and w[1] >= f[1] - 0.5]
        # 脚注本体（FNTEXTを含む行と，その後の脚注の行）は字が小さいので区別する
        big = [w for w in fnlines if (w[3] - w[1]) > (f[3] - f[1]) + 0.5]
        if big:
            problems.append(f'p{pg}: text below footnote in column {c+1}: "{big[0][4][:12]}"')
        if any(col(g) == c for g in figs):
            together += 1
        # footnote=pageの最後の段組：脚注の最終行が版面の下端に来る
        if fnmode == 'page' and lastblock and tb is not None:
            fl = [w for w in W if col(w) == c and w[1] >= f[1] - 0.5 and abs(w[0] - f[0]) < cw]
            bottom = max(w[3] for w in fl)
            if abs(bottom - tb) > 4:
                problems.append(f'p{pg}: footnote bottom {bottom:.1f} not at text bottom {tb:.1f}')
for p in problems: print(p)
print(f'problems: {len(problems)}, float+footnote in one column: {together}')
