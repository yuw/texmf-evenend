#!/usr/bin/env python3
"""乱数でevenendのテスト文書を作る．
使い方: gen.py seed 出力のbasename
basename.texとbasename.json（文書の構造：ブロック，段数，段落・脚注・図の番号）を書く．

目印（pdftotextで拾う）：
  ZB<段落>Z / ZE<段落>Z   段落の先頭と末尾
  ZR<脚注>Z / ZN<脚注>Z   脚注の参照位置と脚注の本文の先頭
  ZF<図>LZ / ZF<図>RZ     図の中身の左端と右端（幅は作ったときの段幅の0.9倍）
  ZW<図>LZ / ZW<図>RZ     段抜きの図
"""
import json, random, sys

seed, base = int(sys.argv[1]), sys.argv[2]
R = random.Random(seed)
R2 = random.Random(seed * 7 + 3)  # 追加の要素用（Rの列を変えない）

cls = R.choice(['jlreq', 'jlreq', 'ltjsarticle', 'article'])
ja = cls != 'article'
N0 = R.choice([2, 2, 3])
fnmode = R.choice(['page', 'column'])
floatgrid = R.choice([True, True, False])
gyoudori = cls == 'jlreq' and R.random() < 0.25
extra = seed >= 100000
extra2 = seed >= 200000  # さらに：tcolorbox，\columnbreak，\evenendcolumns*  # 追加の要素（\evenendclearpage，\onecolumn，\twocolumn[...]，hyperref，長い脚注）
hyper = extra and R.random() < 0.3
title = extra and R.random() < 0.3

JA = ['吾輩は猫である．', '名前はまだ無い．', 'どこで生れたかとんと見当がつかぬ．',
      '何でも薄暗いじめじめした所でニャーニャー泣いていた事だけは記憶している．',
      '吾輩はここで始めて人間というものを見た．',
      'しかもあとで聞くとそれは書生という人間中で一番獰悪な種族であったそうだ．']
EN = ['Lorem ipsum dolor sit amet, consectetuer adipiscing elit.',
      'Ut purus elit, vestibulum ut, placerat ac, adipiscing vitae, felis.',
      'Curabitur dictum gravida mauris.', 'Nam arcu libero, nonummy eget, consectetuer id, vulputate a, magna.',
      'Donec vehicula augue eu neque.', 'Pellentesque habitant morbi tristique senectus et netus.']

def sentences(k):
    src = JA if ja else EN
    return ('' if ja else ' ').join(R.choice(src) for _ in range(k))

meta = {'seed': seed, 'class': cls, 'N0': N0, 'footnote': fnmode, 'floatgrid': floatgrid,
        'gyoudori': gyoudori, 'blocks': [], 'hyperref': hyper, 'title': title}
out = []
opts = ['debug', f'footnote={fnmode}', f'floatgrid={"true" if floatgrid else "false"}']
if seed >= 300000:
    opts.append('headingskip=block')  # 見出しの上アキを段組の間のアキに含める
if N0 != 2:
    opts.append(f'columns={N0}')
docopt = 'twocolumn' + (',fontsize=10pt' if cls == 'jlreq' else '')
out.append(r'\documentclass[%s]{%s}' % (docopt, cls))
if gyoudori:
    out.append(r'\usepackage[float]{gyoudori}')
out.append(r'\usepackage[%s]{evenend}' % ','.join(opts))
if hyper:
    out.append(r'\usepackage{hyperref}')
if extra2:
    out.append(r'\usepackage[most]{tcolorbox}\tcbset{fontupper=\small,fonttitle=\small}')
if gyoudori:
    out.append(r'''\makeatletter
\AddToHook{evenend/deferredfloat}{\@gyoudori@floattop
  \@gyoudori@float@set\evenendfloatbox\@gyoudori@floatpos\@gyoudori@floatshift}
\makeatother''')
out.append(r'''\makeatletter
\AtBeginDocument{\typeout{LAYOUT left=\strip@pt\dimexpr(1in+\hoffset+\oddsidemargin)*7200/7227\relax\space
 width=\strip@pt\dimexpr\textwidth*7200/7227\relax\space
 sep=\strip@pt\dimexpr\columnsep*7200/7227\relax\space
 bottom=\strip@pt\dimexpr(1in+\voffset+\topmargin+\headheight+\headsep+\textheight)*7200/7227\relax\space
 bs=\strip@pt\dimexpr\baselineskip*7200/7227\relax}}
\makeatother
\begin{document}''')

if title:
    out.append(r'\twocolumn[\begin{center}\Large ZTITLEZ Title\end{center}]')
nblocks = R.choice([1, 1, 2, 2, 3, 4])
pid = fid = gid = wid = 0
for b in range(nblocks):
    if b == 0 and R.random() < 0.5:
        N = N0
        switch = False
    else:
        N = R.choice([1, 2, 2, 3, 3, 4]) if b > 0 else R.choice([1, 2, 3])
        switch = True
    blk = {'N': N, 'paras': [], 'fns': [], 'floats': [], 'dbl': []}
    brk = extra and b > 0 and R.random() < 0.25
    if brk:
        # ブロックの境目で改ページする（\evenendclearpage か \onecolumn→\twocolumn）
        if R.random() < 0.5:
            out.append(r'\evenendclearpage')
        else:
            out.append(r'\onecolumn\twocolumn')
            if not switch:
                N = N0  # \twocolumnは読み込み時の段数に戻る
    blk['break'] = brk
    if switch:
        star = '*' if (extra2 and b > 0 and R.random() < 0.2) else ''
        # 番号300000以上：段組ごとの段間と段間罫（別の乱数列で選び，文書の他の部分は変えない）
        sepopt = ''
        if seed >= 300000 and R2.random() < 0.4:
            sp, rl = R2.choice([0, 4, 9, 15, 30]), R2.choice([0, 0.4, 1.5])
            sepopt = '[columnsep=%gpt,columnseprule=%gpt]' % (sp, rl)
            blk['sep'] = sp * 72 / 72.27  # bp
        out.append(r'\evenendcolumns%s%s{%d}' % (star, sepopt, N))
    blk['N'] = N
    if R.random() < 0.6:
        out.append(r'\section{Block %d}' % (b + 1))
    npara = R.choice([0, 1, 2, 3, 5, 8, 12, 18])
    events = []
    for _ in range(R.choice([0, 0, 1, 1, 2])):
        events.append(('fn', R.randrange(max(npara, 1))))
    for _ in range(R.choice([0, 0, 1, 1, 2, 3])):
        events.append(('fl', R.randrange(max(npara, 1))))
    if N > 1 and R.random() < 0.15:
        events.append(('dbl', R.randrange(max(npara, 1))))
    for p in range(max(npara, 1)):
        if npara:
            pid += 1
            blk['paras'].append(pid)
            body = sentences(R.randint(1, 6))
            # 脚注の参照位置は段落の途中
            fnhere = [e for e in events if e[0] == 'fn' and e[1] == p]
            mid = ''
            for _ in fnhere:
                fid += 1
                blk['fns'].append(fid)
                fbody = sentences(R.choice([1, 1, 2, 4] + ([10, 20] if extra else [])))
                mid += r'ZR%dZ\footnote{ZN%dZ %s}' % (fid, fid, fbody)
            sep = '' if ja else ' '
            out.append(r'ZB%dZ%s%s%s%s%sZE%dZ\par' % (pid, sep, body, sep, mid, sep, pid))
        elif any(e[0] == 'fn' for e in events):
            for _ in [e for e in events if e[0] == 'fn']:
                fid += 1
                blk['fns'].append(fid)
                out.append(r'ZR%dZ\footnote{ZN%dZ %s}\par' % (fid, fid, sentences(1)))
        for e in [e for e in events if e[0] == 'fl' and e[1] == p]:
            gid += 1
            pos = R.choice(['t', 'b', 'h', 'tb', 'htb', 't'])
            if R.random() < 0.5:
                ht = R.choice([2, 3, 4, 6, 8])  # 行数
                size = r'%d\baselineskip' % ht
            else:
                size = '%.1fpt' % R.uniform(15, 140)
            blk['floats'].append({'id': gid, 'pos': pos})
            out.append(r'\begin{figure}[%s]\centering\fbox{\parbox[c][%s][c]{.9\columnwidth}{ZF%dLZ\hfill ZF%dRZ}}\caption{ZC%dZ}\end{figure}'
                       % (pos, size, gid, gid, gid))
        if extra2 and R.random() < 0.25:
            # tcolorbox（中身は小さい字．目印は付けない）
            kind = R.choice(['plain', 'breakable', 'float'])
            opt = {'plain': 'title=box', 'breakable': 'breakable,title=box', 'float': 'float=t,title=box'}[kind]
            out.append(r'\begin{tcolorbox}[%s]%s\end{tcolorbox}' % (opt, sentences(R.choice([1, 3, 8, 20]))))
        if extra2 and N > 1 and R.random() < 0.1:
            out.append(r'\columnbreak')
        for e in [e for e in events if e[0] == 'dbl' and e[1] == p]:
            wid += 1
            blk['dbl'].append(wid)
            out.append(r'\begin{figure*}[t]\centering\fbox{\parbox[c][%.1fpt][c]{.9\textwidth}{ZW%dLZ\hfill ZW%dRZ}}\caption{ZD%dZ}\end{figure*}'
                       % (R.uniform(20, 80), wid, wid, wid))
    meta['blocks'].append(blk)
out.append(r'\end{document}')
open(base + '.tex', 'w').write('\n'.join(out) + '\n')
json.dump(meta, open(base + '.json', 'w'))
