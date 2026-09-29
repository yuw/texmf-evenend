#!/usr/bin/env python3
"""各ページの本文の行（本文の字の大きさの語）の下端が行送りの格子に乗っているかを調べる．
使い方: gridcheck.py file.pdf 行送り(pt)"""
import re, subprocess, sys
from collections import Counter
pdf, bs = sys.argv[1], float(sys.argv[2])
pages = int(re.search(r'Pages:\s+(\d+)', subprocess.run(['pdfinfo', pdf], capture_output=True, text=True).stdout).group(1))
bad = 0
for pg in range(1, pages + 1):
    out = subprocess.run(['pdftotext', '-bbox', '-f', str(pg), '-l', str(pg), pdf, '-'], capture_output=True, text=True).stdout
    ws = [tuple(map(float, m.groups())) for m in re.finditer(r'<word xMin="([\d.]+)" yMin="([\d.]+)" xMax="([\d.]+)" yMax="([\d.]+)">', out)]
    hs = Counter(round(w[3] - w[1], 2) for w in ws)
    body = hs.most_common(1)[0][0]
    ys = sorted(set(round(w[3], 2) for w in ws if abs((w[3] - w[1]) - body) < 0.05))
    if not ys: continue
    y0 = ys[0]
    off = [y for y in ys if min((y - y0) % bs, bs - (y - y0) % bs) > 0.05]
    bad += len(off)
    print(f'p{pg}: {len(ys)} line positions, off-grid: {len(off)} {off[:5]}')
print('total off-grid:', bad)
