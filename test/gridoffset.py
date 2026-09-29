#!/usr/bin/env python3
"""本文の行が行送りの格子からどれだけずれているかを測る．
格子はページごとに，本文の字の大きさの行のうち一番上の行を基準にとる．
使い方: gridoffset.py 行送り(bp) file.pdf ...
出力: 行の位置の総数，格子から外れた数（0.05bp超），ずれの最大と平均（外れたものの）"""
import re, subprocess, sys
from collections import Counter
bs = float(sys.argv[1])
tot = off = 0; offs = []
for pdf in sys.argv[2:]:
    pages = int(re.search(r'Pages:\s+(\d+)', subprocess.run(['pdfinfo', pdf], capture_output=True, text=True).stdout).group(1))
    for pg in range(1, pages + 1):
        out = subprocess.run(['pdftotext', '-bbox', '-f', str(pg), '-l', str(pg), pdf, '-'], capture_output=True, text=True).stdout
        ws = [tuple(map(float, m.groups())) for m in re.finditer(r'<word xMin="([\d.]+)" yMin="([\d.]+)" xMax="([\d.]+)" yMax="([\d.]+)">', out)]
        if not ws: continue
        body = Counter(round(w[3] - w[1], 2) for w in ws).most_common(1)[0][0]
        ys = sorted(set(round(w[3], 2) for w in ws if abs((w[3] - w[1]) - body) < 0.05))
        y0 = ys[0]
        for y in ys:
            r = (y - y0) % bs
            d = min(r, bs - r)
            tot += 1
            if d > 0.05:
                off += 1; offs.append(d)
mx = max(offs) if offs else 0
mean = sum(offs) / len(offs) if offs else 0
print(f'lines: {tot}, off-grid: {off}, max: {mx:.2f}bp, mean: {mean:.2f}bp')
