#!/usr/bin/env python3
"""最終ページ（または指定ページ）の各段について，最下行の下端（yMax）を表示する．
使い方: colbottoms.py file.pdf N [page]"""
import re, subprocess, sys
pdf, N = sys.argv[1], int(sys.argv[2])
pages = int(re.search(r'Pages:\s+(\d+)', subprocess.run(['pdfinfo', pdf], capture_output=True, text=True).stdout).group(1))
args = [a for a in sys.argv[1:] if not a.startswith('--')]
page = int(args[2]) if len(args) > 2 else pages
out = subprocess.run(['pdftotext', '-bbox', '-f', str(page), '-l', str(page), pdf, '-'],
                     capture_output=True, text=True).stdout
pw = float(re.search(r'<page width="([\d.]+)"', out).group(1))
words = [tuple(map(float, m.groups()[:4])) + (m.group(5),) for m in
         re.finditer(r'<word xMin="([\d.]+)" yMin="([\d.]+)" xMax="([\d.]+)" yMax="([\d.]+)">([^<]*)</word>', out)]
# ページ番号（最下部の数字だけの語）を除く
bot = max(w[3] for w in words)
words = [w for w in words if not (w[4].isdigit() and w[3] > bot - 1)]
# 本文の字の大きさの語だけを見る（脚注や図の見出しを除く）
from collections import Counter
hs = Counter(round(w[3] - w[1], 1) for w in words)
body = hs.most_common(1)[0][0]
if '--all' not in sys.argv:
    words = [w for w in words if round(w[3] - w[1], 1) >= body - 0.2]
xs = sorted(w[0] for w in words)
lo, hi = xs[0], max(w[2] for w in words)
width = (hi - lo) / N
cols = [[] for _ in range(N)]
for w in words:
    i = min(N - 1, int((w[0] - lo) / width))
    cols[i].append(w)
for i, c in enumerate(cols):
    if not c:
        print(f'col {i+1}: empty'); continue
    # 最下部の行（ページ番号などを除くため，本文域の語だけを見る想定）
    ys = sorted(set(round(w[3], 1) for w in c))
    print(f'col {i+1}: lines={len(ys)} bottom={ys[-1]} (last: {" ".join(w[4] for w in c if round(w[3],1)==ys[-1])[:40]})')
