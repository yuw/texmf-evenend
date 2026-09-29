#!/usr/bin/env python3
"""many.shの結果をまとめる．使い方: summary.py 結果ファイル"""
import re, sys
from collections import Counter
ok = ng = 0; cats = Counter(); ex = {}; lim = Counter(); cov = Counter(); tags = Counter()
for line in open(sys.argv[1]):
    parts = line.rstrip('\n').split(' | ')
    head = parts[0].split()
    if len(head) < 2: continue
    seed, st = head[0], head[1]
    if st == 'OK': ok += 1
    else: ng += 1
    probs = parts[1].split() if len(parts) > 1 else []
    if st == 'NG' and len(head) == 3: probs = [head[2]]
    for p in probs:
        c = re.sub(r'\d+(\.\d+)?', '#', p.split(':')[0])
        cats[c] += 1; ex.setdefault(c, seed)
    if len(parts) > 2:
        for c in parts[2].split(): cov[c] += 1
    if len(parts) > 3:
        for c in parts[3].split(): lim[c] += 1
print(f'OK {ok}  NG {ng}')
for c, n in cats.most_common(): print(f'  {n:4d} {c}  (e.g. seed {ex[c]})')
print('coverage:', dict(cov)); print('limits:', dict(lim))
