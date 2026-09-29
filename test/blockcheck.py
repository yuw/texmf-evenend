#!/usr/bin/env python3
"""debugオプションのログから，揃えた段組（ブロック・最終ページ）ごとに，最右段以外の
段が実際に置かれた見かけの下端が揃った高さに達しているかを調べる．使い方: blockcheck.py file.log"""
import re, sys
log = open(sys.argv[1], encoding='utf-8', errors='replace').read().replace('\n', '')
bad = 0; n = 0
for m in re.finditer(r'evenend: balanced at ([\d.]+)pt(.*?)(?=evenend: balanced at|$)', log):
    h = float(m.group(1)); n += 1
    # 版面下端の脚注に押された段（pushed），フロートだけの段（floats only），次の段の
    # 材料に阻まれた段（blocked）は対象外
    cols = [None if p else float(a) for a, p in re.findall(r'column \d+ placed ([\d.]+)pt( \((?:pushed|floats only|blocked|column break)\))?', m.group(2))]
    for i, v in enumerate(cols[:-1]):
        if v is not None and v > 0 and abs(v - h) > 0.5:  # 空の段は対象外
            bad += 1; print(f'block {n}: column {i+1} bottom {v:.2f} != {h:.2f}')
    if cols and cols[-1] is not None and cols[-1] > h + 0.01:
        bad += 1; print(f'block {n}: last column {cols[-1]:.2f} > {h:.2f}')
print(f'blocks: {n}, problems: {bad}')
