#!/usr/bin/env python3
"""footnote=pageで段数を切り換えた文書（fuzzswitch.sh）の脚注の位置を調べる．
・途中のブロックの脚注（「2段の脚注」）：そのブロックの段の下（同じページで，その下に
  次のブロックの見出し「3段」がある）か，LaTeXが組んだ満杯のページなら版面の下端
・最後の段組の脚注（「最後の脚注」）：版面の下端
版面の下端はログのTEXTBOTTOM（紙面の上端から，bp）．脚注の最終行の下端がそこから
±4bpにあれば版面の下端とみなす．使い方: pagefncheck.py file.pdf file.log"""
import re, subprocess, sys
pdf, log = sys.argv[1], sys.argv[2]
tb = float(re.search(r'TEXTBOTTOM ([\d.]+)', open(log, errors='replace').read()).group(1))
pages = int(re.search(r'Pages:\s+(\d+)', subprocess.run(['pdfinfo', pdf], capture_output=True, text=True).stdout).group(1))
res = {}
for pg in range(1, pages + 1):
    out = subprocess.run(['pdftotext', '-bbox', '-f', str(pg), '-l', str(pg), pdf, '-'], capture_output=True, text=True).stdout
    W = [(float(a), float(b), float(c), float(d), t) for a, b, c, d, t in
         re.findall(r'<word xMin="([\d.]+)" yMin="([\d.]+)" xMax="([\d.]+)" yMax="([\d.]+)">([^<]*)</word>', out)]
    # 見出し「3段」（語が「3」と「段」に分かれる）
    H = [W[i] for i in range(len(W) - 1)
         if W[i][4] == '3' and W[i + 1][4] == '段' and abs(W[i][1] - W[i + 1][1]) < 2]
    for key, pat in (('2段の脚注', '段の脚注'), ('最後の脚注', '最後の脚注')):
        for w in W:
            if pat in w[4]:
                heads = [v for v in H if v[1] > w[3]]
                res[key] = (pg, w, heads)
problems = []
if '最後の脚注' in res:
    pg, w, _ = res['最後の脚注']
    if abs(w[3] - tb) > 4:
        problems.append(f'final footnote not at text bottom: p{pg} {w[3]:.1f} vs {tb:.1f}')
else:
    problems.append('final footnote not found')
if '2段の脚注' in res:
    pg, w, heads = res['2段の脚注']
    if not heads and abs(w[3] - tb) > 4:
        problems.append(f'block footnote neither above the next block nor at text bottom: p{pg} {w[3]:.1f}')
    where = 'block' if heads else 'page-bottom'
else:
    problems.append('block footnote not found'); where = '-'
print(f'problems: {len(problems)} (block footnote at {where}) ' + '; '.join(problems))
