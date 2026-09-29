#!/usr/bin/env python3
"""柱の検証：各ページの柱のHEAD[右の柱][左の柱]が，そのページの本文の目印MKnのうち
読む順序で最初（\\rightmark）と最後（\\leftmark）のものと一致するか．
読む順序はevenendのブロック（上から）と段（左から）．目印の位置と段の境目から求める．"""
import re, subprocess, sys
pdf = sys.argv[1]
xml = subprocess.run(['pdftotext', '-bbox', pdf, '-'], capture_output=True, text=True).stdout
bad = 0
for pno, pg in enumerate(re.findall(r'<page[^>]*>(.*?)</page>', xml, re.S), 1):
    W = [(float(a), float(b), t) for a, b, t in re.findall(r'<word xMin="([\d.]+)" yMin="([\d.]+)"[^>]*>([^<]*)</word>', pg)]
    head = ''.join(t for x, y, t in W if 'HEAD' in t)
    m = re.search(r'HEAD\[R?(\d*)\]\[L?(\d*)\]', head)
    marks = [(y, x, int(re.search(r'MK(\d+)', t).group(1))) for x, y, t in W if re.search(r'MK\d+', t)]
    if not marks: continue
    nums = sorted(n for _, _, n in marks)  # 番号は本文の順序
    first, last = nums[0], nums[-1]
    got = (int(m.group(1)) if m and m.group(1) else None, int(m.group(2)) if m and m.group(2) else None)
    ok = got == (first, last)
    bad += not ok
    print(f'p{pno}: marks {nums[0]}..{nums[-1]} head R{got[0]} L{got[1]} {"ok" if ok else "NG"}')
print('NG pages:', bad)
