#!/usr/bin/env python3
"""ログから判断の記録（evenend: decision …;）を取り出す．使い方: decisions.py ログ…
ログは79桁で折り返されるので，改行を除いてから探す．"""
import re, sys
for f in sys.argv[1:]:
    try:
        log = open(f, encoding='utf-8', errors='replace').read()
    except OSError:
        continue
    if 'evenend: decision' not in log:
        continue
    for m in re.finditer(r'evenend: decision ([^;]*);', log.replace('\n', '')):
        print(m.group(1))
