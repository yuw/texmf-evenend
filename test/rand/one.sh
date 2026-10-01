#!/bin/sh
# 1件：文書を作って組み，調べる．使い方: one.sh seed
cd "$(dirname "$0")"
s=$1; b=d/r$s
mkdir -p d
python3 gen.py $s $b
export PATH=/usr/local/texlive/${TLYEAR:-2026}/bin/universal-darwin:$PATH
export TEXMFHOME="$(cd ../.. && pwd)"
export TEXINPUTS=/Users/yuw/tmp/texmf-gyoudori/tex/latex/gyoudori//:
(cd d && timeout 180 lualatex -interaction=nonstopmode r$s.tex >/dev/null 2>&1)
if [ ! -f $b.pdf ]; then
  if grep -aqi "no pages of output" $b.log && python3 -c "import json,sys;m=json.load(open('$b.json'));sys.exit(any(b['paras'] or b['fns'] or b['floats'] or b['dbl'] for b in m['blocks']))"; then echo "$s OK empty-document"; else echo "$s NG no-pdf"; fi; exit
fi
echo "$s $(python3 check.py $b)"
