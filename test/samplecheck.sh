#!/bin/sh
# マニュアルの見本（doc/lualatex/evenend/evenend-sample*.tex）を今の版で組み，コミット済みの
# PDF（HEAD）と語の位置を比べる．見本を変えていないのに差が出たら，組版が変わっている
# （乱数試験にない組み合わせ（文書の途中でのオプションの切り換えなど）の後退に気づける）．
# 作業用の場所で組むので，リポジトリのPDFは書き換えない．使い方: samplecheck.sh
cd "$(dirname "$0")/.."
export PATH=/usr/local/texlive/${TLYEAR:-2026}/bin/universal-darwin:$PATH
export TEXMFHOME="$(pwd)"
w=$(mktemp -d)
cp doc/lualatex/evenend/evenend-sample*.tex "$w/"
ng=0
for f in doc/lualatex/evenend/evenend-sample*.tex; do
  b=$(basename "$f" .tex)
  (cd "$w" && lualatex -interaction=nonstopmode "$b" >/dev/null 2>&1 && lualatex -interaction=nonstopmode "$b" >/dev/null 2>&1)
  if ! git cat-file -e "HEAD:doc/lualatex/evenend/$b.pdf" 2>/dev/null; then echo "$b 新しい見本（比べる相手がない）"; continue; fi
  git show "HEAD:doc/lualatex/evenend/$b.pdf" > "$w/old.pdf"
  pdftotext -bbox "$w/old.pdf" - | grep '<word' > "$w/o.txt"
  pdftotext -bbox "$w/$b.pdf" - | grep '<word' > "$w/n.txt"
  if cmp -s "$w/o.txt" "$w/n.txt"; then echo "$b 一致"; else echo "$b 差あり"; ng=$((ng+1)); fi
done
rm -rf "$w"
echo "samples: 差あり $ng"
