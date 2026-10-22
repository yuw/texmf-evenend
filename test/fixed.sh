#!/bin/sh
# 固定のテスト文書（t*.tex，fb*.tex，tcb/，span/，split/，mc/，box/）を組み，ファイルごとに
# Overfull \vboxの数，エラーの数，blockcheck.pyの結果を出す．最後に合格の数をまとめ，
# mc/mk*.texの柱をmkcheck.pyで調べる．
# 合格は「of=0 err=0 blocks: N, problems: 0」（\showboxで止めるbox/m1.tex，m2.texは除く）
# 使い方: [JOBS=並列数] fixed.sh
cd "$(dirname "$0")"
export PATH=/usr/local/texlive/${TLYEAR:-2026}/bin/universal-darwin:$PATH
export TEXMFHOME="$(cd .. && pwd)"
export TEXINPUTS=${GYOUDORI:-/Users/yuw/tmp/texmf-gyoudori}/tex/latex/gyoudori//:
if [ "$1" = --one ]; then
  # 1件：fixed.sh --one ファイル
  d=$(dirname "$2"); b=$(basename "$2" .tex)
  (cd "$d" && timeout 300 lualatex -interaction=nonstopmode "$b" >/dev/null 2>&1)
  echo "$2 of=$(grep -a 'Overfull \\vbox' "$d/$b.log" | wc -l | tr -d ' ') err=$(grep -ac '^!' "$d/$b.log") $(./blockcheck.py "$d/$b.log" | tail -1)"
  exit
fi
# 文書は互いに独立なので並列に組む（同じディレクトリの文書が同じ名前のファイルを書くことはない）
ls t*.tex fb*.tex tcb/*.tex span/*.tex split/*.tex mc/*.tex box/b*.tex box/m3.tex \
  | xargs -P "${JOBS:-6}" -n 1 ./fixed.sh --one | sort > fixed.res
cat fixed.res
echo "fixed: $(grep -c 'of=0 err=0 blocks: [0-9]*, problems: 0$' fixed.res) / $(wc -l < fixed.res | tr -d ' ')"
# 柱（mk*.texは上で組んである）
for f in mc/mk*.tex; do
  echo "$f $(python3 mc/mkcheck.py "${f%.tex}.pdf" | tail -1)"
done
