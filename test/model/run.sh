#!/bin/sh
# モデルの仮定を，TeXの原始機能そのもので確かめる（evenendの揃えは通さない）．
#   glue    高さを指定して組む箱のグルーの割り振り（lean/Glue.lean）
#   lines   行を積んだときの最終行のベースライン（lean/Layout.lean）
#   vsplit  \vsplitの性質（lean/Fill.leanのSpec）．欧文のクラスとLuaTeX-jaのクラス
# glueとlinesの期待値は，Leanの関数が書き出したもの（lean/expect．lean/check.shが作り直す）．
# 「0 differ」「violations=0」が並べば合格．使い方: test/model/run.sh
cd "$(dirname "$0")"
export MODELDIR="$(pwd)"
export EXPECT="$(cd ../../lean/expect && pwd)"
export PATH=/usr/local/texlive/${TLYEAR:-2026}/bin/universal-darwin:$PATH
export TEXMFHOME="$(cd ../.. && pwd)"
mkdir -p out && cd out
st=0
for f in glue lines; do
  luatex -interaction=nonstopmode ../$f.tex >/dev/null 2>&1
  r=$(grep -a '^RESULT' $f.log | sed 's/)$//'); echo "${r:-$f: 結果なし}"
  grep -a '^DIFF' $f.log
  echo "$r" | grep -q ' 0 differ$' || st=1
done
for f in vsplit vsplit-ja; do
  lualatex -interaction=nonstopmode ../$f.tex >/dev/null 2>&1
  r=$(grep -a 'evenend: model checks' $f.log); echo "$f: ${r:-結果なし}"
  grep -a -A1 'model violation' $f.log | head -20
  echo "$r" | grep -q 'vsplit=[1-9][0-9]* .*violations=0$' || st=1
done
exit $st
