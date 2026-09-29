#!/bin/sh
# 段数の切り換えを含む文書を，ブロックごとの段落数を変えて組み，エラー，Overfull，
# 行送りの位置（jlreq），ブロックごとの下端の揃いを調べる
# 使い方: [FIG=0] fuzzswitch.sh [パッケージオプション]（FIG=0なら図を入れない）
cd "$(dirname "$0")"
mkdir -p fuzz
opt=${1:-}
bs=$(python3 -c "print(17*72/72.27)")
for a in 2 5 9; do for b in 1 4 8; do for c in 1 3; do for d in 3 12 25; do
  f=fuzz/s-$a-$b-$c-$d
  python3 - "$a" "$b" "$c" "$d" "$opt" > $f.tex <<'PY'
import os, sys
a, b, c, d = map(int, sys.argv[1:5]); opt = sys.argv[5]
P = r"吾輩は猫である．名前はまだ無い．どこで生れたかとんと見当がつかぬ．何でも薄暗いじめじめした所でニャーニャー泣いていた事だけは記憶している．\par "
fig = r"\begin{figure}[t]\centering\fbox{\parbox[c][2\baselineskip][c]{.6\columnwidth}{\centering 図}}\caption{図}\end{figure}"
print(r"\documentclass[twocolumn,fontsize=10pt]{jlreq}\usepackage[debug,%s]{evenend}" % opt)
print(r"\begin{document}\makeatletter\typeout{TEXTBOTTOM \strip@pt\dimexpr(1in+\topmargin+\headheight+\headsep+\textheight)*7200/7227\relax}\makeatother\section{2段}")
print(P * a + r"脚注\footnote{2段の脚注．}．" + P)
print(r"\evenendcolumns{3}\section{3段}" + P * b + (fig if os.environ.get("FIG", "1") == "1" else "") + P)
print(r"\evenendcolumns{1}" + P * c)
print(r"\evenendcolumns{2}\section{2段}" + P * d + r"脚注\footnote{最後の脚注．}．" + P)
print(r"\end{document}")
PY
  (cd fuzz && ../run.sh $(basename $f).tex)
  err=$(grep -ac "^!" $f.log); of=$(grep -ac "Overfull \\\\vbox" $f.log)
  grid=$(./gridcheck.py $f.pdf $bs | tail -1 | awk '{print $3}')
  blk=$(./blockcheck.py $f.log | tail -1)
  warn=$(grep -a "evenend W" $f.log | head -1)
  echo "$a-$b-$c-$d err=$err overfull=$of offgrid=$grid $blk $warn"
done; done; done; done
