#!/bin/sh
# 同じ段にフロートと脚注が入る文書を，フロートの位置（t/b），脚注の置き場所（page/column），
# 場面（final：最終ページ，block：段数の切り換え前のブロック，after：切り換えた後の
# 最後の段組），本文の分量を変えて組み，配置を調べる（MODESで場面を選べる）
# 使い方: [MODES=場面] [JOBS=並列数] fnfloat.sh
cd "$(dirname "$0")"
if [ "$1" = --one ]; then
  # 1件：fnfloat.sh --one 位置 脚注の置き場所 場面 前の段落数 後の段落数
  pos=$2; fnm=$3; mode=$4; a=$5; c=$6
  f=fuzz/ff-$pos-$fnm-$mode-$a-$c
  python3 - "$pos" "$fnm" "$mode" "$a" "$c" > $f.tex <<'PY'
import sys
pos, fnm, mode, a, c = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]), int(sys.argv[5])
P = r"吾輩は猫である．名前はまだ無い．どこで生れたかとんと見当がつかぬ．何でも薄暗いじめじめした所でニャーニャー泣いていた事だけは記憶している．\par "
fig = r"\begin{figure}[%s]\centering\fbox{\parbox[c][3\baselineskip][c]{.6\columnwidth}{\centering FIGMARK}}\caption{図}\end{figure}" % pos
print(r"\documentclass[twocolumn,fontsize=10pt]{jlreq}\usepackage[debug,footnote=%s]{evenend}" % fnm)
print(r"\begin{document}\makeatletter\typeout{TEXTBOTTOM \strip@pt\dimexpr(1in+\topmargin+\headheight+\headsep+\textheight)*7200/7227\relax}\makeatother")
if mode == 'block':
    print(r"\section{前}" + P * 12)
if mode == 'after':
    print(r"\evenendcolumns{1}\section{前}" + P * 2 + r"\evenendcolumns{2}TWOCOL ")
print(P * a + r"脚注FNREF\footnote{FNTEXT 脚注の本文．脚注の本文．脚注の本文．脚注の本文．}．" + fig + P * (c + 1))
if mode == 'block':
    print(r"\evenendcolumns{1}ONECOL " + P)
print(r"\end{document}")
PY
  (cd fuzz && ../run.sh $(basename $f).tex)
  err=$(grep -ac "^!" $f.log); of=$(grep -ac "Overfull \\\\vbox" $f.log)
  echo "$pos $fnm $mode $a $c err=$err overfull=$of $(./blockcheck.py $f.log | tail -1) | $(./fnfloatcheck.py $f.pdf 2 $fnm $f.log | tail -1) $(grep -a 'evenend W' $f.log | head -1)"
  exit
fi
mkdir -p fuzz
# 組ごとの文書は互いに独立なので並列に組み，組の順に並べて出す
for pos in t b; do for fnm in page column; do for mode in ${MODES:-final block after}; do for a in 0 1 2 3 5 7; do for c in 0 1 3; do
  echo "$pos $fnm $mode $a $c"
done; done; done; done; done | xargs -P "${JOBS:-6}" -L 1 ./fnfloat.sh --one | sort -k1,1 -k2,2 -k3,3 -k4,4n -k5,5n
