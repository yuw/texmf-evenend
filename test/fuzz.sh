#!/bin/sh
# 本文の長さを1文ずつ変えて組み，エラーの有無と最終ページの段の下端を調べる
# 使い方: fuzz.sh 開始 終了 [パッケージオプション] [段数]
cd "$(dirname "$0")"
mkdir -p fuzz
opt=${3:-}
N=${4:-2}
for n in $(seq "$1" "${STEP:-1}" "$2"); do
  f=fuzz/f$n.tex
  cat > $f <<EOT
\documentclass[twocolumn]{article}
\usepackage[$opt]{evenend}
\usepackage{lipsum}
\begin{document}
\section{A}
\lipsum[1-7]
Foot\footnote{A footnote that is long enough to take two lines in a column of text.}
\lipsum[8-22][1-$n]
\end{document}
EOT
  (cd fuzz && ../run.sh f$n.tex)
  err=$(grep -ac "^!" fuzz/f$n.log)
  warn=$(grep -a "evenend Warning" fuzz/f$n.log | head -1)
  pages=$(pdfinfo fuzz/f$n.pdf 2>/dev/null | awk '/Pages/{print $2}')
  echo "n=$n err=$err pages=$pages $warn | $(./colbottoms.py fuzz/f$n.pdf $N | awk '{printf "%s %s %s; ", $1$2, $3, $4}')"
done
