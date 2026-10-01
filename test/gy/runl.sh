#!/bin/bash
# gyoudori（行ドリ）と組み合わせた文書を1つ作って組み，行の位置を調べる．
# 使い方: runl.sh クラス 段数(1|2) ジョブ名 [gyoudoriのオプションなど]
# gyoudoriの置き場所は環境変数GYOUDORI（既定は/Users/yuw/tmp/texmf-gyoudori）
cd "$(dirname "$0")"
export PATH=/usr/local/texlive/${TLYEAR:-2026}/bin/universal-darwin:$PATH
export TEXMFHOME="$(cd ../.. && pwd)"
export TEXINPUTS=${GYOUDORI:-/Users/yuw/tmp/texmf-gyoudori}/tex/latex/gyoudori//:
cls=$1; col=$2; job=$3; opts=${4:-float}
mkdir -p out
python3 genf.py $cls "$opts" $col out/$job.tex
sed -i '' 's/\\begin{document}/\\begin{document}\\makeatletter\\@gyoudori@metrics\\typeout{MET \\strip@pt\\@gyoudori@bs\\space\\strip@pt\\@gyoudori@ht\\space\\strip@pt\\@gyoudori@dp}\\makeatother/' out/$job.tex
(cd out && timeout 600 lualatex -interaction=nonstopmode $job.tex >/dev/null 2>&1)
echo "=== $cls col=$col opts=$opts"
grep -E '^!' out/$job.log | sort | uniq -c
read bs ht dp < <(grep '^MET' out/$job.log | cut -d' ' -f2-)
echo "bs=$bs ht=$ht dp=$dp pages=$(grep -o '\[[0-9]*' out/$job.log | tail -1)"
grep -h '^POS' out/$job.log | awk -v bs=$bs -v ht=$ht -v dp=$dp -f chk.awk | grep -v '(as t'
echo "overfull vbox: $(grep -c 'Overfull \\vbox' out/$job.log)"
