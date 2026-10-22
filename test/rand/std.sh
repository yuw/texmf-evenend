#!/bin/sh
# 乱数試験の標準の組を流す．使い方: [QUICK=1] [JOBS=並列数] std.sh 結果ファイル
# 標準の組（3400件）：1〜1000（基本の要素）と，100001〜，200001〜，300001〜，400001〜の
# 各600件（gen.pyは，seedが100000以上で\evenendclearpageやhyperrefなど，200000以上で
# tcolorbox，\columnbreak，\evenendcolumns*，300000以上でheadingskip=blockや段組ごとの段間，
# 箱の中の段組，400000以上で段をまたぐフロートを加える）．
# 1〜3400のように続けて流すと，追加の要素がまったく試されないので注意．
# QUICK=1なら各範囲の先頭1割（340件．直している途中の確かめ用）．
# 前に落ちたseed（failed.txt）を先に流し，後退があれば早く気づけるようにする．
# 落ちたseedはfailed.txtに加える（直った後も，以後の試験で先に流す）．
out=${1:?結果ファイルを指定する}
# 結果ファイルは呼んだ場所から見たパスなので，移る前に絶対パスにする
mkdir -p "$(dirname "$out")"
out="$(cd "$(dirname "$out")" && pwd)/$(basename "$out")"
cd "$(dirname "$0")"
if [ -n "$QUICK" ]; then a=100; b=60; else a=1000; b=600; fi
list=$(mktemp)
{
  [ -f failed.txt ] && cat failed.txt
  seq 1 $a
  for r in 100000 200000 300000 400000; do seq $((r+1)) $((r+b)); done
} | awk '!seen[$1]++' > "$list"
total=$(wc -l < "$list" | tr -d ' ')
: > "$out"
# 進み具合を1分ごとに標準エラーに出す
( while sleep 60; do ./progress.sh "$out" "$total" >&2; done ) &
mon=$!
xargs -P "${JOBS:-6}" -n 1 ./one.sh < "$list" >> "$out"
kill $mon 2>/dev/null
rm -f "$list"
./progress.sh "$out" "$total"
# 落ちたseedを覚える
grep ' NG' "$out" | awk '{print $1}' >> failed.txt
sort -n -u -o failed.txt failed.txt
grep ' NG' "$out"
