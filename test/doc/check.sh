#!/bin/sh
# 文書（マニュアルなど）を段組で組んだときに見つかった不具合の再現（d*.tex）を調べる．
# fixed.shがd*.texを組んだ後に呼ぶ．ページ数，ブロックの高さ，行の重なり（overlap.py）を見る．
# 使い方: doc/check.sh
cd "$(dirname "$0")"
st=0
pages() { pdfinfo "$1.pdf" 2>/dev/null | awk '/^Pages/{print $2}'; }
want() {  # want 文書 ページ数
  p=$(pages "$1")
  if [ "$p" = "$2" ]; then echo "ok   $1: $p pages"; else echo "FAIL $1: $p pages (expected $2)"; st=1; fi
}
want d1-oneline 2
want d2-mcend 2
want d6-tallbox 2
# d8：1段のブロックの高さ（表の深さを行の標準の深さにしていない）
if grep -q 'columns balanced at 164.2pt (block)' d8-deepmid.log; then echo "ok   d8-deepmid: block 164.2pt"
else echo "FAIL d8-deepmid: $(grep 'columns balanced at' d8-deepmid.log | tr '\n' ' ')"; st=1; fi
for f in d*.tex; do
  b=${f%.tex}
  o=$(python3 overlap.py "$b.pdf" | tail -1)
  if [ "$o" = "overlaps 0" ]; then echo "ok   $b: $o"; else echo "FAIL $b: $o"; st=1; fi
done
exit $st
