#!/bin/sh
# Leanの証明をまとめて確かめる．Lean 4とMathlibの入った作業場所（既定は~/lean/mathlib-ws）で動かす．
# 「ok」が並べば，すべての証明が通っている．
# Balance.leanはMinH.leanとSelect.leanを読み込むので，一時的な場所に.oleanを作って読ませる．
dir=$(cd "$(dirname "$0")" && pwd)
ws=${LEAN_WS:-$HOME/lean/mathlib-ws}
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
cd "$ws" || exit 1
st=0
for f in Example MinH Select Fill Enum Span Misaligned Beta Bottom Layout Glue Column Page Balance Whole Link Replay; do
  out=$(LEAN_PATH="$tmp" lake env sh -c 'LEAN_PATH="$1:$LEAN_PATH" lean --root="$2" -o "$1/$3.olean" "$2/$3.lean"' sh "$tmp" "$dir" "$f" 2>&1)
  if [ -z "$out" ]; then echo "ok   $f.lean"; else echo "FAIL $f.lean"; echo "$out"; st=1; fi
done
# 格子状の入力についてのモデルの期待値（TeXの実測とtest/model/run.shで比べる）
mkdir -p "$dir/expect"
for g in GridGlue GridLines; do
  if LEAN_PATH="$tmp" lake env sh -c 'LEAN_PATH="$1:$LEAN_PATH" lean --run "$2/grid/$3.lean"' sh "$tmp" "$dir" "$g" > "$tmp/$g.txt" 2> "$tmp/$g.err" && [ -s "$tmp/$g.txt" ]; then
    cp "$tmp/$g.txt" "$dir/expect/$g.txt"; echo "ok   grid/$g.lean（$(wc -l < "$dir/expect/$g.txt" | tr -d ' ')件）"
  else echo "FAIL grid/$g.lean"; cat "$tmp/$g.err"; st=1; fi
done
if grep -n 'sorry\|admit\|native_decide\|^axiom' "$dir"/*.lean; then echo "FAIL 証明の抜け"; st=1; fi
exit $st
