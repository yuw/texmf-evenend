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
for f in Example MinH Select Fill Enum Misaligned Beta Bottom Glue Page Balance; do
  out=$(LEAN_PATH="$tmp" lake env sh -c 'LEAN_PATH="$1:$LEAN_PATH" lean --root="$2" -o "$1/$3.olean" "$2/$3.lean"' sh "$tmp" "$dir" "$f" 2>&1)
  if [ -z "$out" ]; then echo "ok   $f.lean"; else echo "FAIL $f.lean"; echo "$out"; st=1; fi
done
if grep -n 'sorry\|admit\|native_decide\|^axiom' "$dir"/*.lean; then echo "FAIL 証明の抜け"; st=1; fi
exit $st
