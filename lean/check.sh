#!/bin/sh
# Leanの証明をまとめて確かめる．Lean 4とMathlibの入った作業場所（既定は~/lean/mathlib-ws）で動かす．
# 何も出ずに「ok」が並べば，すべての証明が通っている．
dir=$(cd "$(dirname "$0")" && pwd)
ws=${LEAN_WS:-$HOME/lean/mathlib-ws}
cd "$ws" || exit 1
st=0
for f in Example MinH Fill Enum Select Beta Glue Page; do
  out=$(lake env lean "$dir/$f.lean" 2>&1)
  if [ -z "$out" ]; then echo "ok   $f.lean"; else echo "FAIL $f.lean"; echo "$out"; st=1; fi
done
if grep -n 'sorry\|admit\|native_decide\|^axiom' "$dir"/*.lean; then echo "FAIL 証明の抜け"; st=1; fi
exit $st
