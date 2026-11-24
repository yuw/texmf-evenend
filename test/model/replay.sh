#!/bin/sh
# 実装（evenend.lua）がdebugのログに書いた判断の記録（evenend: decision …;）を集め，Leanの
# モデルの関数（lean/Replay.lean）で同じ入力から結果を求めて，実装の結果と比べる．
#   select  候補を選ぶ（命題の手順3）
#   mis     揃わない配分の判定（手順4）
#   beta    下端の決め方（手順5）
# Lean 4の入った作業場所（既定は~/lean/mathlib-ws）が要る．「0 differ」なら合格．
# 使い方: test/model/replay.sh [ログのあるディレクトリ…]（既定はtest/rand/dとtest）
cd "$(dirname "$0")"
here=$(pwd); lean=$(cd ../../lean && pwd)
[ $# -eq 0 ] && set -- "$here/../rand/d" "$here/.."
ws=${LEAN_WS:-$HOME/lean/mathlib-ws}
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
if [ -n "$DECISIONS" ]; then cp "$DECISIONS" "$tmp/decisions.txt"  # 記録のファイルを直に渡す
else find "$@" -name '*.log' -print0 | xargs -0 python3 "$here/decisions.py" > "$tmp/decisions.txt"; fi
echo "記録 $(wc -l < "$tmp/decisions.txt" | tr -d ' ')件（select $(grep -c '^select' "$tmp/decisions.txt")，mis $(grep -c '^mis' "$tmp/decisions.txt")，beta $(grep -c '^beta' "$tmp/decisions.txt")）"
cd "$ws" || exit 1
for f in Select Misaligned Beta Replay; do
  LEAN_PATH="$tmp" lake env sh -c 'LEAN_PATH="$1:$LEAN_PATH" lean --root="$2" -o "$1/$3.olean" "$2/$3.lean"' sh "$tmp" "$lean" "$f" || exit 1
done
LEAN_PATH="$tmp" lake env sh -c 'LEAN_PATH="$1:$LEAN_PATH" lean --run "$2/grid/RunReplay.lean" < "$1/decisions.txt"' sh "$tmp" "$lean" | tee "$tmp/out.txt"
grep -q ' 0 differ, 0 unreadable$' "$tmp/out.txt"
