#!/bin/sh
# 実装の純粋な計算（evenend.luaのM.pure：候補の列挙，候補を選ぶ規則，揃わない配分の判定，
# 下端の決め方，高さを探す手順）を，Leanのモデルの関数と，小さな範囲の入力のすべてで比べる．
# 期待値は，その場でLeanの関数（lean/grid/GridPure.lean）が書き出す．Lean 4の入った作業場所
# （既定は~/lean/mathlib-ws）が要る．「0 differ」が4つ並べば合格．使い方: test/model/pure.sh
cd "$(dirname "$0")"
export MODELDIR="$(pwd)"
lean=$(cd ../../lean && pwd)
ws=${LEAN_WS:-$HOME/lean/mathlib-ws}
export PATH=/usr/local/texlive/${TLYEAR:-2026}/bin/universal-darwin:$PATH
export TEXMFHOME="$(cd ../.. && pwd)"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
mkdir -p out
(cd "$ws" || exit 1
 for f in Enum Span Select Misaligned Beta MinH Replay; do
   LEAN_PATH="$tmp" lake env sh -c 'LEAN_PATH="$1:$LEAN_PATH" lean --root="$2" -o "$1/$3.olean" "$2/$3.lean"' sh "$tmp" "$lean" "$f" || exit 1
 done
 LEAN_PATH="$tmp" lake env sh -c 'LEAN_PATH="$1:$LEAN_PATH" lean --run "$2/grid/GridPure.lean"' sh "$tmp" "$lean" > "$tmp/GridPure.txt") || exit 1
export PUREFILE="$tmp/GridPure.txt"
cd out && lualatex -interaction=nonstopmode ../pure.tex >/dev/null 2>&1
grep -a '^RESULT pure\|^DIFF' pure.log
[ "$(grep -ac '^RESULT pure .* 0 differ$' pure.log)" = 4 ]
