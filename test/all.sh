#!/bin/sh
# 回帰試験の全部：乱数試験の標準の組（rand/std.sh），固定のテスト一式（suite.sh），
# 固定のテスト文書（fixed.sh），モデルとの照らし合わせ（model/）を順に流す（それぞれの中で並列に組む）．
# 結果は引数のディレクトリ（既定はtest/results）に書く．
# 使い方: [QUICK=1] [JOBS=並列数] all.sh [結果のディレクトリ]
cd "$(dirname "$0")"
r=${1:-results}
mkdir -p "$r"
start=$(date +%s)
echo "== rand（$( [ -n "$QUICK" ] && echo 340件 || echo 3400件 )）"
rand/std.sh "$r/rand.txt" 2> "$r/rand.progress" | tail -n +1
echo "== suite"
./suite.sh > "$r/suite.txt" 2>&1; cat "$r/suite.txt"
echo "== fixed"
./fixed.sh > "$r/fixed.txt" 2>&1; grep -v 'of=0 err=0 blocks: [0-9]*, problems: 0$' "$r/fixed.txt"
# モデル（lean/）と実装・TeXの照らし合わせ：原始機能の格子の試験と，上で組んだログの
# 判断の記録の再生（Leanの作業場所があるときだけ）
echo "== model"
model/run.sh > "$r/model.txt" 2>&1; cat "$r/model.txt"
if [ -d "${LEAN_WS:-$HOME/lean/mathlib-ws}" ]; then
  model/replay.sh > "$r/replay.txt" 2>&1; cat "$r/replay.txt"
else echo "replay: Leanの作業場所がないので省いた"; fi
echo "所要 $(( ($(date +%s) - start) / 60 ))分"
