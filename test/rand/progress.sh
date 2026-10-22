#!/bin/sh
# 乱数試験の進み具合：済み・残り・不合格の件数．使い方: progress.sh 結果ファイル [総数]
# 総数を省くと標準の組（3400件）とみなす
out=$1; total=${2:-3400}
n=$(grep -cE '^[0-9]+ (OK|NG)' "$out")
ng=$(grep -cE '^[0-9]+ NG' "$out")
echo "済み $n／$total，残り $((total-n))，不合格 $ng"
