#!/bin/sh
# 並列で回す．使い方: many.sh 開始 終了 > 結果
cd "$(dirname "$0")"
seq "$1" "$2" | xargs -P 8 -n 1 ./one.sh
