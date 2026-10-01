#!/bin/sh
# テスト用：このリポジトリをTEXMFHOMEとして使ってLuaLaTeXを走らせる
export PATH=/usr/local/texlive/${TLYEAR:-2026}/bin/universal-darwin:$PATH
export TEXMFHOME="$(cd "$(dirname "$0")/.." && pwd)"
for f in "$@"; do
  lualatex -interaction=nonstopmode "$f" >/dev/null
done
