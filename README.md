# evenend

LaTeXの段組（`\twocolumn`）で，最終ページの各段の下端を揃えるLuaLaTeX用パッケージ．
flushendと同じ目的のものだが，次の点を扱う．

- 3段以上の段組（`columns=3`など）
- 段内フロート（最右段に載ったものも含む）と段抜きフロート（上端・stfloatsによる下端）
- 最終ページの脚注：参照位置が移った段へ脚注も移し，版面下端またはカラム下端に置く
- 段をまたいで分割された脚注の再結合

行数によっては最右段だけが短くなる（たとえば2段で31行なら16行と15行）．それ以外の段は
下端が揃う．

詳しくは`doc/lualatex/evenend/evenend-ja.pdf`（マニュアル）を参照．

## 動作要件

- LuaLaTeX（LaTeX 2023-06-01以降）
- LaTeX標準の段組（クラスオプション`twocolumn`または`\twocolumn`）．multicolの
  `multicols`環境は対象外．
- jlreq，LuaTeX-jaのクラスで動作を確認している（横組のみ）．

## インストール

`tex/lualatex/evenend/`の`evenend.sty`と`evenend.lua`をTEXMFツリーに置く．
このリポジトリ自体をTEXMFHOMEとして使うこともできる．

```bash
export TEXMFHOME=/path/to/texmf-evenend
```

## 使い方

```latex
\documentclass[twocolumn]{jlreq}
\usepackage[footnote=column]{evenend}
```

読み込むだけで，文書末（`\end{document}`）と`\onecolumn`の直前のページが揃う．

### オプション

| キー | 値 | 既定 | 意味 |
|---|---|---|---|
| `columns` | 整数 | `2` | 段数．3以上なら段幅も`(\textwidth-(N-1)\columnsep)/N`に設定する（読み込み時のみ） |
| `footnote` | `page`／`column` | `page` | 最終ページの脚注を版面下端に置くか，各段の本文の下（カラム下端）に置くか |
| `onecolumn` | 真偽 | `true` | `\onecolumn`の直前のページも揃える |
| `enable` | 真偽 | `true` | 文書末のページを揃える |
| `debug` | 真偽 | `false` | 段ごとの高さなどをログに書く |

`footnote=column`では，脚注を含めた各段の下端が揃う．`footnote=page`では，本文を揃えた
段の下を空け，脚注は版面の下端に置く．どちらの場合も脚注は参照位置のある段に入る．

`footnote`，`onecolumn`，`enable`，`debug`は文書中でも`\evenendsetup{...}`で変えられる．

### 命令

- `\evenend`，`\raggedend`：文書末のページを揃えるかどうかを切り替える
- `\evenendclearpage`：いまのページを揃えてから改ページする（章末などに）
- `\evenendsetup{キー=値}`：オプションの変更

## 仕組み

1. 各段を出力するとき（`\@makecol`の直前），段の生の材料（`\box255`），改段位置で捨て
   られるグルー類，脚注（`\box\footins`），段内フロートの複製をLua側にとっておく．
2. 脚注には番号を属性として付け，本文中の参照位置には同じ番号の印（`\vadjust`で
   行の直後に置くwhatsit）を置く．
3. 最終ページの最後の段が`\clearpage`の強制改段で出力されるとき，そのページの全段の
   材料を1本の垂直リストに繋ぎ直し，入り切る最小の段の高さを探して`\vsplit`で再分割する．
   脚注は参照位置の入った段に移し，その高さを段の容量から差し引く．
4. 段内フロートは元の段に残し，その高さも勘定に入れる．段抜きフロートは
   `\@combinedblfloats`がこれまでどおり配置する．
5. 各段の見かけの下端をそろえる．本文で終わる段は最終行の字面の下端（ベースライン＋深さ），
   下のフロートで終わる段はフロートの下端，段下端の脚注で終わる段は脚注の最終行の字面の
   下端を見る．最後の箱の中身が箱の下端からはみ出している場合（中身をグルーで下へずらした
   箱など）は，はみ出した位置を下端とみなす．
6. 本文だけの満杯の段があればその段を基準にし，フロートのある段はフロートまわりの
   グルーの伸び縮みで合わせる（行の位置を揃えるため）．

最終ページ以外の組版は，パッケージを読み込まない場合と変わらない．

## 制限事項

- 最終ページにフロートだけの段（フロート段）があるときは揃えない（警告を出す）．
- 最終ページ内の強制改段（`\newpage`など）は無視して詰め直す．
- 脚注は段をまたいで分割しない．
- 段内フロートは元の段に残る．参照位置との前後関係は保証しない．
- `\marginpar`の左右は再計算しない．
- 縦組は未対応．
- `\@outputdblcol`を再定義する他のパッケージ（flushend，balanceなど）とは併用できない．
  stfloatsは併用できる．

## マニュアル

`doc/lualatex/evenend/`にマニュアル（`evenend-ja.tex`）と見本（`evenend-sample.tex`，
`evenend-sample-column.tex`）がある．マニュアルは見本の最終ページを貼り込むので，
見本を先に組む．

```bash
cd doc/lualatex/evenend
lualatex evenend-sample.tex
lualatex evenend-sample-column.tex
lualatex evenend-ja.tex
lualatex evenend-ja.tex
```

## テスト

`test/`にテスト文書と補助スクリプトがある（poppler-utilsの`pdftotext`などを使う）．

```bash
test/run.sh test/t1-basic.tex
```

- `run.sh`：リポジトリをTEXMFHOMEにしてLuaLaTeXを走らせる
- `colbottoms.py`：最終ページの各段の最下行の位置を表示する
- `fuzz.sh`：本文の長さを1文ずつ変えて組み，エラーと段の下端を調べる

## バージョン表記

`v年月日.番号`と表す．年月日は変更した日（8桁），番号はその日のうちの変更回数
（0から数える）．たとえば`v20260925.0`は，2026年9月25日の最初の版．
現在のバージョンは`evenend.sty`の`\ProvidesPackage`に書いてある．

## ライセンス

MITライセンス（`LICENSE`を参照）．

Copyright (c) 2026 Yuwsuke Kieda
