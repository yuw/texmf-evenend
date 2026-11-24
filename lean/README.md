# Leanによる確認

`doc/lualatex/evenend/evenend-theory-ja.pdf`（evenendパッケージの定式化）の例，補題，命題の一部を，
Lean 4で書き直したもの．文とLeanの定理の対応は，その文書の「Leanによる確認」の節にある．

| ファイル | 中身 |
|---|---|
| `Example.lean` | 1節の例の数値（所要の高さ，見かけの下端，揃う配置と揃わない配置） |
| `MinH.lean` | 補題「割り振りごとの最小の高さ」と，最小とは限らない例 |
| `Fill.lean` | 補題「貪欲な分割」（止まること，(P1)，(P2)，(P3)，捨てられる要素） |
| `Bottom.lean` | 定義「見かけの下端」の一般の形と，段の脚注を置く位置の性質 |
| `Layout.lean` | 定義「所要の高さ」と「見かけの下端」を，本文の行の並びから求める計算（`Bottom.lean`を読み込む） |
| `Enum.lean` | 命題「揃えた配置の構成」の手順1（割り振りの列挙．段をまたぐフロート，候補の打ち切りを含む） |
| `Span.lean` | 同じ命題の手順1で，段をまたぐフロートが重なる候補を除く判定 |
| `Misaligned.lean` | 同じ命題の手順4の判定（揃わない配分）と，判定を通ったときに言えること |
| `Balance.lean` | 同じ命題の手順の全体を1つの関数につないだもの（`MinH.lean`と`Select.lean`を読み込む） |
| `Whole.lean` | 手順の全体に`Fill.lean`の手順を代入したときの，命題の(i)（`Fill.lean`と`Balance.lean`を読み込む） |
| `Select.lean` | 同じ命題の手順3（候補を選ぶ），手順4（高さを上げて探す），手順6（緩める） |
| `Beta.lean` | 命題「揃えた配置の構成」の(ii)（下端の決め方） |
| `Glue.lean` | 命題「段が揃うための条件」（箱のグルーの割り振りのモデル） |
| `Column.lean` | 手順5で各段の並びを作る部分（無限に伸びるグルーを入れる所．`Glue.lean`を読み込む） |
| `Link.lean` | ファイルどうしのつなぎ（`Span.lean`の判定を`Enum.lean`の候補に，`Beta.lean`の下端を`Column.lean`の箱の高さに，`Layout.lean`の高さを`Fill.lean`の本文の高さに代入する） |
| `Replay.lean` | 実装がログに書いた判断の記録をモデルで再生するための定義（実装の単位と余裕を引数に持つ形と，元の関数との一致） |
| `Page.lean` | 「ほかの場面への適用」（段組を改めるときの高さ，footnote=pageのくり返し） |

## 確かめ方

Lean 4とMathlibの入った作業場所で動かす（`Glue.lean`，`Column.lean`，`Link.lean`，`grid/GridGlue.lean`がMathlibを使う．ほかのファイルを読み込むファイルがあるので，1つずつではなく`check.sh`で確かめる）．

```bash
lean/check.sh
```

作業場所は，環境変数`LEAN_WS`で指定する（既定は`~/lean/mathlib-ws`．Lean v4.35.0，Mathlib v4.35.0で
確かめた）．`ok`が17並び，その後に`grid/`の2つの`ok`が出れば，すべての証明が通っている．

## モデルと実装の照らし合わせ

`grid/`のファイルは，証明ではなく，モデルの関数を動かすためのものである．

| ファイル | 中身 |
|---|---|
| `grid/GridGlue.lean` | `Glue.lean`のモデルの期待値を，格子状の入力（箱とグルーの並び，箱の高さ）について書き出す |
| `grid/GridLines.lean` | `Layout.lean`のモデルの期待値を，格子状の入力（行の高さと深さの並び）について書き出す |
| `grid/RunReplay.lean` | 実装がログに書いた判断の記録を読み，モデルの関数の結果と比べる |

`check.sh`は，`grid/GridGlue.lean`と`grid/GridLines.lean`を動かして，期待値を`expect/`に書き直す．
TeXの実測と比べるのは`test/model/run.sh`，判断の記録を再生するのは`test/model/replay.sh`．
モデルを変えて期待値が変わったら，`expect/`の差分に出る．

## 確かめていること，いないこと

確かめているのは，文書に書いた手順（モデル）が，書いた性質を持つことである．モデルが`evenend.lua`や
TeXの動作に合っていることは，Leanの証明では確かめられない．それは`test/`の試験が受け持つ
（乱数試験のほか，上の照らし合わせと，`evenend.lua`が`debug`のときに行うモデルの仮定の検査）．
