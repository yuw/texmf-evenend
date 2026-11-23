/-
evenendパッケージの定式化の定義「見かけの下端」を，一般の形で書く．
確かめ方：cd ~/lean/mathlib-ws && lake env lean <このファイルの絶対パス>
-/
namespace Evenend.Bottom

/-- 段の終わり方．
`text B`：本文の行で終わる（最終行のベースラインが`B`）．
`botFloat y`：下のフロートで終わる（フロートの下端が`y`）．
`foot B dp fn`：段の脚注で終わる（本文の最終行のベースラインが`B`，その行の深さが`dp`，
脚注の塊の高さが`fn`）．
`vbox y`：垂直の箱で終わり，中身が箱の下端より下に出ている（中身の下端が`y`）． -/
inductive End
  | text (B : Nat)
  | botFloat (y : Nat)
  | foot (B dp fn : Nat)
  | vbox (y : Nat)

/-- 脚注が収まるのに要る行数：`dp + fn`を行送り`b`で割って切り上げる． -/
def rows (b x : Nat) : Nat := (x + b - 1) / b

/-- 最後の要素の基準線の位置`n` -/
def base (b : Nat) : End → Nat
  | .text B => B
  | .botFloat y => y
  | .foot B dp fn => B + rows b (dp + fn) * b
  | .vbox y => y

/-- 基準線より下に見える分`e`（`d`は本文の行の標準の深さ） -/
def below (d : Nat) : End → Nat
  | .text _ => d
  | .botFloat _ => 0
  | .foot _ _ _ => d
  | .vbox _ => 0

/-- 見かけの下端`v = n + e` -/
def v (b d : Nat) (e : End) : Nat := base b e + below d e

theorem rows_spec (b x : Nat) (hb : 0 < b) : x ≤ rows b x * b ∧ rows b x * b < x + b := by
  unfold rows
  have h1 := Nat.div_add_mod (x + b - 1) b
  have h2 := Nat.mod_lt (x + b - 1) hb
  rw [Nat.mul_comm] at h1
  constructor <;> omega

/-- 段の脚注：最終行のベースラインを置いた位置に，行の深さと脚注の塊が収まる． -/
theorem foot_fits (b B dp fn : Nat) (hb : 0 < b) :
    B + dp + fn ≤ base b (.foot B dp fn) := by
  have := (rows_spec b (dp + fn) hb).1
  simp only [base]
  omega

/-- 段の脚注：その位置は，収まる最初の行の位置である（1行上では収まらない）． -/
theorem foot_first (b B dp fn : Nat) (hb : 0 < b) :
    base b (.foot B dp fn) < B + dp + fn + b := by
  have := (rows_spec b (dp + fn) hb).2
  simp only [base]
  omega

/-- 段の脚注：本文の最終行が行の位置（`τ + ℓb`）にあれば，脚注の最終行のベースラインも
行の位置にある． -/
theorem foot_grid (b τ l dp fn : Nat) :
    ∃ l', base b (.foot (τ + l * b) dp fn) = τ + l' * b := by
  refine ⟨l + rows b (dp + fn), ?_⟩
  simp only [base, Nat.add_mul]
  omega

/-- 例10：b = 12，d = 3で，段1（本文の最終行のベースライン94，脚注の塊20），段2（118），
段3（106）の見かけの下端は121，121，109． -/
example : v 12 3 (.foot 94 3 20) = 121 ∧ v 12 3 (.text 118) = 121 ∧ v 12 3 (.text 106) = 109 := by
  decide

end Evenend.Bottom
