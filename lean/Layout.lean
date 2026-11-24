/-
evenendパッケージの定式化の定義「所要の高さ」と「見かけの下端」を，本文の行の並びから求める．
TeXが行を積むときの規則（\topskipと\baselineskip）をモデルにする．
確かめ方：lean/check.sh
-/
import Bottom

namespace Evenend.Layout

open Evenend.Bottom

/-- 本文の行：高さと深さ． -/
structure Line where
  ht : Nat
  dp : Nat

/-- 次の行のベースライン．前の行（ベースライン`B`，深さ`dp`）との間は，行送り`b`に収まれば
`b`，収まらなければ行を離して`\lineskip`（`ls`）を入れる（TeXの行送りの規則）． -/
def next (b ls B dp : Nat) (l : Line) : Nat :=
  if dp + l.ht ≤ b then B + b else B + dp + ls + l.ht

/-- 前の行のベースライン`B`と深さ`dp`から，残りの行を積んだときの最終行のベースライン． -/
def run (b ls : Nat) : Nat → Nat → List Line → Nat
  | B, _, [] => B
  | B, dp, l :: r => run b ls (next b ls B dp l) l.dp r

/-- 段の本文の最終行のベースライン（段の上端から）．最初の行は，高さが`\topskip`（`τ`）以下
なら`τ`の位置，高ければその高さの位置に置かれる．これが本文の高さ`|T_i|`（最後の行の深さは
箱の深さになり，高さに入らない）． -/
def lastBaseline (τ b ls : Nat) : List Line → Nat
  | [] => 0
  | l :: r => run b ls (max τ l.ht) l.dp r

/-- 行が行送りに収まる：どの行も高さが`ht`以下，深さが`dp`以下． -/
def Bounded (ht dp : Nat) (ls : List Line) : Prop := ∀ l ∈ ls, l.ht ≤ ht ∧ l.dp ≤ dp

theorem run_regular (b ls ht dp : Nat) (hb : dp + ht ≤ b) :
    ∀ (r : List Line) (B d0 : Nat), d0 ≤ dp → Bounded ht dp r →
      run b ls B d0 r = B + r.length * b := by
  intro r
  induction r with
  | nil => intro B d0 _ _; simp [run]
  | cons l r ih =>
    intro B d0 hd hr
    have hl := hr l (by simp)
    have hn : next b ls B d0 l = B + b := by
      unfold next
      split
      · rfl
      · omega
    simp only [run, hn]
    rw [ih (B + b) l.dp hl.2 (fun x hx => hr x (by simp [hx]))]
    simp only [List.length_cons, Nat.add_mul]
    omega

/-- 行の高さが`\topskip`以下で，行の高さと深さの和が行送り以下なら，`n`行の本文の最終行の
ベースラインは`τ + (n - 1)b`である（行は行送りの位置に並ぶ）． -/
theorem lastBaseline_regular (τ b ls ht dp : Nat) (hτ : ht ≤ τ) (hb : dp + ht ≤ b)
    (l : Line) (r : List Line) (h : Bounded ht dp (l :: r)) :
    lastBaseline τ b ls (l :: r) = τ + r.length * b := by
  have hl := h l (by simp)
  simp only [lastBaseline]
  rw [run_regular b ls ht dp hb r _ l.dp hl.2 (fun x hx => h x (by simp [hx]))]
  have : max τ l.ht = τ := Nat.max_eq_left (by omega)
  rw [this]

/-- 段の所要の高さ`U = A + |T| + G`．`A`はフロートの高さ，`T`は本文の高さ，`fn`は脚注の塊の
高さ（段の脚注がなければ`none`）．脚注があるとき，`G`は塊の高さに行の深さ`d`を足して`b`の
倍数に切り上げたもの． -/
def used (b d A T : Nat) : Option Nat → Nat
  | none => A + T
  | some fn => A + T + rows b (d + fn) * b

/-- 段の終わり方：上のフロート（高さ`A`）の下に本文（高さ`T`）を積み，脚注があればその下に
置く． -/
def ending (d A T : Nat) : Option Nat → End
  | none => .text (A + T)
  | some fn => .foot (A + T) d fn

/-- 本文か段の脚注で終わる段では，見かけの下端は，所要の高さに行の深さ`d`を足した位置である．
したがって，こうした段どうしでは，見かけの下端が揃うことと所要の高さが等しいことは同じである． -/
theorem v_eq_used (b d A T : Nat) (fn : Option Nat) :
    v b d (ending d A T fn) = used b d A T fn + d := by
  cases fn <;> simp [v, ending, used, base, below]

/-- 例の段：τ = 10，b = 12，行の高さ8，深さ3．段2は本文10行で，最終行のベースラインは118．
段1は上のフロート48，本文4行（高さ46），脚注の塊20で，所要の高さは118，見かけの下端は121．
段3は本文9行で，所要の高さ106，見かけの下端109． -/
example : lastBaseline 10 12 1 (List.replicate 10 ⟨8, 3⟩) = 118 ∧
    lastBaseline 10 12 1 (List.replicate 4 ⟨8, 3⟩) = 46 ∧
    used 12 3 48 46 (some 20) = 118 ∧ v 12 3 (ending 3 48 46 (some 20)) = 121 ∧
    used 12 3 0 (lastBaseline 10 12 1 (List.replicate 9 ⟨8, 3⟩)) none = 106 ∧
    v 12 3 (ending 3 0 106 none) = 109 := by decide

/-- 行送りに収まらない行（高さ14）があると，その後の行は行送りの位置からずれる
（3行で34でなく40）． -/
example : lastBaseline 10 12 1 [⟨8, 3⟩, ⟨14, 3⟩, ⟨8, 3⟩] = 40 := by decide

end Evenend.Layout
