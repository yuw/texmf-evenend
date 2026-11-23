/-
evenendパッケージの定式化（doc/lualatex/evenend/evenend-theory-ja.tex）の1節の例を確かめる．
長さの単位はpt．確かめ方：cd ~/lean/mathlib-ws && lake env lean <このファイルの絶対パス>
-/
namespace Evenend.Example

/-- 行送り -/
def b : Nat := 12
/-- 1行目のベースラインの位置（\topskip） -/
def τ : Nat := 10
/-- 本文の行の深さ -/
def d : Nat := 3
/-- 段の高さ -/
def H : Nat := 178

/-- 例2（段組）：版面238ptから段抜きのフロート60ptを除く．15行入る． -/
example : H = 238 - 60 := rfl
example : H = τ + 14 * b := rfl

/-- `l`行の本文の高さ（最終行のベースラインまで） -/
def textHt (l : Nat) : Nat := if l = 0 then 0 else τ + (l - 1) * b

/-- `m`の倍数への切り上げ -/
def ceilTo (m x : Nat) : Nat := (x + m - 1) / m * m

/-- 段：フロートの高さ，本文の行数，脚注の塊の高さ（脚注がなければ0） -/
structure Col where
  A : Nat
  lines : Nat
  fn : Nat

/-- 脚注の高さ G（定義7．footnote=column）：塊に行の深さを足し，行送りの倍数に切り上げる -/
def G (c : Col) : Nat := if c.fn = 0 then 0 else ceilTo b (c.fn + d)

/-- 所要の高さ U（定義7） -/
def U (c : Col) : Nat := c.A + textHt c.lines + G c

/-- 見かけの下端 v（定義9）．本文の行で終わる段と，段の脚注で終わる段 -/
def v (c : Col) : Nat :=
  if c.fn = 0 then c.A + textHt c.lines + d
  else c.A + textHt c.lines + ceilTo b (d + c.fn) + d

/-- 例6：LaTeXが組んだ配置 k⁰ = (0, 9, 23, 23) -/
def k0 : List Col := [⟨48, 9, 20⟩, ⟨0, 14, 0⟩, ⟨0, 0, 0⟩]
/-- 例6：揃えた配置 k = (0, 4, 14, 23) -/
def k : List Col := [⟨48, 4, 20⟩, ⟨0, 10, 0⟩, ⟨0, 9, 0⟩]
/-- 例12：揃っていない配置 k' = (0, 4, 13, 23) -/
def k' : List Col := [⟨48, 4, 20⟩, ⟨0, 9, 0⟩, ⟨0, 10, 0⟩]

/-- どの配置も本文は23行 -/
example : (k0.map Col.lines).sum = 23 ∧ (k.map Col.lines).sum = 23 ∧ (k'.map Col.lines).sum = 23 := by
  decide

/-- 例8（所要の高さ） -/
example : k.map U = [118, 118, 106] := by decide
example : k0.map U = [178, 166, 0] := by decide
/-- kはh = 118に入り切り，k⁰は117には入り切らない -/
example : k.all (fun c => U c ≤ 118) = true := by decide
example : k0.all (fun c => U c ≤ H) = true ∧ k0.all (fun c => U c ≤ H - 1) = false := by decide

/-- 例10（見かけの下端） -/
example : k.map v = [121, 121, 109] := by decide
example : k'.map v = [121, 109, 121] := by decide

/-- 本文だけの段（フロートも脚注もない） -/
def textOnly (c : Col) : Bool := c.A == 0 && c.fn == 0

/-- 途中の段を下端βに合わせられるか（定義11の1と3）．本文だけの段は動かせないので，
初めからβにあるときだけ．脚注のある段は，脚注を下げてβに合わせられる（上げられない）． -/
def canReach (β : Nat) (c : Col) : Bool :=
  if textOnly c then v c == β else v c ≤ β

/-- 3段とも中身のある配置が，下端βで揃っている（定義11） -/
def aligned (β : Nat) : List Col → Bool
  | [c1, c2, c3] => canReach β c1 && canReach β c2 && v c3 ≤ β
  | _ => false

/-- 例12：kはβ = 121で揃っている -/
example : aligned 121 k = true := by decide

/-- 例12：k'は，どのβでも揃っていない -/
example : ∀ β, aligned β k' = false := by
  intro β
  have h1 : v ⟨0, 9, 0⟩ = 109 := by decide
  have h2 : v ⟨0, 10, 0⟩ = 121 := by decide
  have h3 : textOnly ⟨0, 9, 0⟩ = true := by decide
  simp only [aligned, k', canReach, h1, h2, h3]
  simp
  omega

end Evenend.Example
