/-
evenendパッケージの定式化の命題「揃えた配置の構成」の手順3（候補を選ぶ），手順4（揃わない配分を
直す），手順6（緩める）を確かめる．
長さの単位は，高さを調べる刻み（1pt）の半分．
確かめ方：cd ~/lean/mathlib-ws && lake env lean <このファイルの絶対パス>
-/
namespace Evenend.Select

/-- 候補：動かす量μと，高さh(σ) -/
structure Cand where
  m : Nat
  h : Nat
  deriving DecidableEq, Repr

/-- 手順3の規則：最良`best`を候補`c`で置き換えるか．`g`は1行（行送り）．
・動かす量が同じか少ないとき：高さが1行未満しか高くならず，しかも，明らかに低いか，動かす量が
  少ないなら，置き換える．
・動かす量が多いとき：1行以上低くなるときだけ，置き換える． -/
def better (g : Nat) (best c : Cand) : Bool :=
  (c.m ≤ best.m && c.h + 1 < best.h + g && (c.h + 1 < best.h || c.m < best.m))
    || (best.m < c.m && c.h + g < best.h + 1)

/-- 候補を順に見て，最良を選ぶ -/
def select (g : Nat) : Option Cand → List Cand → Option Cand
  | best, [] => best
  | none, c :: cs => select g (some c) cs
  | some b, c :: cs => select g (some (if better g b c then c else b)) cs

/-- 選んだものは，初めの最良か，候補のどれかである． -/
theorem select_mem (g : Nat) :
    ∀ (cs : List Cand) (init : Option Cand) (r : Cand),
      select g init cs = some r → init = some r ∨ r ∈ cs := by
  intro cs
  induction cs with
  | nil => intro init r hs; simp [select] at hs; exact Or.inl hs
  | cons c cs ih =>
    intro init r hs
    cases init with
    | none =>
      simp only [select] at hs
      rcases ih (some c) r hs with h1 | h1
      · simp only [Option.some.injEq] at h1; subst h1; exact Or.inr (by simp)
      · exact Or.inr (by simp [h1])
    | some b =>
      simp only [select] at hs
      rcases ih _ r hs with h1 | h1
      · simp only [Option.some.injEq] at h1
        split at h1
        · subst h1; exact Or.inr (by simp)
        · subst h1; exact Or.inl rfl
      · exact Or.inr (by simp [h1])

/-- 入り切る候補が1つでもあれば，必ずどれかを選ぶ（選べないのは，候補がないときだけ）． -/
theorem select_isSome (g : Nat) :
    ∀ (cs : List Cand) (init : Option Cand),
      (init.isSome = true ∨ cs ≠ []) → (select g init cs).isSome = true := by
  intro cs
  induction cs with
  | nil => intro init h; simpa [select] using h
  | cons c cs ih =>
    intro init _
    cases init with
    | none => simp only [select]; exact ih _ (Or.inl rfl)
    | some b => simp only [select]; exact ih _ (Or.inl rfl)

/-- 注意：選んだ高さは，調べた候補の最小より1行以上高いことがある．
1行を12pt（`g = 24`）として，候補が（μ = 2，100pt），（μ = 1，110pt），（μ = 0，120pt）の順に
来ると，動かす量の少ないほうへ2回置き換わり，最小より20pt高い120ptを選ぶ． -/
example : select 24 none [⟨2, 200⟩, ⟨1, 220⟩, ⟨0, 240⟩] = some ⟨0, 240⟩ := by decide

/-- 手順4：`good h`は「Fill(σ*, h)が成功し，揃わない配分でない」．`h`から1ずつ上げて，`H`までで
最初に`good`になる高さを探す． -/
def raise (good : Nat → Bool) (H : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, h => if H < h then none else if good h then some h else raise good H fuel (h + 1)

theorem raise_spec (good : Nat → Bool) (H : Nat) :
    ∀ (fuel h r : Nat), raise good H fuel h = some r → h ≤ r ∧ r ≤ H ∧ good r = true := by
  intro fuel
  induction fuel with
  | zero => intro h r hr; simp [raise] at hr
  | succ k ih =>
    intro h r hr
    simp only [raise] at hr
    split at hr
    · simp at hr
    · split at hr
      · rename_i hH hg
        simp only [Option.some.injEq] at hr
        subst hr
        exact ⟨Nat.le_refl _, by omega, hg⟩
      · have := ih (h + 1) r hr
        exact ⟨by omega, this.2.1, this.2.2⟩

/-- 手順4の全体：`h*`が揃わない配分なら上げて探し，見つからなければ`h*`のままにする． -/
def step4 (good : Nat → Bool) (H hstar : Nat) : Nat :=
  if good hstar then hstar else (raise good H (H - hstar) (hstar + 1)).getD hstar

/-- 手順4の結果は，元の`h*`か，`h*`より高く`H`以下で`good`な高さである． -/
theorem step4_spec (good : Nat → Bool) (H hstar : Nat) :
    step4 good H hstar = hstar ∨
    (hstar < step4 good H hstar ∧ step4 good H hstar ≤ H ∧ good (step4 good H hstar) = true) := by
  unfold step4
  split
  · exact Or.inl rfl
  · cases hr : raise good H (H - hstar) (hstar + 1) with
    | none => exact Or.inl rfl
    | some r =>
      have := raise_spec good H _ _ r hr
      exact Or.inr ⟨by simp; omega, by simpa using this.2.1, by simpa using this.2.2⟩

/-- 手順6：条件を緩めながら，高々3回試す（そのまま，脚注を切り上げない，floatgridもやめる）．
`attempt k`は，緩め方`k`での手順1から5の結果． -/
def relax {α : Type} (attempt : Nat → Option α) : Option α :=
  match attempt 0 with
  | some r => some r
  | none =>
    match attempt 1 with
    | some r => some r
    | none => attempt 2

/-- 返した結果は，3回のどれかの結果である．どれも失敗したときだけ「揃えられない」． -/
theorem relax_spec {α : Type} (attempt : Nat → Option α) (r : α) (h : relax attempt = some r) :
    ∃ k, k < 3 ∧ attempt k = some r := by
  unfold relax at h
  split at h
  · rename_i r0 h0
    simp only [Option.some.injEq] at h; subst h; exact ⟨0, by omega, h0⟩
  · split at h
    · rename_i r1 h1
      simp only [Option.some.injEq] at h; subst h; exact ⟨1, by omega, h1⟩
    · exact ⟨2, by omega, h⟩

theorem relax_none {α : Type} (attempt : Nat → Option α) :
    relax attempt = none ↔ attempt 0 = none ∧ attempt 1 = none ∧ attempt 2 = none := by
  unfold relax
  cases h0 : attempt 0 <;> cases h1 : attempt 1 <;> cases h2 : attempt 2 <;> simp

end Evenend.Select
