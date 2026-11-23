/-
evenendパッケージの定式化の命題「揃えた配置の構成」の手順1（候補を挙げる）を確かめる．
割り振りσを，各フロートの置く段の並び`List Nat`で表す．段をまたぐフロートと，候補が多い
ときの打ち切りは扱わない．
確かめ方：cd ~/lean/mathlib-ws && lake env lean <このファイルの絶対パス>
-/
namespace Evenend.Enum

/-- 割り振りの条件（定義「配置」）．`lo`はここまでに置いた段（初めは1），`os`はLaTeXが置いた段．
番号順を保ち（前のフロートの段以上），前の段へ動かさず（`o`以上），段数`N`を超えない． -/
inductive Valid (N : Nat) : Nat → List Nat → List Nat → Prop
  | nil {lo : Nat} : Valid N lo [] []
  | cons {lo o c : Nat} {os σ : List Nat} :
      lo ≤ c → o ≤ c → c ≤ N → Valid N c os σ → Valid N lo (o :: os) (c :: σ)

/-- 割り振りの列挙 -/
def enumFrom (N : Nat) : Nat → List Nat → List (List Nat)
  | _, [] => [[]]
  | lo, o :: os =>
    (List.range (N + 1)).flatMap fun c =>
      if lo ≤ c ∧ o ≤ c then (enumFrom N c os).map (c :: ·) else []

/-- 列挙は，条件を満たす割り振りのすべてを，それだけを挙げる． -/
theorem mem_enumFrom (N : Nat) :
    ∀ (os : List Nat) (lo : Nat) (σ : List Nat), σ ∈ enumFrom N lo os ↔ Valid N lo os σ := by
  intro os
  induction os with
  | nil =>
    intro lo σ
    simp only [enumFrom, List.mem_singleton]
    constructor
    · rintro rfl; exact Valid.nil
    · intro hv; cases hv; rfl
  | cons o os ih =>
    intro lo σ
    simp only [enumFrom, List.mem_flatMap, List.mem_range]
    constructor
    · rintro ⟨c, hc, hmem⟩
      split at hmem
      · rename_i hlo
        simp only [List.mem_map] at hmem
        obtain ⟨σ', hσ', rfl⟩ := hmem
        exact Valid.cons hlo.1 hlo.2 (by omega) ((ih c σ').mp hσ')
      · simp at hmem
    · intro hv
      cases hv with
      | cons h1 h2 h3 h4 =>
        rename_i c σ'
        refine ⟨c, by omega, ?_⟩
        simp only [h1, h2, and_self, ite_true, List.mem_map]
        exact ⟨σ', (ih c σ').mpr h4, rfl⟩

/-- 例（図「材料と配置」の下）：2段で，2つのフロートをどちらもLaTeXが段1に置いたとき，
割り振りは3つ． -/
example : enumFrom 2 1 [1, 1] = [[1, 1], [1, 2], [2, 2]] := by decide

/-- 例6：3段で，フロートが1つ（段1）のとき，割り振りは3つ． -/
example : enumFrom 3 1 [1] = [[1], [2], [3]] := by decide

end Evenend.Enum
