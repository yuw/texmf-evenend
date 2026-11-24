/-
evenendパッケージの定式化の命題「揃えた配置の構成」の手順1（候補を挙げる）を確かめる．
割り振りσ（定式化の文書のs）を，各フロートの置く段の並び`List Nat`で表す．段をまたぐフロートと，候補が多い
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

/-! ### 段をまたぐフロートと，候補が多いときの打ち切り -/

/-- フロート：LaTeXが置いた段`o`，段をまたぐか，持ち越したものか -/
structure Fl where
  o : Nat
  span : Bool
  deferred : Bool

/-- 置かれた段から動かさないフロートか．段をまたぐフロートはつねに動かさない．候補を絞るとき
（`fixed`）は，持ち越したフロートのほかは動かさない． -/
def pinned (fixed : Bool) (f : Fl) : Bool := f.span || (fixed && !f.deferred)

/-- 割り振りの条件．動かさないフロートは，LaTeXが置いた段のまま． -/
inductive ValidG (N : Nat) (fixed : Bool) : Nat → List Fl → List Nat → Prop
  | nil {lo : Nat} : ValidG N fixed lo [] []
  | cons {lo c : Nat} {f : Fl} {fs : List Fl} {σ : List Nat} :
      lo ≤ c → f.o ≤ c → c ≤ N → (pinned fixed f = true → c = f.o) →
      ValidG N fixed c fs σ → ValidG N fixed lo (f :: fs) (c :: σ)

/-- 割り振りの列挙 -/
def enumG (N : Nat) (fixed : Bool) : Nat → List Fl → List (List Nat)
  | _, [] => [[]]
  | lo, f :: fs =>
    (List.range (N + 1)).flatMap fun c =>
      if lo ≤ c ∧ f.o ≤ c ∧ (pinned fixed f = true → c = f.o) then
        (enumG N fixed c fs).map (c :: ·)
      else []

theorem mem_enumG (N : Nat) (fixed : Bool) :
    ∀ (fs : List Fl) (lo : Nat) (σ : List Nat),
      σ ∈ enumG N fixed lo fs ↔ ValidG N fixed lo fs σ := by
  intro fs
  induction fs with
  | nil =>
    intro lo σ
    simp only [enumG, List.mem_singleton]
    constructor
    · rintro rfl; exact ValidG.nil
    · intro hv; cases hv; rfl
  | cons f fs ih =>
    intro lo σ
    simp only [enumG, List.mem_flatMap, List.mem_range]
    constructor
    · rintro ⟨c, hc, hmem⟩
      split at hmem
      · rename_i hlo
        simp only [List.mem_map] at hmem
        obtain ⟨σ', hσ', rfl⟩ := hmem
        exact ValidG.cons hlo.1 hlo.2.1 (by omega) hlo.2.2 ((ih c σ').mp hσ')
      · simp at hmem
    · intro hv
      cases hv with
      | cons h1 h2 h3 h4 h5 =>
        rename_i c σ'
        refine ⟨c, by omega, ?_⟩
        split
        · simp only [List.mem_map]
          exact ⟨σ', (ih c σ').mpr h5, rfl⟩
        · rename_i hn
          exact absurd ⟨h1, h2, h4⟩ hn

/-- 絞った候補も，絞らないときの条件を満たす（割り振りの全体Sの元である）． -/
theorem validG_fixed (N : Nat) :
    ∀ (fs : List Fl) (lo : Nat) (σ : List Nat),
      ValidG N true lo fs σ → ValidG N false lo fs σ := by
  intro fs
  induction fs with
  | nil => intro lo σ hv; cases hv; exact ValidG.nil
  | cons f fs ih =>
    intro lo σ hv
    cases hv with
    | cons h1 h2 h3 h4 h5 =>
      refine ValidG.cons h1 h2 h3 ?_ (ih _ _ h5)
      intro hp
      apply h4
      simp only [pinned, Bool.or_eq_true] at hp ⊢
      rcases hp with hp | hp
      · exact Or.inl hp
      · simp at hp

/-- 手順1の候補：すべての割り振りを高々257個まで挙げる．64個を超えるときは，絞った条件で
挙げ直す．最後に，段をまたぐフロートが重なる候補を除く（`spanOk`は任意の述語）． -/
def candidates (N : Nat) (spanOk : List Nat → Bool) (fs : List Fl) : List (List Nat) :=
  let all := (enumG N false 1 fs).take 257
  (if 64 < all.length then (enumG N true 1 fs).take 257 else all).filter spanOk

/-- 候補は，どれも割り振りの条件を満たす． -/
theorem candidates_valid (N : Nat) (spanOk : List Nat → Bool) (fs : List Fl) (σ : List Nat)
    (h : σ ∈ candidates N spanOk fs) : ValidG N false 1 fs σ := by
  unfold candidates at h
  simp only [List.mem_filter] at h
  have h1 := h.1
  split at h1
  · exact validG_fixed N fs 1 σ ((mem_enumG N true fs 1 σ).mp (List.mem_of_mem_take h1))
  · exact (mem_enumG N false fs 1 σ).mp (List.mem_of_mem_take h1)

/-- 候補は高々257個． -/
theorem candidates_length (N : Nat) (spanOk : List Nat → Bool) (fs : List Fl) :
    (candidates N spanOk fs).length ≤ 257 := by
  unfold candidates
  refine Nat.le_trans (List.length_filter_le _ _) ?_
  split <;> simp [List.length_take] <;> omega

/-- LaTeXが置いた段の並びが番号順で，段数を超えなければ，LaTeXの割り振りσ⁰（どのフロートも
置かれた段のまま）は，絞ったときも含めて，つねに列挙に入る． -/
theorem self_valid (N : Nat) (fixed : Bool) :
    ∀ (fs : List Fl) (lo : Nat),
      (fs.map Fl.o).Pairwise (· ≤ ·) → (∀ f ∈ fs, lo ≤ f.o ∧ f.o ≤ N) →
      ValidG N fixed lo fs (fs.map Fl.o) := by
  intro fs
  induction fs with
  | nil => intro lo _ _; exact ValidG.nil
  | cons f fs ih =>
    intro lo hs hb
    simp only [List.map_cons, List.pairwise_cons] at hs
    have hf := hb f (by simp)
    refine ValidG.cons hf.1 (Nat.le_refl _) hf.2 (fun _ => rfl) (ih f.o hs.2 ?_)
    intro f' hf'
    exact ⟨hs.1 f'.o (List.mem_map_of_mem hf'), (hb f' (by simp [hf'])).2⟩

end Evenend.Enum
