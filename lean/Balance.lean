/-
evenendパッケージの定式化の命題「揃えた配置の構成」の手順の全体を，1つの関数につなぐ．
補題の手順（MinH.lean），候補を選ぶ規則と手順4，6（Select.lean）を使う．
確かめ方：lean/check.sh
-/
import MinH
import Select

namespace Evenend.Balance

open Evenend.MinH Evenend.Select

/-
`S`は割り振りσの型，`L`は配置．`fillAt σ h`は手順Fill(σ, h)（成功すれば配置を返す），`mu`は動かす量，
`h0`は二分法の下界，`aligned σ h`は「揃わない配分でない」，`H`は段の高さ，`g`は1行．
-/
variable {S L : Type} (fillAt : S → Nat → Option L) (mu : S → Nat) (h0 : S → Nat)
  (aligned : S → Nat → Bool) (H g : Nat)

/-- 手順2：各候補の高さh(σ)を求め，入り切る候補だけを残す． -/
def heights (σs : List S) : List (Cand S) :=
  σs.filterMap fun σ =>
    (minH (fun h => (fillAt σ h).isSome) (h0 σ) H).map fun h => ⟨σ, mu σ, h⟩

/-- 手順1から5：候補`σs`から，割り振り，高さ，配置を決める．どの候補も入り切らなければ`none`． -/
def balance (σs : List S) : Option (S × Nat × L) :=
  match select g none (heights fillAt mu h0 H σs) with
  | none => none
  | some c =>
    let h := step4 (fun h => (fillAt c.tag h).isSome && aligned c.tag h) H c.h
    (fillAt c.tag h).map fun l => (c.tag, h, l)

theorem mem_heights (σs : List S) (c : Cand S) (hc : c ∈ heights fillAt mu h0 H σs) :
    c.tag ∈ σs ∧ (fillAt c.tag c.h).isSome = true ∧ c.h ≤ H := by
  simp only [heights, List.mem_filterMap, Option.map_eq_some_iff] at hc
  obtain ⟨σ, hσ, h, hm, rfl⟩ := hc
  have := minH_spec _ _ _ _ hm
  exact ⟨hσ, this.1, this.2⟩

/-- 命題の(i)：手順が返すのは，候補のどれかの割り振りσと，高さ`h ≤ H`と，Fill(σ, h)が
返した配置である． -/
theorem balance_spec (σs : List S) (σ : S) (h : Nat) (l : L)
    (hb : balance fillAt mu h0 aligned H g σs = some (σ, h, l)) :
    σ ∈ σs ∧ h ≤ H ∧ fillAt σ h = some l := by
  unfold balance at hb
  split at hb
  · simp at hb
  · rename_i c hsel
    have hc : c ∈ heights fillAt mu h0 H σs := by
      rcases select_mem g _ none c hsel with h1 | h1
      · simp at h1
      · exact h1
    have hm := mem_heights fillAt mu h0 H σs c hc
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hb
    obtain ⟨l', hl', rfl, rfl, rfl⟩ := hb
    refine ⟨hm.1, ?_, hl'⟩
    rcases step4_spec (fun h => (fillAt c.tag h).isSome && aligned c.tag h) H c.h with h1 | h1
    · rw [h1]; exact hm.2.2
    · exact h1.2.1

/-- 候補のどれかが高さ`H`に入り切れば，手順は必ず配置を返す． -/
theorem balance_isSome (σs : List S) (σ : S) (hσ : σ ∈ σs)
    (hfit : (fillAt σ H).isSome = true) :
    (balance fillAt mu h0 aligned H g σs).isSome = true := by
  have hne : heights fillAt mu h0 H σs ≠ [] := by
    have hs := minH_isSome (fun h => (fillAt σ h).isSome) (h0 σ) H hfit
    obtain ⟨hh, hm⟩ := Option.isSome_iff_exists.mp hs
    intro hnil
    have : (⟨σ, mu σ, hh⟩ : Cand S) ∈ heights fillAt mu h0 H σs := by
      simp only [heights, List.mem_filterMap, Option.map_eq_some_iff]
      exact ⟨σ, hσ, hh, hm, rfl⟩
    rw [hnil] at this
    simp at this
  have hsel := select_isSome g (heights fillAt mu h0 H σs) none (Or.inr hne)
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hsel
  have hcm : c ∈ heights fillAt mu h0 H σs := by
    rcases select_mem g _ none c hc with h1 | h1
    · simp at h1
    · exact h1
  have hm := mem_heights fillAt mu h0 H σs c hcm
  unfold balance
  simp only [hc, Option.isSome_map]
  rcases step4_spec (fun h => (fillAt c.tag h).isSome && aligned c.tag h) H c.h with h1 | h1
  · rw [h1]; exact hm.2.1
  · have := h1.2.2
    simp only [Bool.and_eq_true] at this
    exact this.1

/-- 手順の全体（手順6を含む）：緩め方`k = 0, 1, 2`の順に試す．`fillK k`は緩め方`k`でのFill． -/
def procedure (fillK : Nat → S → Nat → Option L) (σs : List S) : Option (S × Nat × L) :=
  relax fun k => balance (fillK k) mu h0 aligned H g σs

/-- 手順の全体が返す配置は，ある緩め方`k < 3`でのFill(σ, h)が返したもので，σは候補のどれか，
`h ≤ H`である．`P k σ h l`が「配置`l`が（緩め方`k`の所要の高さで）割り振り`σ`と高さ`h`について(P1)から(P3)を
満たす」を表し，Fillが返す配置がつねに`P`を満たす（補題）なら，手順の全体が返す配置も`P`を
満たす． -/
theorem procedure_spec (fillK : Nat → S → Nat → Option L) (σs : List S)
    (P : Nat → S → Nat → L → Prop)
    (hfill : ∀ k σ h l, fillK k σ h = some l → P k σ h l)
    (σ : S) (h : Nat) (l : L)
    (hp : procedure mu h0 aligned H g fillK σs = some (σ, h, l)) :
    σ ∈ σs ∧ h ≤ H ∧ ∃ k, k < 3 ∧ P k σ h l := by
  obtain ⟨k, hk, hb⟩ := relax_spec _ _ hp
  have := balance_spec (fillK k) mu h0 aligned H g σs σ h l hb
  exact ⟨this.1, this.2.1, k, hk, hfill k σ h l this.2.2⟩

/-- 「揃えられない」と答えるのは，3つの緩め方のどれでも，どの候補も高さ`H`に入り切らない
ときだけである． -/
theorem procedure_none (fillK : Nat → S → Nat → Option L) (σs : List S)
    (hp : procedure mu h0 aligned H g fillK σs = none) :
    ∀ k, k < 3 → ∀ σ ∈ σs, fillK k σ H = none := by
  have h3 := (relax_none _).mp hp
  intro k hk σ hσ
  have hbk : balance (fillK k) mu h0 aligned H g σs = none := by
    have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases this with rfl | rfl | rfl
    · exact h3.1
    · exact h3.2.1
    · exact h3.2.2
  cases hf : fillK k σ H with
  | none => rfl
  | some l =>
    have := balance_isSome (fillK k) mu h0 aligned H g σs σ hσ (by simp [hf])
    rw [hbk] at this
    simp at this

end Evenend.Balance
