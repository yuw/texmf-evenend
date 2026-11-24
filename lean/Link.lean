/-
evenendパッケージの定式化のLeanのファイルどうしをつなぐ．
1. 段をまたぐフロートの判定（Span.lean）を，候補の列挙（Enum.lean）に代入する．
2. 下端β（Beta.lean）を，段の並びを組む箱の高さ（Column.lean）に代入する．
3. 行の並びから求めた本文の高さ（Layout.lean）を，貪欲な分割（Fill.lean）に代入する．
確かめ方：lean/check.sh
-/
import Enum
import Span
import Beta
import Column
import Layout
import Fill

namespace Evenend.Link

/-! ### 1. 段をまたぐフロートの判定を，候補の列挙に代入する -/

open Evenend.Enum Evenend.Span in
/-- 手順1の候補（判定を代入したもの）：どれも割り振りの条件を満たし，段をまたぐフロートは
どれも段`N`を越えず，どの2つも両立する（同じ位置で同じ段にかかるなら，同じ段から同じ段数に
またがる）． -/
theorem candidates_span (N : Nat) (geom : List (Option (Bool × Nat))) (fs : List Fl)
    (σ : List Nat)
    (h : σ ∈ candidates N (fun σ => spanOk N (placements geom σ)) fs) :
    ValidG N false 1 fs σ ∧
    (∀ s ∈ placements geom σ, ∀ x, covers s x = true → x ≤ N) ∧
    (placements geom σ).Pairwise Compat := by
  have hv := candidates_valid N _ fs σ h
  unfold candidates at h
  simp only [List.mem_filter] at h
  exact ⟨hv, (spanOk_iff N _).mp h.2⟩

/-! ### 2. 下端βを，段を組む箱の高さに代入する -/

open Evenend.Beta Evenend.Glue Evenend.Column in
/-- 段`c`（見かけの下端`c.1`，グルーの縮み`c.2`）を，手順5の下端βから`e`を引いた高さの箱に
組む．段の並びの自然な高さが`c.1 - e`（最後の要素の基準線の位置），並びの縮みが`c.2`以上で，
下端がβに届かない段には\vfilか有限の伸びがあるなら，中身は箱の高さちょうどになる
（最後の要素の基準線がβ - eに，見かけの下端がβに来る）． -/
theorem column_packed (βT : Option Nat) (cs : List (Nat × Nat)) (c : Nat × Nat) (hc : c ∈ cs)
    (e : Nat) (p : Parts) (a b : Bool) (hn : NoFil p)
    (hnat : natAll p = (c.1 : ℚ) - e) (hshr : (c.2 : ℚ) ≤ shr (build p a b))
    (hst : c.1 ≤ chooseBeta βT cs → (a || b) = true ∨ 0 < finS (build p a b)) :
    packed ((chooseBeta βT cs : ℚ) - e) (build p a b) = (chooseBeta βT cs : ℚ) - e := by
  have hb := nat_build p a b
  by_cases hle : c.1 ≤ chooseBeta βT cs
  · have hq : (c.1 : ℚ) ≤ (chooseBeta βT cs : ℚ) := by exact_mod_cast hle
    apply packed_stretch
    · rw [hb, hnat]; linarith
    · rcases hst hle with h1 | h1
      · left; rw [filS_build p a b hn, h1]; norm_num
      · right; exact h1
  · have h1 := le_chooseBeta βT cs c hc
    have h2 : c.1 ≤ chooseBeta βT cs + c.2 := by omega
    have hq : (c.1 : ℚ) ≤ (chooseBeta βT cs : ℚ) + c.2 := by exact_mod_cast h2
    have hgt : (chooseBeta βT cs : ℚ) < c.1 := by exact_mod_cast Nat.lt_of_not_le hle
    apply packed_shrink
    · rw [hb, hnat]; linarith
    · rw [hb, hnat]; linarith

/-! ### 3. 行の並びから求めた本文の高さを，貪欲な分割に代入する -/

open Evenend.Fill Evenend.Layout in
/-- 行だけが並ぶ本文のモデル．本文の高さは，行を積んだときの最終行のベースライン．
`\vsplit`は，行の間で切る（`cut c t`行目の後．どこで切るかは任意）．行の間に捨てられる
要素はない． -/
def lineSpec {Note : Type} (τ b ls : Nat) (notes : Line → List Note)
    (noteHt : List Note → Nat) (cut : Nat → List Line → Nat) : Spec Line Note where
  ht := lastBaseline τ b ls
  disc := fun _ => false
  notes := notes
  noteHt := noteHt
  split := fun c t => (t.take (cut c t), t.drop (cut c t))
  split_keep := by intro c t; simp
  disc_notes := by intro x hx; simp at hx

open Evenend.Fill Evenend.Layout in
/-- 行が行送りに収まるとき，`n`行の本文の段が高さ`h`に入り切るのは，
`A + τ + (n - 1)b + G ≤ h`のとき，そのときだけである． -/
theorem fits_lines {Note : Type} (τ b ls ht dp : Nat) (notes : Line → List Note)
    (noteHt : List Note → Nat) (cut : Nat → List Line → Nat)
    (hτ : ht ≤ τ) (hb : dp + ht ≤ b) (h A : Nat) (l : Line) (r : List Line)
    (hbd : Bounded ht dp (l :: r)) :
    Fits (lineSpec τ b ls notes noteHt cut) h A (l :: r) ↔
      A + (τ + r.length * b) + G (lineSpec τ b ls notes noteHt cut) (l :: r) ≤ h := by
  unfold Fits
  have : (lineSpec τ b ls notes noteHt cut).ht (l :: r) = τ + r.length * b :=
    lastBaseline_regular τ b ls ht dp hτ hb l r hbd
  rw [this]

open Evenend.Fill Evenend.Layout in
/-- 補題「貪欲な分割」を，行だけが並ぶ本文に当てはめる：Fillが返した各段の行をつなぐと元の
本文になり（行は失われず，順も変わらない），どの段も高さ`h`に入り切る． -/
theorem fill_lines {Note : Type} (τ b ls : Nat) (notes : Line → List Note)
    (noteHt : List Note → Nat) (cut : Nat → List Line → Nat) (h : Nat)
    (c0 : Nat → List Line → Nat) (As : List Nat) (text : List Line)
    (cols : List (List Line)) (m : Nat)
    (hf : fill (lineSpec τ b ls notes noteHt cut) h c0 As text = some (cols, m)) :
    cols.flatten = text ∧
    AllFit (lineSpec τ b ls notes noteHt cut) h As cols := by
  have hs := fill_spec _ h c0 As text cols m hf
  refine ⟨?_, hs.2.1⟩
  have hk : ∀ t : List Line, keep (lineSpec τ b ls notes noteHt cut) t = t := by
    intro t; simp [keep, lineSpec]
  have := hs.1
  rw [hk, hk] at this
  exact this

end Evenend.Link
