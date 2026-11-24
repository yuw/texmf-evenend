/-
evenendパッケージの定式化の命題「揃えた配置の構成」の(i)を，手順の全体（Balance.lean）の
Fillに補題の手順（Fill.lean）を代入して確かめる．
確かめ方：lean/check.sh
-/
import Fill
import Balance

namespace Evenend.Whole

open Evenend.Fill Evenend.Balance

/-
`Sp`は本文と脚注のモデル（Fill.lean），`c0`は切り出しの初めの高さ，`text`は本文．
`Sg`は割り振りσの型，`As k σ`は緩め方`k`と割り振り`σ`での各段のフロートの高さの並び．
脚注の高さの測り方は緩め方で変わるので，モデルも緩め方ごとに与える（`Sp k`）．
-/
variable {Item Note Sg : Type} (Sp : Nat → Spec Item Note) (c0 : Nat → List Item → Nat)
  (As : Nat → Sg → List Nat) (mu h0 : Sg → Nat) (aligned : Sg → Nat → Bool) (H g : Nat)
  (text : List Item)

/-- 緩め方`k`，割り振り`σ`，高さ`h`でのFill． -/
def fillK (k : Nat) (σ : Sg) (h : Nat) : Option (List (List Item) × Nat) :=
  fill (Sp k) h c0 (As k σ) text

/-- 命題の(i)：手順の全体が配置を返したとき，割り振り`σ`は候補のどれかで，高さ`h`は`H`以下で
あり，ある緩め方`k < 3`について，
(P2) 各段の本文を順につなぐと，捨てられる要素のほかは，元の本文と同じ並びになる，
(P1) どの段も（緩め方`k`の所要の高さで）高さ`h`に入り切る，
(P3) どの脚注も，参照位置のある本文と同じ段に，ちょうど1回，読む順のまま置かれる，
`\vsplit`の回数は高々`10(N - 1)`である． -/
theorem whole_spec (σs : List Sg) (σ : Sg) (h : Nat)
    (cols : List (List Item)) (m : Nat)
    (hp : procedure mu h0 aligned H g (fillK Sp c0 As text) σs = some (σ, h, (cols, m))) :
    σ ∈ σs ∧ h ≤ H ∧ ∃ k, k < 3 ∧
      keep (Sp k) cols.flatten = keep (Sp k) text ∧
      AllFit (Sp k) h (As k σ) cols ∧
      cols.flatMap (notesOf (Sp k)) = notesOf (Sp k) text ∧
      m ≤ 10 * ((As k σ).length - 1) := by
  refine procedure_spec mu h0 aligned H g (fillK Sp c0 As text) σs
    (fun k σ h l =>
      keep (Sp k) l.1.flatten = keep (Sp k) text ∧
      AllFit (Sp k) h (As k σ) l.1 ∧
      l.1.flatMap (notesOf (Sp k)) = notesOf (Sp k) text ∧
      l.2 ≤ 10 * ((As k σ).length - 1)) ?_ σ h (cols, m) hp
  intro k σ h l hl
  obtain ⟨cols', m'⟩ := l
  have hs := fill_spec (Sp k) h c0 (As k σ) text cols' m' hl
  have hn := fill_notes (Sp k) h c0 (As k σ) text cols' m' hl
  exact ⟨hs.1, hs.2.1, hn, hs.2.2⟩

/-- 「揃えられない」と答えるのは，3つの緩め方のどれでも，どの候補でも，高さ`H`でのFillが
失敗するときだけである． -/
theorem whole_none (σs : List Sg)
    (hp : procedure mu h0 aligned H g (fillK Sp c0 As text) σs = none) :
    ∀ k, k < 3 → ∀ σ ∈ σs, fill (Sp k) H c0 (As k σ) text = none :=
  procedure_none mu h0 aligned H g (fillK Sp c0 As text) σs hp

end Evenend.Whole
