/-
evenendパッケージの定式化の命題「揃えた配置の構成」の手順4の判定（揃わない配分）を確かめる．
確かめ方：cd ~/lean/mathlib-ws && lake env lean <このファイルの絶対パス>
-/
namespace Evenend.Misaligned

/-- 段：見かけの下端`v`，フロートまわりのグルーの縮み`shr`，本文だけの段か，本文があるか，
中身（本文かフロート）があるか -/
structure Col where
  v : Nat
  shr : Nat
  textOnly : Bool
  hasText : Bool
  content : Bool

/-- 見かけの下端の最大 -/
def mx : List Col → Nat
  | [] => 0
  | c :: cs => max c.v (mx cs)

/-- 本文だけの段の見かけの下端の最大β_T（本文だけの段がなければ`none`） -/
def tv : List Col → Option Nat
  | [] => none
  | c :: cs =>
    if c.textOnly then
      match tv cs with
      | some t => some (max c.v t)
      | none => some c.v
    else tv cs

/-- (b)：後ろに中身のある途中の段で，本文があり，β_Tより半行を超えて短いものがあるか．
`init`は最右段より前の段，`last`は最右段，`b`は行送り． -/
def anyShort (b t : Nat) (last : Col) : List Col → Bool
  | [] => false
  | c :: cs =>
    ((cs.any (·.content) || last.content) && c.hasText && decide (2 * c.v + b < 2 * t))
      || anyShort b t last cs

/-- 揃わない配分か（手順4の(a)，(b)，(c)） -/
def mis (b : Nat) (init : List Col) (last : Col) : Bool :=
  decide (mx init < last.v) ||
  (match tv init with
    | some t => anyShort b t last init || (init ++ [last]).any (fun c => decide (t < c.v - c.shr))
    | none => false)

/-- 判定を通れば，最右段はほかのどの段よりも高くはない（(a)の否定）． -/
theorem last_le (b : Nat) (init : List Col) (last : Col) (h : mis b init last = false) :
    last.v ≤ mx init := by
  simp only [mis, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
  omega

/-- 判定を通り，本文だけの段があれば，どの段もグルーを縮めてβ_T以下に収まる（(c)の否定）．
このとき手順5は，下端をβ_Tにする． -/
theorem shrinks_to (b : Nat) (init : List Col) (last : Col) (t : Nat)
    (h : mis b init last = false) (ht : tv init = some t) :
    ∀ c ∈ init ++ [last], c.v - c.shr ≤ t := by
  simp only [mis, ht, Bool.or_eq_false_iff] at h
  have hc := h.2.2
  intro c hmem
  have := List.all_eq_true.mp (by simpa [List.any_eq_false] using hc : (init ++ [last]).all (fun c => !decide (t < c.v - c.shr)) = true) c hmem
  simp at this
  omega

theorem anyShort_false (b t : Nat) (last : Col) :
    ∀ (init pre post : List Col) (c : Col), anyShort b t last init = false →
      init = pre ++ c :: post → (post.any (·.content) || last.content) = true →
      c.hasText = true → 2 * (t - c.v) ≤ b := by
  intro init
  induction init with
  | nil => intro pre post c _ he; simp at he
  | cons x xs ih =>
    intro pre post c h he hl hx
    simp only [anyShort, Bool.or_eq_false_iff] at h
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have h1 := h.1
      simp only [hl, hx, Bool.true_and, decide_eq_false_iff_not] at h1
      omega
    | cons p ps =>
      simp only [List.cons_append, List.cons.injEq] at he
      exact ih ps post c h.2 he.2 hl hx

/-- 判定を通り，本文だけの段があれば，後ろに中身のある途中の段（本文のあるもの）の不足は，
半行以下である（(b)の否定）．命題「段が揃うための条件」の(ii)の(a)が成り立つ． -/
theorem deficit_le (b : Nat) (init pre post : List Col) (last c : Col) (t : Nat)
    (h : mis b init last = false) (ht : tv init = some t)
    (he : init = pre ++ c :: post) (hl : (post.any (·.content) || last.content) = true)
    (hx : c.hasText = true) : 2 * (t - c.v) ≤ b := by
  simp only [mis, ht, Bool.or_eq_false_iff] at h
  exact anyShort_false b t last init pre post c h.2.1 he hl hx

end Evenend.Misaligned
