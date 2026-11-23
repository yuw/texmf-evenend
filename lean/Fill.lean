/-
evenendパッケージの定式化の補題「貪欲な分割」（Fill）を確かめる．
本文は要素の並び`List Item`で，`\vsplit`などは次の仕様`Spec`を満たす任意の関数とする．
確かめ方：cd ~/lean/mathlib-ws && lake env lean <このファイルの絶対パス>
-/
namespace Evenend.Fill

/-- 本文と脚注のモデル．
`ht`は本文の高さ，`disc`は捨てられる要素（グルーなど）か，`notes`は要素に参照位置のある脚注，
`noteHt`は脚注の並びを積んだ高さ（footnote=pageではつねに0とする），`split`は`\vsplit`．
`split c t`は，`t`を（切り出した本文，切れ目で捨てる要素，残りの本文）に分ける．順を変えず，
捨てるのは捨てられる要素だけである．捨てられる要素に脚注の参照位置はない．
高さ`c`以下に切ることは仮定しない（手順が切った後で高さを確かめるので，性質の証明には要らない）． -/
structure Spec (Item Note : Type) where
  ht : List Item → Nat
  disc : Item → Bool
  notes : Item → List Note
  noteHt : List Note → Nat
  split : Nat → List Item → List Item × List Item × List Item
  split_append : ∀ c t, (split c t).1 ++ (split c t).2.1 ++ (split c t).2.2 = t
  split_drop : ∀ c t, ∀ x ∈ (split c t).2.1, disc x = true
  disc_notes : ∀ x, disc x = true → notes x = []

variable {Item Note : Type} (S : Spec Item Note) (h : Nat)

/-- 本文`t`に参照位置のある脚注（読む順） -/
def notesOf (t : List Item) : List Note := t.flatMap S.notes

/-- 脚注の高さ G -/
def G (t : List Item) : Nat := S.noteHt (notesOf S t)

/-- 段が高さ`h`に入り切る：フロートの高さ`A`，本文`t`，脚注の和が`h`以下． -/
def Fits (A : Nat) (t : List Item) : Prop := A + S.ht t + G S t ≤ h

instance (A : Nat) (t : List Item) : Decidable (Fits S h A t) := by
  unfold Fits; infer_instance

/-- 途中の段の切り出し（手順1から4）．高さ`c`で切り，入り切らなければ超えた分だけ`c`を
小さくしてやり直す．`fuel`は回数の上限．
返すのは（段の本文，捨てた要素，残りの本文，`\vsplit`の回数）． -/
def fillCol (A : Nat) :
    Nat → Nat → List Item → Option (List Item × List Item × List Item × Nat)
  | 0, _, _ => none
  | fuel + 1, c, rest =>
    let p := S.split c rest
    if Fits S h A p.1 then some (p.1, p.2.1, p.2.2, 1)
    else
      match fillCol A fuel (c - (A + S.ht p.1 + G S p.1 - h)) rest with
      | none => none
      | some (t, d, r, n) => some (t, d, r, n + 1)

theorem fillCol_spec (A : Nat) :
    ∀ (fuel c : Nat) (rest t d r : List Item) (n : Nat),
      fillCol S h A fuel c rest = some (t, d, r, n) →
      t ++ d ++ r = rest ∧ (∀ x ∈ d, S.disc x = true) ∧ Fits S h A t ∧ n ≤ fuel := by
  intro fuel
  induction fuel with
  | zero => intro c rest t d r n hf; simp [fillCol] at hf
  | succ k ih =>
    intro c rest t d r n hf
    unfold fillCol at hf
    simp only at hf
    split at hf
    · rename_i hfit
      simp only [Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hf
      exact ⟨S.split_append c rest, S.split_drop c rest, hfit, by omega⟩
    · split at hf
      · simp at hf
      · rename_i t' d' r' n' heq
        simp only [Option.some.injEq, Prod.mk.injEq] at hf
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hf
        have := ih _ rest t' d' r' n' heq
        exact ⟨this.1, this.2.1, this.2.2.1, by omega⟩

/-- 段ごとに入り切る：フロートの高さの並び`As`と段の並び`cols`が同じ長さで，対応する段の
本文がどれも高さ`h`に入り切る．段は（本文，その後ろで捨てた要素）の組． -/
inductive AllFit : List Nat → List (List Item × List Item) → Prop
  | nil : AllFit [] []
  | cons {a : Nat} {p : List Item × List Item} {as : List Nat} {ps : List (List Item × List Item)} :
      Fits S h a p.1 → AllFit as ps → AllFit (a :: as) (p :: ps)

/-- 手順Fill．`As`は各段のフロートの高さ（割り振りσで決まる）．最後の段は残りの本文の
すべてを取る．`c0`は切り出しの初めの高さ（何でもよい）．
返すのは（各段の（本文，捨てた要素），`\vsplit`の回数）． -/
def fill (c0 : Nat → List Item → Nat) :
    List Nat → List Item → Option (List (List Item × List Item) × Nat)
  | [], _ => none
  | [a], rest => if Fits S h a rest then some ([(rest, [])], 0) else none
  | a :: a' :: as, rest =>
    match fillCol S h a 10 (c0 a rest) rest with
    | none => none
    | some (t, d, r, n) =>
      match fill c0 (a' :: as) r with
      | none => none
      | some (cols, m) => some ((t, d) :: cols, n + m)

/-- 補題：Fillが配置を返したとき，
(P2) 各段の本文と捨てた要素を順につなぐと元の本文になる（読む順のまま，何も失わない），
捨てたのは捨てられる要素だけである，
(P1) どの段も高さ`h`に入り切る，
`\vsplit`の回数は高々`10(N - 1)`である． -/
theorem fill_spec (c0 : Nat → List Item → Nat) :
    ∀ (As : List Nat) (rest : List Item) (cols : List (List Item × List Item)) (m : Nat),
      fill S h c0 As rest = some (cols, m) →
      cols.flatMap (fun p => p.1 ++ p.2) = rest ∧
      (∀ p ∈ cols, ∀ x ∈ p.2, S.disc x = true) ∧
      AllFit S h As cols ∧ m ≤ 10 * (As.length - 1) := by
  intro As
  induction As with
  | nil => intro rest cols m hf; simp [fill] at hf
  | cons a as ih =>
    intro rest cols m hf
    cases as with
    | nil =>
      simp only [fill] at hf
      split at hf
      · rename_i hfit
        simp only [Option.some.injEq, Prod.mk.injEq] at hf
        obtain ⟨rfl, rfl⟩ := hf
        refine ⟨by simp, by simp, ?_, by simp⟩
        exact AllFit.cons hfit AllFit.nil
      · simp at hf
    | cons a' as' =>
      simp only [fill] at hf
      split at hf
      · simp at hf
      · rename_i t d r n hcol
        split at hf
        · simp at hf
        · rename_i cols' m' hrest
          simp only [Option.some.injEq, Prod.mk.injEq] at hf
          obtain ⟨rfl, rfl⟩ := hf
          have hc := fillCol_spec S h a 10 (c0 a rest) rest t d r n hcol
          have hr := ih r cols' m' hrest
          refine ⟨?_, ?_, AllFit.cons hc.2.2.1 hr.2.2.1, ?_⟩
          · rw [List.flatMap_cons, hr.1]
            exact hc.1
          · intro p hp
            simp only [List.mem_cons] at hp
            rcases hp with rfl | hp
            · exact hc.2.1
            · exact hr.2.1 p hp
          · have := hc.2.2.2
            have := hr.2.2.2
            simp only [List.length_cons] at *
            omega

theorem notesOf_append (t₁ t₂ : List Item) :
    notesOf S (t₁ ++ t₂) = notesOf S t₁ ++ notesOf S t₂ := by
  simp [notesOf, List.flatMap_append]

theorem notesOf_disc (d : List Item) (hd : ∀ x ∈ d, S.disc x = true) : notesOf S d = [] := by
  induction d with
  | nil => rfl
  | cons x xs ih =>
    have hx : S.notes x = [] := S.disc_notes x (hd x (by simp))
    have hxs : notesOf S xs = [] := ih (fun y hy => hd y (by simp [hy]))
    simp only [notesOf] at hxs ⊢
    simp [List.flatMap_cons, hx, hxs]

/-- (P3)，footnote=column：どの脚注も，参照位置のある本文と同じ段に，ちょうど1回，読む順のまま
置かれる．各段の本文に参照位置のある脚注を段の順につなぐと，本文全体の脚注の並びになる． -/
theorem fill_notes (c0 : Nat → List Item → Nat) (As : List Nat) (rest : List Item)
    (cols : List (List Item × List Item)) (m : Nat)
    (hf : fill S h c0 As rest = some (cols, m)) :
    cols.flatMap (fun p => notesOf S p.1) = notesOf S rest := by
  have hs := fill_spec S h c0 As rest cols m hf
  have key : ∀ (cs : List (List Item × List Item)),
      (∀ p ∈ cs, ∀ x ∈ p.2, S.disc x = true) →
      cs.flatMap (fun p => notesOf S p.1) = notesOf S (cs.flatMap (fun p => p.1 ++ p.2)) := by
    intro cs
    induction cs with
    | nil => intro _; rfl
    | cons p ps ih =>
      intro hd
      have hp : notesOf S p.2 = [] := notesOf_disc S p.2 (hd p (by simp))
      have hps := ih (fun q hq => hd q (by simp [hq]))
      rw [List.flatMap_cons, List.flatMap_cons, notesOf_append, notesOf_append, hp, hps]
      simp
  rw [key cols hs.2.1, hs.1]

/-- (P3)，footnote=page：段の高さ`h`を，版面の高さ`Hfull`からページの脚注の領域`Ψ`を引いた
高さ以下にしておけば，入り切る段は脚注の領域に掛からない． -/
theorem page_region (Hfull Ψ A : Nat) (t : List Item) (hfit : Fits S h A t) (hh : h + Ψ ≤ Hfull) :
    A + S.ht t + G S t + Ψ ≤ Hfull := by
  unfold Fits at hfit
  omega

end Evenend.Fill
