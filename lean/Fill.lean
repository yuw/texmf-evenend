/-
evenendパッケージの定式化の補題「貪欲な分割」（Fill）を確かめる．
本文は要素の並び`List Item`で，`\vsplit`などは次の仕様`Spec`を満たす任意の関数とする．
仕様は，実装に入れた検査（evenend.luaのMC.split）で，組むたびに確かめている．
確かめ方：cd ~/lean/mathlib-ws && lake env lean <このファイルの絶対パス>
-/
namespace Evenend.Fill

/-- 本文と脚注のモデル．
`ht`は本文の高さ，`disc`は捨てられる要素（グルーなど）か，`notes`は要素に参照位置のある脚注，
`noteHt`は脚注の並びを積んだ高さ（footnote=pageではつねに0とする），`split`は`\vsplit`．
`split c t`は，`t`を（切り出した本文，残りの本文）に分ける．捨てられる要素のほかは，順を変えず，
何も失わない（`\vsplit`は，切れ目から残りの最初の箱までにある捨てられる要素を捨てる．その間に
ある捨てられない要素は残す）．捨てられる要素に脚注の参照位置はない．
高さ`c`以下に切ることは仮定しない（手順が切った後で高さを確かめるので，性質の証明には要らない）． -/
structure Spec (Item Note : Type) where
  ht : List Item → Nat
  disc : Item → Bool
  notes : Item → List Note
  noteHt : List Note → Nat
  split : Nat → List Item → List Item × List Item
  split_keep : ∀ c t, ((split c t).1 ++ (split c t).2).filter (fun x => !disc x)
    = t.filter (fun x => !disc x)
  disc_notes : ∀ x, disc x = true → notes x = []

variable {Item Note : Type} (S : Spec Item Note) (h : Nat)

/-- 捨てられる要素を除いた並び -/
def keep (t : List Item) : List Item := t.filter (fun x => !S.disc x)

theorem keep_append (t₁ t₂ : List Item) : keep S (t₁ ++ t₂) = keep S t₁ ++ keep S t₂ := by
  simp [keep, List.filter_append]

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
返すのは（段の本文，残りの本文，`\vsplit`の回数）． -/
def fillCol (A : Nat) :
    Nat → Nat → List Item → Option (List Item × List Item × Nat)
  | 0, _, _ => none
  | fuel + 1, c, rest =>
    let p := S.split c rest
    if Fits S h A p.1 then some (p.1, p.2, 1)
    else
      match fillCol A fuel (c - (A + S.ht p.1 + G S p.1 - h)) rest with
      | none => none
      | some (t, r, n) => some (t, r, n + 1)

theorem fillCol_spec (A : Nat) :
    ∀ (fuel c : Nat) (rest t r : List Item) (n : Nat),
      fillCol S h A fuel c rest = some (t, r, n) →
      keep S (t ++ r) = keep S rest ∧ Fits S h A t ∧ n ≤ fuel := by
  intro fuel
  induction fuel with
  | zero => intro c rest t r n hf; simp [fillCol] at hf
  | succ k ih =>
    intro c rest t r n hf
    unfold fillCol at hf
    simp only at hf
    split at hf
    · rename_i hfit
      simp only [Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl, rfl⟩ := hf
      exact ⟨S.split_keep c rest, hfit, by omega⟩
    · split at hf
      · simp at hf
      · rename_i t' r' n' heq
        simp only [Option.some.injEq, Prod.mk.injEq] at hf
        obtain ⟨rfl, rfl, rfl⟩ := hf
        have := ih _ rest t' r' n' heq
        exact ⟨this.1, this.2.1, by omega⟩

/-- 段ごとに入り切る：フロートの高さの並び`As`と段の並び`cols`が同じ長さで，対応する段の
本文がどれも高さ`h`に入り切る． -/
inductive AllFit : List Nat → List (List Item) → Prop
  | nil : AllFit [] []
  | cons {a : Nat} {t : List Item} {as : List Nat} {ts : List (List Item)} :
      Fits S h a t → AllFit as ts → AllFit (a :: as) (t :: ts)

/-- 手順Fill．`As`は各段のフロートの高さ（定式化の文書の|F_i|．割り振りσで決まる）．最後の段は残りの本文の
すべてを取る．`c0`は切り出しの初めの高さ（何でもよい）．
返すのは（各段の本文，`\vsplit`の回数）． -/
def fill (c0 : Nat → List Item → Nat) :
    List Nat → List Item → Option (List (List Item) × Nat)
  | [], _ => none
  | [a], rest => if Fits S h a rest then some ([rest], 0) else none
  | a :: a' :: as, rest =>
    match fillCol S h a 10 (c0 a rest) rest with
    | none => none
    | some (t, r, n) =>
      match fill c0 (a' :: as) r with
      | none => none
      | some (cols, m) => some (t :: cols, n + m)

/-- 補題：Fillが配置を返したとき，
(P2) 各段の本文を順につなぐと，捨てられる要素のほかは，元の本文と同じ並びになる（読む順の
まま，何も失わない），
(P1) どの段も高さ`h`に入り切る，
`\vsplit`の回数は高々`10(N - 1)`である． -/
theorem fill_spec (c0 : Nat → List Item → Nat) :
    ∀ (As : List Nat) (rest : List Item) (cols : List (List Item)) (m : Nat),
      fill S h c0 As rest = some (cols, m) →
      keep S cols.flatten = keep S rest ∧
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
        refine ⟨by simp, ?_, by simp⟩
        exact AllFit.cons hfit AllFit.nil
      · simp at hf
    | cons a' as' =>
      simp only [fill] at hf
      split at hf
      · simp at hf
      · rename_i t r n hcol
        split at hf
        · simp at hf
        · rename_i cols' m' hrest
          simp only [Option.some.injEq, Prod.mk.injEq] at hf
          obtain ⟨rfl, rfl⟩ := hf
          have hc := fillCol_spec S h a 10 (c0 a rest) rest t r n hcol
          have hr := ih r cols' m' hrest
          refine ⟨?_, AllFit.cons hc.2.1 hr.2.1, ?_⟩
          · rw [List.flatten_cons, keep_append, hr.1, ← keep_append]
            exact hc.1
          · have := hc.2.2
            have := hr.2.2
            simp only [List.length_cons] at *
            omega

theorem notesOf_append (t₁ t₂ : List Item) :
    notesOf S (t₁ ++ t₂) = notesOf S t₁ ++ notesOf S t₂ := by
  simp [notesOf, List.flatMap_append]

/-- 捨てられる要素を除いても，脚注の並びは変わらない． -/
theorem notesOf_keep (t : List Item) : notesOf S (keep S t) = notesOf S t := by
  induction t with
  | nil => rfl
  | cons x xs ih =>
    simp only [notesOf, keep] at ih ⊢
    cases hx : S.disc x with
    | true =>
      have hn : S.notes x = [] := S.disc_notes x hx
      simp [hx, List.flatMap_cons, hn, ih]
    | false =>
      simp [hx, List.flatMap_cons, ih]

theorem notesOf_flatten (cs : List (List Item)) :
    notesOf S cs.flatten = cs.flatMap (notesOf S) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [List.flatten_cons, notesOf_append, ih, List.flatMap_cons]

/-- (P3)，footnote=column：どの脚注も，参照位置のある本文と同じ段に，ちょうど1回，読む順のまま
置かれる．各段の本文に参照位置のある脚注を段の順につなぐと，本文全体の脚注の並びになる． -/
theorem fill_notes (c0 : Nat → List Item → Nat) (As : List Nat) (rest : List Item)
    (cols : List (List Item)) (m : Nat)
    (hf : fill S h c0 As rest = some (cols, m)) :
    cols.flatMap (notesOf S) = notesOf S rest := by
  have hs := fill_spec S h c0 As rest cols m hf
  rw [← notesOf_flatten, ← notesOf_keep, hs.1, notesOf_keep]

/-- (P3)，footnote=page：段の高さ`h`を，版面の高さ`Hfull`からページの脚注の領域`Ψ`を引いた
高さ以下にしておけば，入り切る段は脚注の領域に掛からない． -/
theorem page_region (Hfull Ψ A : Nat) (t : List Item) (hfit : Fits S h A t) (hh : h + Ψ ≤ Hfull) :
    A + S.ht t + G S t + Ψ ≤ Hfull := by
  unfold Fits at hfit
  omega

end Evenend.Fill
