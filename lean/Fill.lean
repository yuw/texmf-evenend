/-
evenendパッケージの定式化の補題「貪欲な分割」（Fill）を確かめる．
本文は要素の並び`List Item`で，`\vsplit`などは次の仕様`Spec`を満たす任意の関数とする．
段の先頭で捨てられる要素（グルーなど）は，このモデルでは扱わない．
確かめ方：cd ~/lean/mathlib-ws && lake env lean <このファイルの絶対パス>
-/
namespace Evenend.Fill

/-- 本文の高さ`ht`，その本文に参照位置のある脚注の高さ`G`，`\vsplit`にあたる`split`．
`split c t`は，`t`を前と後ろに分ける（順を変えず，何も失わない）．高さ`c`以下に切ることは
仮定しない（手順が切った後で高さを確かめるので，性質の証明には要らない）． -/
structure Spec (Item : Type) where
  ht : List Item → Nat
  G : List Item → Nat
  split : Nat → List Item → List Item × List Item
  split_append : ∀ c t, (split c t).1 ++ (split c t).2 = t

variable {Item : Type} (S : Spec Item) (h : Nat)

/-- 段が高さ`h`に入り切る：フロートの高さ`A`，本文`t`，脚注の和が`h`以下． -/
def Fits (A : Nat) (t : List Item) : Prop := A + S.ht t + S.G t ≤ h

instance (A : Nat) (t : List Item) : Decidable (Fits S h A t) := by
  unfold Fits; infer_instance

/-- 途中の段の切り出し（手順1から4）．高さ`c`で切り，入り切らなければ超えた分だけ`c`を
小さくしてやり直す．`fuel`は回数の上限．返すのは（段の本文，残りの本文，`\vsplit`の回数）． -/
def fillCol (A : Nat) : Nat → Nat → List Item → Option (List Item × List Item × Nat)
  | 0, _, _ => none
  | fuel + 1, c, rest =>
    let p := S.split c rest
    if Fits S h A p.1 then some (p.1, p.2, 1)
    else
      match fillCol A fuel (c - (A + S.ht p.1 + S.G p.1 - h)) rest with
      | none => none
      | some (t, r, n) => some (t, r, n + 1)

theorem fillCol_spec (A : Nat) :
    ∀ (fuel c : Nat) (rest t r : List Item) (n : Nat),
      fillCol S h A fuel c rest = some (t, r, n) →
      t ++ r = rest ∧ Fits S h A t ∧ n ≤ fuel := by
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
      exact ⟨S.split_append c rest, hfit, by omega⟩
    · split at hf
      · simp at hf
      · rename_i t' r' n' heq
        simp only [Option.some.injEq, Prod.mk.injEq] at hf
        obtain ⟨rfl, rfl, rfl⟩ := hf
        have := ih _ rest t' r' n' heq
        exact ⟨this.1, this.2.1, by omega⟩

/-- 段ごとに入り切る：フロートの高さの並び`As`と段の本文の並び`cols`が同じ長さで，
対応する段がどれも高さ`h`に入り切る． -/
inductive AllFit : List Nat → List (List Item) → Prop
  | nil : AllFit [] []
  | cons {a : Nat} {t : List Item} {as : List Nat} {ts : List (List Item)} :
      Fits S h a t → AllFit as ts → AllFit (a :: as) (t :: ts)

/-- 手順Fill．`As`は各段のフロートの高さ（割り振りσで決まる）．最後の段は残りの本文の
すべてを取る．`c0`は切り出しの初めの高さ（何でもよい）．返すのは（各段の本文，`\vsplit`の回数）． -/
def fill (c0 : Nat → List Item → Nat) : List Nat → List Item → Option (List (List Item) × Nat)
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
(P2) 各段の本文を順につなぐと元の本文になる（読む順のまま，何も失わない），
(P1) どの段も高さ`h`に入り切る，
`\vsplit`の回数は高々`10(N - 1)`である． -/
theorem fill_spec (c0 : Nat → List Item → Nat) :
    ∀ (As : List Nat) (rest : List Item) (cols : List (List Item)) (m : Nat),
      fill S h c0 As rest = some (cols, m) →
      cols.flatten = rest ∧ AllFit S h As cols ∧ m ≤ 10 * (As.length - 1) := by
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
          · rw [List.flatten_cons, hr.1, hc.1]
          · have := hc.2.2
            have := hr.2.2
            simp only [List.length_cons] at *
            omega

end Evenend.Fill
