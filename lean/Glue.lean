/-
evenendパッケージの定式化の命題「段が揃うための条件」を確かめる．
TeXが高さを指定して垂直の箱を組むとき（\vbox to）のグルーの割り振りをモデルにする．
確かめ方：cd ~/lean/mathlib-ws && lake env lean <このファイルの絶対パス>
-/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Field.Rat

namespace Evenend.Glue

/-- 垂直リストの要素：箱（高さ），グルー（自然な長さ，伸び，縮み，無限に伸びるか）．
無限に伸びるグルーでは，`st`は無限の伸びの重み（\vfilなら1）． -/
inductive Node
  | box (h : ℚ)
  | glue (w st sh : ℚ) (fil : Bool)

/-- 自然な高さ -/
def nat : List Node → ℚ
  | [] => 0
  | .box h :: l => h + nat l
  | .glue w _ _ _ :: l => w + nat l

/-- 有限の伸びの和 -/
def finS : List Node → ℚ
  | [] => 0
  | .box _ :: l => finS l
  | .glue _ st _ f :: l => (if f then 0 else st) + finS l

/-- 無限の伸びの重みの和 -/
def filS : List Node → ℚ
  | [] => 0
  | .box _ :: l => filS l
  | .glue _ st _ f :: l => (if f then st else 0) + filS l

/-- 縮みの和 -/
def shr : List Node → ℚ
  | [] => 0
  | .box _ :: l => shr l
  | .glue _ _ sh _ :: l => sh + shr l

/-- 無限に伸びるグルーがあるか -/
def hasFil : List Node → Bool
  | [] => false
  | .box _ :: l => hasFil l
  | .glue _ _ _ f :: l => f || hasFil l

/-- グルーの割り振り方：そのまま，無限のグルーだけを比`r`で伸ばす，有限の伸びを比`r`で伸ばす，
比`r`で縮める． -/
inductive Mode
  | natural
  | fil (r : ℚ)
  | fin (r : ℚ)
  | shrink (r : ℚ)

/-- 割り振った後の高さ -/
def ht (m : Mode) : List Node → ℚ
  | [] => 0
  | .box h :: l => h + ht m l
  | .glue w st sh f :: l =>
    (match m with
      | .natural => w
      | .fil r => if f then w + r * st else w
      | .fin r => if f then w else w + r * st
      | .shrink r => w - r * sh) + ht m l

theorem ht_natural (l : List Node) : ht .natural l = nat l := by
  induction l with
  | nil => rfl
  | cons n l ih => cases n <;> simp [ht, nat, ih]

theorem ht_fil (r : ℚ) (l : List Node) : ht (.fil r) l = nat l + r * filS l := by
  induction l with
  | nil => simp [ht, nat, filS]
  | cons n l ih =>
    cases n with
    | box h => simp [ht, nat, filS, ih]; ring
    | glue w st sh f => cases f <;> simp [ht, nat, filS, ih] <;> ring

theorem ht_fin (r : ℚ) (l : List Node) : ht (.fin r) l = nat l + r * finS l := by
  induction l with
  | nil => simp [ht, nat, finS]
  | cons n l ih =>
    cases n with
    | box h => simp [ht, nat, finS, ih]; ring
    | glue w st sh f => cases f <;> simp [ht, nat, finS, ih] <;> ring

theorem ht_shrink (r : ℚ) (l : List Node) : ht (.shrink r) l = nat l - r * shr l := by
  induction l with
  | nil => simp [ht, nat, shr]
  | cons n l ih =>
    cases n with
    | box h => simp [ht, nat, shr, ih]; ring
    | glue w st sh f => simp [ht, nat, shr, ih]; ring

/-- TeXの規則：高さ`target`の箱に組むときの割り振り方．
足りないとき，無限に伸びるグルーがあればそれだけを伸ばし，なければ有限の伸びを伸ばす
（伸びの和が0なら伸ばせない）．余るとき，縮みの和が足りれば縮め，足りなければ縮みの
限度まで縮める． -/
def mode (target : ℚ) (l : List Node) : Mode :=
  if nat l ≤ target then
    if 0 < filS l then .fil ((target - nat l) / filS l)
    else if 0 < finS l then .fin ((target - nat l) / finS l)
    else .natural
  else
    if nat l - target ≤ shr l then .shrink ((nat l - target) / shr l)
    else .shrink 1

/-- 組んだ後の中身の高さ -/
def packed (target : ℚ) (l : List Node) : ℚ := ht (mode target l) l

/-- 足りないとき：無限に伸びるグルーがあるか，有限の伸びの和が正なら，中身は指定の高さになる． -/
theorem packed_stretch (target : ℚ) (l : List Node) (h : nat l ≤ target)
    (hs : 0 < filS l ∨ 0 < finS l) : packed target l = target := by
  unfold packed mode
  simp only [h, ite_true]
  by_cases hf : 0 < filS l
  · simp only [hf, ite_true, ht_fil]
    field_simp
    ring
  · rcases hs with hs | hs
    · exact absurd hs hf
    · simp only [hf, ite_false, hs, ite_true, ht_fin]
      field_simp
      ring

/-- 余るとき：縮みの和が超過以上なら，中身は指定の高さになる． -/
theorem packed_shrink (target : ℚ) (l : List Node) (h : target < nat l)
    (hs : nat l - target ≤ shr l) : packed target l = target := by
  have hpos : 0 < shr l := by linarith
  unfold packed mode
  simp only [not_le.mpr h, ite_false, hs, ite_true, ht_shrink]
  field_simp
  ring

/-- 無限に伸びるグルーのない並びは，無限のグルーだけを伸ばす割り振りで動かない． -/
theorem ht_fil_noFil (r : ℚ) (l : List Node) (h : hasFil l = false) : ht (.fil r) l = nat l := by
  induction l with
  | nil => rfl
  | cons n l ih =>
    cases n with
    | box b => simp [hasFil] at h; simp [ht, nat, ih h]
    | glue w st sh f =>
      simp [hasFil] at h
      simp [ht, nat, h.1, ih h.2]

theorem filS_noFil (l : List Node) (h : hasFil l = false) : filS l = 0 := by
  induction l with
  | nil => rfl
  | cons n l ih =>
    cases n with
    | box b => simp [hasFil] at h; simp [filS, ih h]
    | glue w st sh f =>
      simp [hasFil] at h
      simp [filS, h.1, ih h.2]

theorem nat_append (l₁ l₂ : List Node) : nat (l₁ ++ l₂) = nat l₁ + nat l₂ := by
  induction l₁ with
  | nil => simp [nat]
  | cons n l ih => cases n <;> simp [nat, ih] <;> ring

theorem filS_append (l₁ l₂ : List Node) : filS (l₁ ++ l₂) = filS l₁ + filS l₂ := by
  induction l₁ with
  | nil => simp [filS]
  | cons n l ih =>
    cases n with
    | box h => simp [filS, ih]
    | glue w st sh f => simp [filS, ih]; ring

theorem ht_append (m : Mode) (l₁ l₂ : List Node) : ht m (l₁ ++ l₂) = ht m l₁ + ht m l₂ := by
  induction l₁ with
  | nil => simp [ht]
  | cons n l ih => cases n <;> simp [ht, ih] <;> ring

/-- 手順5で入れる，無限に伸びるグルー（\vfil） -/
def vfil : Node := .glue 0 1 0 true

/-- 命題の(ii)，段の脚注や下のフロートで終わる段：本文`text`と，下端に付けるもの`bottom`の
間に\vfilを入れて高さ`target`に組むと，足りない分は\vfilが受け持つ．中身は指定の高さになり
（`bottom`が箱の下端に来る），本文は動かない． -/
theorem attach_bottom (target : ℚ) (text bottom : List Node)
    (ht_ : hasFil text = false) (hb : hasFil bottom = false)
    (h : nat text + nat bottom ≤ target) :
    packed target (text ++ vfil :: bottom) = target ∧
    ht (mode target (text ++ vfil :: bottom)) text = nat text := by
  have hn : nat (text ++ vfil :: bottom) = nat text + nat bottom := by
    simp [nat_append, nat, vfil]
  have hf : filS (text ++ vfil :: bottom) = 1 := by
    simp [filS_append, filS, vfil, filS_noFil text ht_, filS_noFil bottom hb]
  refine ⟨packed_stretch _ _ (by rw [hn]; exact h) (Or.inl (by rw [hf]; norm_num)), ?_⟩
  unfold mode
  simp only [hn, h, ite_true, hf]
  norm_num
  exact ht_fil_noFil _ text ht_

/-- 手順5の3（不足が半行を超える段）：本文の末尾に\vfilを入れると，本文は動かず，
最後の要素は箱の下端に届かない（下が空く）． -/
theorem ragged (target : ℚ) (text : List Node) (ht_ : hasFil text = false)
    (h : nat text ≤ target) :
    ht (mode target (text ++ [vfil])) text = nat text := by
  have := (attach_bottom target text [] ht_ rfl (by simpa [nat] using h)).2
  simpa using this

/-- 命題の(ii)，どちらでもない段：段が最後の要素で終わり（並び全体を組む），有限の伸びの
和が正なら，中身は指定の高さになる．最後の要素は並びの末尾なので，箱の下端に来る． -/
theorem stretch_finite (target : ℚ) (l : List Node) (h : nat l ≤ target) (hs : 0 < finS l) :
    packed target l = target :=
  packed_stretch target l h (Or.inr hs)

end Evenend.Glue
