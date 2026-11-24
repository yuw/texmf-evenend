/-
evenendパッケージの定式化の命題「揃えた配置の構成」の手順5で，各段の並びを作る部分を確かめる．
できた並びを箱に組むところは，Glue.leanの定義と定理を使う．
確かめ方：lean/check.sh
-/
import Glue

namespace Evenend.Column

open Evenend.Glue

/-- 段の材料．`top`は上のフロート（下のアキを含む），`body`は本文，`bot`は下のフロート
（上のアキを含む），`foot`は段の脚注． -/
structure Parts where
  top : List Node
  body : List Node
  bot : List Node
  foot : List Node

/-- 材料に，無限に伸びるグルーがない． -/
def NoFil (p : Parts) : Prop :=
  hasFil p.top = false ∧ hasFil p.body = false ∧ hasFil p.bot = false ∧ hasFil p.foot = false

def opt (b : Bool) : List Node := if b then [vfil] else []

/-- 段の並び．上のフロート，本文，下のフロート，脚注の順に積む．`a`が真なら本文の後に，
`a`が偽で`b`が真なら下のフロートの前に，\vfilを入れる（\vfilは高々1つ）． -/
def build (p : Parts) (a b : Bool) : List Node :=
  p.top ++ p.body ++ opt (a || b) ++ p.bot ++ p.foot

/-- \vfilのない並びの自然な高さ -/
def natAll (p : Parts) : ℚ := nat p.top + nat p.body + nat p.bot + nat p.foot

/-- \vfilを入れる所を決める（手順5の1から3）．`target`は箱の高さ，`half`は半行，
`mid`は「段Lか，次の段に中身のある途中の段」．
`a`：段の脚注があるか，`mid`で不足が半行を超える．
`b`：下のフロートがあり，有限の伸びを足しても箱の高さに届かない． -/
def chooseA (p : Parts) (target half : ℚ) (mid : Bool) : Bool :=
  !p.foot.isEmpty || (mid && decide (half < target - natAll p))

def chooseB (p : Parts) (target : ℚ) : Bool :=
  !p.bot.isEmpty && decide (natAll p + finS (build p false false) < target)

theorem nat_opt (b : Bool) : nat (opt b) = 0 := by cases b <;> simp [opt, nat, vfil]

theorem filS_opt (b : Bool) : filS (opt b) = if b then 1 else 0 := by
  cases b <;> simp [opt, filS, vfil]

theorem hasFil_append (l₁ l₂ : List Node) : hasFil (l₁ ++ l₂) = (hasFil l₁ || hasFil l₂) := by
  induction l₁ with
  | nil => simp [hasFil]
  | cons n l ih => cases n <;> simp [hasFil, ih, Bool.or_assoc]

/-- \vfilは自然な高さを変えない． -/
theorem nat_build (p : Parts) (a b : Bool) : nat (build p a b) = natAll p := by
  simp only [build, nat_append, nat_opt, natAll]
  ring

theorem filS_build (p : Parts) (a b : Bool) (hn : NoFil p) :
    filS (build p a b) = if (a || b) then 1 else 0 := by
  simp only [build, filS_append, filS_opt, filS_noFil _ hn.1, filS_noFil _ hn.2.1,
    filS_noFil _ hn.2.2.1, filS_noFil _ hn.2.2.2]
  ring

/-- \vfilを入れた段：中身は箱の高さちょうどになる．上のフロートと本文は自然な高さのまま
（本文の行は動かない），下のフロートと脚注も自然な高さのままである．下のフロートと脚注は
並びの末尾にあるので，箱の下端に付く．足りない分は，\vfilの所が空く． -/
theorem build_fil (target : ℚ) (p : Parts) (a b : Bool) (hn : NoFil p) (hab : (a || b) = true)
    (h : natAll p ≤ target) :
    packed target (build p a b) = target ∧
    ht (mode target (build p a b)) (p.top ++ p.body) = nat p.top + nat p.body ∧
    ht (mode target (build p a b)) (p.bot ++ p.foot) = nat p.bot + nat p.foot := by
  have hf : filS (build p a b) = 1 := by rw [filS_build p a b hn, hab]; rfl
  have hnat : nat (build p a b) ≤ target := by rw [nat_build]; exact h
  have hm : mode target (build p a b) = .fil ((target - nat (build p a b)) / filS (build p a b)) := by
    unfold mode
    simp only [hnat, ite_true, hf]
    norm_num
  refine ⟨packed_stretch _ _ hnat (Or.inl (by rw [hf]; norm_num)), ?_, ?_⟩
  · rw [hm, ht_fil_noFil _ _ (by rw [hasFil_append, hn.1, hn.2.1]; rfl), nat_append]
  · rw [hm, ht_fil_noFil _ _ (by rw [hasFil_append, hn.2.2.1, hn.2.2.2]; rfl), nat_append]

/-- \vfilを入れない段：並びは材料を順に積んだだけで，最後の要素で終わる．有限の伸びの和が
不足以上なら（`chooseB`が偽で，下のフロートがある段はこれに当たる），中身は箱の高さに届く． -/
theorem build_plain (target : ℚ) (p : Parts) (h : natAll p ≤ target)
    (hs : 0 < finS (build p false false)) :
    build p false false = p.top ++ p.body ++ p.bot ++ p.foot ∧
    packed target (build p false false) = target := by
  refine ⟨by simp [build, opt], ?_⟩
  exact stretch_finite target _ (by rw [nat_build]; exact h) hs

/-- 段の脚注のある段には，必ず\vfilが入る（手順5の1）． -/
theorem chooseA_foot (p : Parts) (target half : ℚ) (mid : Bool) (hf : p.foot ≠ []) :
    chooseA p target half mid = true := by
  cases hp : p.foot with
  | nil => exact absurd hp hf
  | cons x xs => simp [chooseA, hp]

/-- 本文だけの段で，`mid`でないか不足が半行以下なら，\vfilは入らない（グルーを伸ばして揃える）． -/
theorem choose_none (p : Parts) (target half : ℚ) (mid : Bool) (hf : p.foot = []) (hb : p.bot = [])
    (hm : mid = false ∨ target - natAll p ≤ half) :
    (chooseA p target half mid || chooseB p target) = false := by
  have h1 : chooseB p target = false := by simp [chooseB, hb]
  have h2 : chooseA p target half mid = false := by
    rcases hm with hm | hm
    · simp [chooseA, hf, hm]
    · simp [chooseA, hf, not_lt.mpr hm]
  rw [h1, h2]; rfl

end Evenend.Column
