/-
evenendパッケージの定式化の命題「揃えた配置の構成」の手順1で，段をまたぐフロートが重なる
候補を除く判定を確かめる．
確かめ方：cd ~/lean/mathlib-ws && lake env lean <このファイルの絶対パス>
-/
namespace Evenend.Span

/-- 段をまたぐフロートの置き方：上か下か（`top`），左端の段`c`，またがる段数`w`． -/
structure Sp where
  top : Bool
  c : Nat
  w : Nat

/-- フロートが段`x`にかかる． -/
def covers (s : Sp) (x : Nat) : Bool := decide (s.c ≤ x) && decide (x < s.c + s.w)

/-- 2つのフロートが両立する：同じ位置（上どうし，下どうし）で同じ段にかかるなら，左端の段も
またがる段数も同じである（同じ段から同じ段数にまたがるものは積み重ねてよい）． -/
def Compat (t s : Sp) : Prop :=
  t.top = s.top → (∃ x, covers t x = true ∧ covers s x = true) → t.c = s.c ∧ t.w = s.w

/-- 段`x`で，前に置いた`t`と`s`がぶつかる． -/
def clash (t s : Sp) (x : Nat) : Bool :=
  (t.top == s.top) && covers t x && (t.c != s.c || t.w != s.w)

/-- 前に置いたフロート`prev`のもとで，`s`を置けるか．`s`のかかる段を左から順に見て，段が`N`を
超えるか，前に置いたものとぶつかれば，置けない．
実装は，段ごとに「かかっているフロートの（左端，段数）」を表に書いて調べる．表にあるのは，
前に置いたフロートのうちその段にかかるものの（左端，段数）である． -/
def okWith (N : Nat) (prev : List Sp) (s : Sp) : Bool :=
  (List.range' s.c s.w).all fun x => decide (x ≤ N) && prev.all fun t => !clash t s x

def go (N : Nat) : List Sp → List Sp → Bool
  | _, [] => true
  | prev, s :: l => okWith N prev s && go N (s :: prev) l

/-- 判定：フロートを順に置いていき，どれも置ければ通す． -/
def spanOk (N : Nat) (l : List Sp) : Bool := go N [] l

theorem covers_iff (s : Sp) (x : Nat) : covers s x = true ↔ s.c ≤ x ∧ x < s.c + s.w := by
  simp [covers]

theorem okWith_iff (N : Nat) (prev : List Sp) (s : Sp) :
    okWith N prev s = true ↔
      (∀ x, covers s x = true → x ≤ N) ∧ ∀ t ∈ prev, Compat t s := by
  simp only [okWith, List.all_eq_true, List.mem_range'_1, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true']
  constructor
  · intro h
    refine ⟨fun x hx => (h x ((covers_iff s x).mp hx)).1, ?_⟩
    intro t ht htop ⟨x, hx1, hx2⟩
    have hc := (h x ((covers_iff s x).mp hx2)).2 t ht
    simp only [clash, htop, beq_self_eq_true, hx1, Bool.true_and, Bool.or_eq_false_iff,
      bne_eq_false_iff_eq] at hc
    exact hc
  · intro h x hx
    have hcov : covers s x = true := (covers_iff s x).mpr hx
    refine ⟨h.1 x hcov, ?_⟩
    intro t ht
    have hcomp := h.2 t ht
    cases hc : clash t s x with
    | false => rfl
    | true =>
      simp only [clash, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, bne_iff_ne] at hc
      have := hcomp hc.1.1 ⟨x, hc.1.2, hcov⟩
      rcases hc.2 with h1 | h1
      · exact absurd this.1 h1
      · exact absurd this.2 h1

theorem go_iff (N : Nat) :
    ∀ (l prev : List Sp), go N prev l = true ↔
      (∀ s ∈ l, (∀ x, covers s x = true → x ≤ N) ∧ ∀ t ∈ prev, Compat t s) ∧
      l.Pairwise Compat := by
  intro l
  induction l with
  | nil => intro prev; simp [go]
  | cons s l ih =>
    intro prev
    simp only [go, Bool.and_eq_true, okWith_iff, ih, List.mem_cons, List.pairwise_cons]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      refine ⟨?_, fun s' hs' => (h3 s' hs').2 s (Or.inl rfl), h4⟩
      rintro s' (rfl | hs')
      · exact ⟨h1, h2⟩
      · exact ⟨(h3 s' hs').1, fun t ht => (h3 s' hs').2 t (Or.inr ht)⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1 s (Or.inl rfl), ?_, h3⟩
      intro s' hs'
      refine ⟨(h1 s' (Or.inr hs')).1, ?_⟩
      rintro t (rfl | ht)
      · exact h2 s' hs'
      · exact (h1 s' (Or.inr hs')).2 t ht

/-- 判定を通るのは，どのフロートも段数`N`を超える段にかからず，どの2つも両立するとき，
そのときだけである． -/
theorem spanOk_iff (N : Nat) (l : List Sp) :
    spanOk N l = true ↔ (∀ s ∈ l, ∀ x, covers s x = true → x ≤ N) ∧ l.Pairwise Compat := by
  unfold spanOk
  rw [go_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨fun s hs => (h1 s hs).1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨fun s hs => ⟨h1 s hs, fun t ht => by simp at ht⟩, h2⟩

/-- 判定を通れば，どのフロートも右端の段を越えない． -/
theorem spanOk_right (N : Nat) (l : List Sp) (h : spanOk N l = true) (s : Sp) (hs : s ∈ l)
    (hw : 0 < s.w) : s.c + s.w - 1 ≤ N :=
  ((spanOk_iff N l).mp h).1 s hs _ ((covers_iff s _).mpr (by omega))

/-- 例：3段で，上に段1から2段のフロートと段2から2段のフロートは置けない（段2で重なる）．
上と下に分ければ置ける．同じ段から同じ段数の2つは置ける． -/
example : spanOk 3 [⟨true, 1, 2⟩, ⟨true, 2, 2⟩] = false ∧
    spanOk 3 [⟨true, 1, 2⟩, ⟨false, 2, 2⟩] = true ∧
    spanOk 3 [⟨true, 1, 2⟩, ⟨true, 1, 2⟩] = true ∧
    spanOk 3 [⟨true, 2, 3⟩] = false := by decide

end Evenend.Span
