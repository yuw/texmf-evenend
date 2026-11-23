/-
evenendパッケージの定式化の補題「割り振りごとの最小の高さ」（min_h）と，その後の注意を確かめる．
`ok h`は「Fill(σ, h)が成功する」を表す，任意の述語である（単調とは仮定しない）．
長さの単位は，二分法を止める幅（1pt）．
確かめ方：cd ~/lean/mathlib-ws && lake env lean <このファイルの絶対パス>
-/
namespace Evenend.MinH

/-- 二分法．区間`[lo, hi]`を，幅が1以下になるまで狭める．返すのは（上端，`ok`を調べた回数）．
`fuel`は回数の上限（`hi - lo`あれば足りる）． -/
def bisect (ok : Nat → Bool) : Nat → Nat → Nat → Nat × Nat
  | 0, _, hi => (hi, 0)
  | fuel + 1, lo, hi =>
    if hi - lo > 1 then
      let mid := (lo + hi) / 2
      if ok mid then
        let r := bisect ok fuel lo mid
        (r.1, r.2 + 1)
      else
        let r := bisect ok fuel mid hi
        (r.1, r.2 + 1)
    else (hi, 0)

/-- 不変な性質：上端ではつねに`ok`が成り立つ．上端は初めの上端を超えない． -/
theorem bisect_ok (ok : Nat → Bool) (fuel lo hi : Nat) (h : ok hi = true) :
    ok (bisect ok fuel lo hi).1 = true ∧ (bisect ok fuel lo hi).1 ≤ hi := by
  induction fuel generalizing lo hi with
  | zero => simp [bisect, h]
  | succ n ih =>
    unfold bisect
    by_cases hw : hi - lo > 1
    · simp only [hw, ite_true]
      by_cases hm : ok ((lo + hi) / 2) = true
      · simp only [hm, ite_true]
        have := ih lo ((lo + hi) / 2) hm
        exact ⟨this.1, by omega⟩
      · simp only [hm]
        have := ih ((lo + hi) / 2) hi h
        exact ⟨this.1, this.2⟩
    · simp [hw, h]

/-- 回数：区間の幅が`2^k`以下なら，`ok`を調べるのは`k`回以下． -/
theorem bisect_steps (ok : Nat → Bool) (fuel : Nat) :
    ∀ (k lo hi : Nat), hi - lo ≤ 2 ^ k → (bisect ok fuel lo hi).2 ≤ k := by
  induction fuel with
  | zero => intro k lo hi _; simp [bisect]
  | succ n ih =>
    intro k lo hi hk
    unfold bisect
    by_cases hw : hi - lo > 1
    · simp only [hw, ite_true]
      cases k with
      | zero => simp at hk; omega
      | succ k =>
        have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
        by_cases hm : ok ((lo + hi) / 2) = true
        · simp only [hm, ite_true]
          have := ih k lo ((lo + hi) / 2) (by omega)
          omega
        · simp only [hm]
          have := ih k ((lo + hi) / 2) hi (by omega)
          simp
          omega
    · simp [hw]

/-- 調べ直し：`h1`の4下から`h1`まで，最初に`ok`が成り立つ高さ． -/
def scan (ok : Nat → Bool) (h1 : Nat) : Nat :=
  if ok (h1 - 4) then h1 - 4
  else if ok (h1 - 3) then h1 - 3
  else if ok (h1 - 2) then h1 - 2
  else if ok (h1 - 1) then h1 - 1
  else h1

theorem scan_ok (ok : Nat → Bool) (h1 : Nat) (h : ok h1 = true) :
    ok (scan ok h1) = true ∧ scan ok h1 ≤ h1 := by
  unfold scan
  split
  · exact ⟨by assumption, by omega⟩
  · split
    · exact ⟨by assumption, by omega⟩
    · split
      · exact ⟨by assumption, by omega⟩
      · split
        · exact ⟨by assumption, by omega⟩
        · exact ⟨h, Nat.le_refl _⟩

/-- 補題の手順：`Fill(σ, H)`が失敗すれば「入り切らない」（`none`）．成功すれば，下界`h0`から
二分法で狭め，調べ直して`h(σ)`を返す． -/
def minH (ok : Nat → Bool) (h0 H : Nat) : Option Nat :=
  if ok H then some (scan ok (bisect ok (H - h0) h0 H).1) else none

/-- 補題：返した高さでは`Fill`が成功し，`H`以下である． -/
theorem minH_spec (ok : Nat → Bool) (h0 H r : Nat) (h : minH ok h0 H = some r) :
    ok r = true ∧ r ≤ H := by
  unfold minH at h
  by_cases hH : ok H = true
  · simp only [hH, ite_true, Option.some.injEq] at h
    have hb := bisect_ok ok (H - h0) h0 H hH
    have hs := scan_ok ok _ hb.1
    subst h
    exact ⟨hs.1, by omega⟩
  · simp [hH] at h

/-- 補題：`Fill(σ, H)`が成功すれば，高さは必ず決まる． -/
theorem minH_isSome (ok : Nat → Bool) (h0 H : Nat) (h : ok H = true) :
    (minH ok h0 H).isSome = true := by
  simp [minH, h]

/-- 注意：`h(σ)`は，`Fill`が成功する最小の高さとは限らない．
`ok h`が`h = 3`と`h ≥ 50`で成り立つとき，`h0 = 0`，`H = 100`で手順は50を返すが，3でも成功する． -/
example : minH (fun h => h == 3 || decide (50 ≤ h)) 0 100 = some 50 := by decide

end Evenend.MinH
