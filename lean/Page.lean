/-
evenendパッケージの定式化の4節「ほかの場面への適用」を確かめる．
確かめ方：cd ~/lean/mathlib-ws && lake env lean <このファイルの絶対パス>
-/
namespace Evenend.Page

/-- ページの途中で段組を改める：下端`β`で揃えた段組と，段組の間のアキ`g`を積んだ残りが，
次の段組の段の高さ`H' = H - β - g`である．積んだものの合計は，元の高さ`H`を超えない． -/
theorem block_height (H β g : Nat) (h : β + g ≤ H) : β + g + (H - β - g) = H := by omega

variable {R : Type} (fillAt : Nat → Option R) (need : R → Nat) (H : Nat)

/-- footnote=pageのページのくり返し．`fillAt h`は高さ`h`で段を分けた結果，`need r`は結果`r`で
ページに残した本文の脚注の領域の高さ．今の領域`Ψ`と結果`res`から始める．
残した本文の脚注の領域`nd`が`Ψ`より小さければ，高さ`H - nd`で分け直し，その結果の脚注が`nd`に
収まるときだけ置き換える．そうでなければ終える． -/
def loop : Nat → Nat → R → Nat × R
  | 0, Ψ, res => (Ψ, res)
  | fuel + 1, Ψ, res =>
    if Ψ ≤ need res then (Ψ, res)
    else
      match fillAt (H - need res) with
      | none => (Ψ, res)
      | some r2 => if need r2 ≤ need res then loop fuel (need res) r2 else (Ψ, res)

/-- 不変な性質：採った結果では，残した本文の脚注がつねに領域`Ψ`に収まる．領域は初めより
大きくならない．くり返しを何回で打ち切っても成り立つ． -/
theorem loop_inv :
    ∀ (fuel Ψ : Nat) (res : R), need res ≤ Ψ →
      need (loop fillAt need H fuel Ψ res).2 ≤ (loop fillAt need H fuel Ψ res).1 ∧
      (loop fillAt need H fuel Ψ res).1 ≤ Ψ := by
  intro fuel
  induction fuel with
  | zero => intro Ψ res h; simp [loop, h]
  | succ k ih =>
    intro Ψ res h
    simp only [loop]
    split
    · exact ⟨h, Nat.le_refl _⟩
    · split
      · exact ⟨h, Nat.le_refl _⟩
      · rename_i hlt _ r2 _
        split
        · rename_i h2
          have := ih (need res) r2 h2
          exact ⟨this.1, by omega⟩
        · exact ⟨h, Nat.le_refl _⟩

end Evenend.Page
