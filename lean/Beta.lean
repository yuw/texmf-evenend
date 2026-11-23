/-
evenendパッケージの定式化の命題「揃えた配置の構成」の(ii)（下端βの決め方）を確かめる．
段を（見かけの下端`v`，フロートまわりのグルーの縮み`shr`）の組で表す．
確かめ方：cd ~/lean/mathlib-ws && lake env lean <このファイルの絶対パス>
-/
namespace Evenend.Beta

/-- 見かけの下端の最大 -/
def maxv : List (Nat × Nat) → Nat
  | [] => 0
  | c :: cs => max c.1 (maxv cs)

theorem le_maxv : ∀ (cs : List (Nat × Nat)) (c : Nat × Nat), c ∈ cs → c.1 ≤ maxv cs := by
  intro cs
  induction cs with
  | nil => intro c hc; simp at hc
  | cons x xs ih =>
    intro c hc
    simp only [List.mem_cons] at hc
    simp only [maxv]
    rcases hc with rfl | hc
    · omega
    · have := ih c hc
      omega

/-- どの段も，グルーを縮めれば`t`以下に収まる -/
def shrinksTo (t : Nat) (cs : List (Nat × Nat)) : Bool := cs.all (fun c => c.1 - c.2 ≤ t)

/-- 手順5の下端：基本は見かけの下端の最大．本文だけの段の下端`βT`があり，どの段も縮めて
`βT`以下に収まるときだけ，`βT`にする． -/
def chooseBeta (βT : Option Nat) (cs : List (Nat × Nat)) : Nat :=
  match βT with
  | some t => if shrinksTo t cs then t else maxv cs
  | none => maxv cs

/-- 命題の(ii)：どの段の見かけの下端も，グルーの縮みの範囲で下端β以下にできる． -/
theorem le_chooseBeta (βT : Option Nat) (cs : List (Nat × Nat)) (c : Nat × Nat) (hc : c ∈ cs) :
    c.1 - c.2 ≤ chooseBeta βT cs := by
  have hmax := le_maxv cs c hc
  unfold chooseBeta
  cases βT with
  | none => simp only; omega
  | some t =>
    simp only
    split
    · rename_i hs
      simp only [shrinksTo, List.all_eq_true, decide_eq_true_eq] at hs
      exact hs c hc
    · omega

end Evenend.Beta
