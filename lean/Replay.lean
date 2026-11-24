/-
実装（evenend.lua）がログに書いた判断の記録を，モデルの関数で再生するための定義．
実装は長さをsp（1/65536pt）の整数で持ち，比較に小さな余裕を持たせる．モデルの関数に，
刻みの半分`s`と余裕`ε`の引数を加えた形を定義し，`s = 1`，`ε = 0`のときにSelect.lean，
Misaligned.leanの関数と一致することを示す．再生するのはgrid/RunReplay.lean
（test/model/replay.shが動かす）．
確かめ方：lean/check.sh
-/
import Select
import Misaligned
import Beta

namespace Evenend.Replay

open Evenend.Select Evenend.Misaligned

/-- 手順3の規則．`g`は1行，`s`は高さを調べる刻みの半分（どちらも実装の単位）． -/
def betterS {α : Type} (g s : Nat) (best c : Cand α) : Bool :=
  (c.m ≤ best.m && c.h + s < best.h + g && (c.h + s < best.h || c.m < best.m))
    || (best.m < c.m && c.h + g < best.h + s)

def selectS {α : Type} (g s : Nat) : Option (Cand α) → List (Cand α) → Option (Cand α)
  | best, [] => best
  | none, c :: cs => selectS g s (some c) cs
  | some b, c :: cs => selectS g s (some (if betterS g s b c then c else b)) cs

theorem betterS_one {α : Type} (g : Nat) (best c : Cand α) :
    betterS g 1 best c = better g best c := rfl

/-- 単位を刻みの半分にすれば，Select.leanの`select`と同じ関数である． -/
theorem selectS_one {α : Type} (g : Nat) :
    ∀ (cs : List (Cand α)) (init : Option (Cand α)), selectS g 1 init cs = select g init cs := by
  intro cs
  induction cs with
  | nil => intro init; cases init <;> rfl
  | cons c cs ih =>
    intro init
    cases init with
    | none => simp only [selectS, select]; exact ih _
    | some b => simp only [selectS, select, betterS_one]; exact ih _

/-- 手順4の判定．(a)と(c)の比較に余裕`ε`を持たせる（実装は0.01pt）． -/
def misE (b ε : Nat) (init : List Col) (last : Col) : Bool :=
  decide (mx init + ε < last.v) ||
  (match tv init with
    | some t =>
      anyShort b t last init || (init ++ [last]).any (fun c => decide (t + ε < c.v - c.shr))
    | none => false)

/-- 余裕が0なら，Misaligned.leanの`mis`と同じ関数である． -/
theorem misE_zero (b : Nat) (init : List Col) (last : Col) :
    misE b 0 init last = mis b init last := by
  unfold misE mis
  cases tv init <;> simp

end Evenend.Replay
