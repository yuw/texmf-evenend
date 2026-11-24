/-
Glue.leanのモデル（高さを指定して組む箱のグルーの割り振り）の期待値を，格子状の入力について
書き出す．TeXの実測と比べるのはtest/model/run.sh．
1行が1件：「要素の並び | 箱の高さ | 組んだ後の各要素の長さ」．長さの単位はpt．
-/
import Glue

open Evenend.Glue

/-- 要素の種類：箱，伸び縮みしないグルー，有限の伸び縮みのグルー2種，無限に伸びるグルー2種 -/
def kinds : List Node :=
  [.box 10, .glue 5 0 0 false, .glue 5 3 2 false, .glue 4 6 1 false,
   .glue 0 1 0 true, .glue 2 2 0 true]

def lists : Nat → List (List Node)
  | 0 => [[]]
  | n + 1 => (lists n).flatMap fun l => kinds.map (· :: l)

def showNode : Node → String
  | .box h => s!"b{h}"
  | .glue w st sh f => s!"g{w},{st},{sh},{if f then 1 else 0}"

def line (l : List Node) (δ : ℚ) : String :=
  let t := Evenend.Glue.nat l + δ
  let m := mode t l
  " ".intercalate (l.map showNode) ++ " | " ++ toString t ++ " | " ++
    " ".intercalate (l.map fun n => toString (ht m [n]))

def main : IO Unit := do
  for n in [1, 2, 3, 4] do
    for l in lists n do
      for δ in ([-4, -3, -1, 0, 1, 2, 7] : List ℚ) do
        IO.println (line l δ)
