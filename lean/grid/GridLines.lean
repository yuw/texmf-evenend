/-
Layout.leanのモデル（行を積んだときの最終行のベースライン）の期待値を，格子状の入力について
書き出す．TeXの実測と比べるのはtest/model/run.sh．
\topskip（\splittopskip）は10pt，行送りは12pt，\lineskipは1pt，\lineskiplimitは0pt．
1行が1件：「各行の高さ,深さ | 最終行のベースライン」．単位はpt．
-/
import Layout

open Evenend.Layout

def kinds : List Line :=
  [6, 8, 10, 11, 14].flatMap fun h => [0, 3, 5].map fun d => ⟨h, d⟩

def lists : Nat → List (List Line)
  | 0 => [[]]
  | n + 1 => (lists n).flatMap fun l => kinds.map (· :: l)

def main : IO Unit := do
  for n in [1, 2, 3] do
    for l in lists n do
      IO.println (" ".intercalate (l.map fun x => s!"{x.ht},{x.dp}") ++ " | " ++
        toString (lastBaseline 10 12 1 l))
