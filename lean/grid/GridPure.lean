/-
モデルの関数（候補の列挙，候補を選ぶ規則，揃わない配分の判定，下端の決め方，高さを探す手順）の
結果を，小さな範囲の入力のすべてについて書き出す．実装（evenend.luaのM.pure）と比べるのは
test/model/pure.sh．1行が1件：
  enum N | 置かれていた段,種類 … | 候補の数 候補の並びのハッシュ
    種類：n ふつう，d 持ち越し，t 上の段をまたぐ（2段），b 下の段をまたぐ（2段）
  better g s 最良の動かす量 最良の高さ 候補の動かす量 候補の高さ | 置き換えるか
  mis b ε | v:縮み:本文だけか:本文があるか:中身があるか …（最後が最右段） | 判定 下端
  minh h0 H | 高さ0からHで入り切るか（0か1の並び） | 返す高さ（入り切らなければ-）
-/
import Enum
import Span
import Replay
import MinH

open Evenend

def tuples {α : Type} (xs : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => (tuples xs n).flatMap fun l => xs.map (· :: l)

/-- フロートの種類：名前，段をまたぐか，持ち越しか，またぐものの（上か，段数） -/
def kindsAll : List (Char × Bool × Bool × Option (Bool × Nat)) :=
  [('n', false, false, none), ('d', false, true, none),
   ('t', true, false, some (true, 2)), ('b', true, false, some (false, 2))]

def hashC (cs : List (List Nat)) : Nat :=
  cs.foldl (fun h σ => σ.foldl (fun h c => (h * 131 + c + 1) % 1000000007)
    ((h * 131 + 1000) % 1000000007)) 0

def enumLine (N : Nat) (fs : List (Nat × Char × Bool × Bool × Option (Bool × Nat))) : String :=
  let F : List Enum.Fl := fs.map fun (o, _, sp, df, _) => ⟨o, sp, df⟩
  let geom := fs.map fun (_, _, _, _, g) => g
  let cs := Enum.candidates N (fun σ => Span.spanOk N (Span.placements geom σ)) F
  let spec := " ".intercalate (fs.map fun (o, k, _, _, _) => s!"{o},{k}")
  s!"enum {N} | {spec} | {cs.length} {hashC cs}"

def colKinds (vs : List Nat) : List Misaligned.Col :=
  vs.flatMap fun v => [0, 8].flatMap fun sh => [false, true].flatMap fun t =>
    [(false, false), (false, true), (true, true)].map fun (x, c) => ⟨v, sh, t, x, c⟩

def b01 (b : Bool) : String := if b then "1" else "0"

def misLine (b e : Nat) (cols : List Misaligned.Col) : String :=
  match cols.reverse with
  | [] => ""
  | last :: ri =>
    let init := ri.reverse
    let spec := " ".intercalate (cols.map fun c =>
      s!"{c.v}:{c.shr}:{b01 c.textOnly}:{b01 c.hasText}:{b01 c.content}")
    let beta := Beta.chooseBeta (Misaligned.tv init) (cols.map fun c => (c.v, c.shr))
    s!"mis {b} {e} | {spec} | {b01 (Replay.misE b e init last)} {beta}"

def main : IO Unit := do
  -- 候補の列挙：段数1から4，フロート3つまで，置かれていた段と種類のすべて
  for N in [1, 2, 3, 4] do
    let one := (List.range N).flatMap fun o => kindsAll.map fun k => (o + 1, k)
    for n in [0, 1, 2, 3] do
      for fs in tuples one n do
        IO.println (enumLine N fs)
  -- 候補が多いとき（64個を超えると絞る．257個で打ち切る）：段1のフロート6から8個
  for N in [3, 4, 5] do
    for n in [6, 7, 8] do
      for fs in tuples [(1, kindsAll[0]!), (1, kindsAll[1]!)] n do
        IO.println (enumLine N fs)
  -- 候補を選ぶ規則
  for g in [2, 4, 5] do
    for s in [1, 2] do
      for bm in [0, 1, 2] do
        for bh in List.range 10 do
          for m in [0, 1, 2] do
            for h in List.range 10 do
              let r := Replay.betterS g s (⟨(), bm, bh⟩ : Select.Cand Unit) ⟨(), m, h⟩
              IO.println s!"better {g} {s} {bm} {bh} {m} {h} | {b01 r}"
  -- 揃わない配分の判定と下端：行送り12．2段は見かけの下端4通り，3段は3通り
  for e in [0, 1] do
    for cols in tuples (colKinds [4, 10, 11, 18]) 2 do
      IO.println (misLine 12 e cols)
    for cols in tuples (colKinds [4, 11, 18]) 3 do
      IO.println (misLine 12 e cols)
  -- 高さを探す手順：H = 10で，入り切るかどうかのすべての組み合わせ
  for h0 in [0, 3, 12] do
    for bits in List.range 2048 do
      let ok := fun h => decide (h ≤ 10) && bits.testBit h
      let spec := String.join ((List.range 11).map fun h => b01 (ok h))
      let r := match MinH.minH ok h0 10 with
        | some r => toString r
        | none => "-"
      IO.println s!"minh {h0} 10 | {spec} | {r}"
