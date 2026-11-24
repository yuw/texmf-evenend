/-
実装がログに書いた判断の記録（test/model/replay.shが集めたもの）を標準入力から読み，
モデルの関数で同じ入力から結果を求めて，実装の結果と比べる．1行が1件：
  select g s 実装が選んだ候補の番号 μ:h μ:h …
  mis b ε 実装の判定（0か1） v:縮み:本文だけか:本文があるか:中身があるか …（最後が最右段）
  beta β_T（なければ-） 実装の下端 v:縮み …
-/
import Replay

open Evenend Evenend.Select Evenend.Misaligned Evenend.Beta Evenend.Replay

def nats (s : String) : List Nat := (s.splitOn ":").filterMap String.toNat?

def cands (ts : List String) : List (Cand Nat) :=
  (ts.zip (List.range ts.length)).filterMap fun (t, i) =>
    match nats t with
    | [m, h] => some ⟨i + 1, m, h⟩
    | _ => none

def col (t : String) : Option Col :=
  match nats t with
  | [v, sh, a, b, c] => some ⟨v, sh, a == 1, b == 1, c == 1⟩
  | _ => none

/-- モデルの結果（文字列）．読めない行は`none` -/
def model (ts : List String) : Option (String × String) :=
  match ts with
  | "select" :: g :: s :: r :: rest =>
    match g.toNat?, s.toNat? with
    | some g, some s =>
      match selectS g s none (cands rest) with
      | some c => some (r, toString c.tag)
      | none => some (r, "0")
    | _, _ => none
  | "mis" :: b :: e :: r :: rest =>
    match b.toNat?, e.toNat?, (rest.filterMap col).reverse with
    | some b, some e, last :: init => some (r, if misE b e init.reverse last then "1" else "0")
    | _, _, _ => none
  | "beta" :: t :: r :: rest =>
    let cs := rest.filterMap fun x => match nats x with | [v, sh] => some (v, sh) | _ => none
    some (r, toString (chooseBeta t.toNat? cs))
  | _ => none

partial def loop (h : IO.FS.Stream) (n bad skip : Nat) : IO (Nat × Nat × Nat) := do
  let line ← h.getLine
  if line.isEmpty then return (n, bad, skip)
  let line := line.replace "\n" ""
  let ts := (line.splitOn " ").filter (· ≠ "")
  match model ts with
  | none => loop h n bad (skip + 1)
  | some (got, want) =>
    if got == want then loop h (n + 1) bad skip
    else
      if bad < 10 then IO.println s!"DIFF 実装 {got}，モデル {want}：{line}"
      loop h (n + 1) (bad + 1) skip

def main : IO Unit := do
  let (n, bad, skip) ← loop (← IO.getStdin) 0 0 0
  IO.println s!"RESULT replay: {n} decisions, {bad} differ, {skip} unreadable"
