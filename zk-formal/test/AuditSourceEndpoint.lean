import ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionCompile

open ZkFormal.NearV3 ZkFormal.NearV3.Rcpt.Candidates
open ZkFormal.Near ZkFormal.Near.Render.EvI

-- Regression: a final leaf can cyclically point at a path carry row. The old
-- endpoint then suppresses q=qe and le=32, permitting false terminal metadata.
private def badTerminal : SrcpB :=
  { j := 0, L := 12, dup := false, root := List.replicate 32 0,
    qe := 999, le := 999, ql := 1, leaf := List.replicate 32 0,
    path := [{q := 2, dir := false, sib := List.replicate 32 0, acc := List.replicate 32 0, pq := 1, pl := 32}] }

private def current (x : Nat) : Int :=
  (DedupRender.localCells badTerminal 0 (.leaf 31) true false x : Int)
private def carry (x : Nat) : Int :=
  (DedupRender.localCells badTerminal 0 (.path 0 0) false false x : Int)

set_option maxRecDepth 8192 in
example : DedupPartitionTable.rightBaseConstraints.all
    (fun e => decide (ev current carry 0 1 0 (fun _ => 0) e = 0)) = true := by
  decide +kernel

example : current SrcpV3.q ≠ current SrcpV3.qe ∧
    current SrcpV3.le ≠ 32 ∧ carry SrcpV3.sg = 1 := by
  decide +kernel

set_option maxRecDepth 8192 in
example : DedupPartitionTable.rightConstraints.all
    (fun e => decide (ev current carry 0 1 0 (fun _ => 0) e = 0)) = false := by
  decide +kernel

example : ev current carry 0 1 0 (fun _ => 0) DedupPartitionTable.rightEndpoint = 1 := by
  decide +kernel
