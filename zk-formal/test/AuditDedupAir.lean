import ZkFormal.NearV3.Rcpt.Candidates.DedupRootLocal
import ZkFormal.NearV3.Rcpt.Candidates.DedupLeafLocal
import ZkFormal.NearV3.Rcpt.Candidates.DedupPathLocal
import ZkFormal.NearV3.Rcpt.Candidates.DedupPathUpper
import ZkFormal.NearV3.Rcpt.Candidates.DedupPathBoundary
import ZkFormal.NearV3.Rcpt.Candidates.DedupLeafExit
import ZkFormal.NearV3.Rcpt.Candidates.DedupPathExit
import ZkFormal.NearV3.Rcpt.Candidates.DedupTerminalLocal
import ZkFormal.NearV3.Rcpt.Candidates.DedupPaddingLocal
import ZkFormal.NearV3.Rcpt.Candidates.DedupTerminalPadding
import ZkFormal.NearV3.Rcpt.Candidates.DedupCrossLocal
import ZkFormal.NearV3.Rcpt.Candidates.DedupLocalBits
import ZkFormal.NearV3.Rcpt.Candidates.DedupAdjacency
import ZkFormal.NearV3.Rcpt.Candidates.DedupActualTraffic
import ZkFormal.NearV3.Rcpt.Candidates.DedupTrafficProof
import ZkFormal.NearV3.Rcpt.Candidates.DedupComputedLocal
import ZkFormal.NearV3.Rcpt.Candidates.DedupTraffic
import ZkFormal.NearV3.Rcpt.Candidates.DedupTable
import ZkFormal.Near.Render.Proof.NodeEv

open ZkFormal.NearV3 ZkFormal.NearV3.Rcpt.Candidates
open ZkFormal.Near ZkFormal.Near.Render.EvI

private def leafBlock (j q L : Nat) (dup : Bool) : SrcpB :=
  { j, L, dup, root := List.replicate 32 0, qe := q, le := 32, ql := q,
    leaf := List.replicate 32 0, path := [] }

private def pathBlock (dir : Bool) : SrcpB :=
  { leafBlock 0 1 12 false with
    qe := 2, le := 64,
    path := [{q := 2, dir, sib := List.replicate 32 0, acc := List.replicate 32 0, pq := 1, pl := 32}] }

private def checkRows (bs : List SrcpB) (repeated : Nat → Bool) (H : Nat) : Bool :=
  (List.range H).all fun r => DedupTable.constraints.all fun ex =>
    decide (ev (fun c => (DedupRender.cell bs repeated r c : Int))
      (fun c => (DedupRender.cell bs repeated ((r+1)%H) c : Int))
      (if r = 0 then 1 else 0) (if r+1 = H then 1 else 0)
      (if r+1 < H then 1 else 0) (fun _ => 0) ex = 0)

/-- info: true -/
#guard_msgs in
#eval checkRows [leafBlock 0 1 12 false] (fun _ => false) 64

/-- info: true -/
#guard_msgs in
#eval checkRows [leafBlock 0 1 12 false, leafBlock 1 2 12 true] (fun _ => true) 64

/-- info: true -/
#guard_msgs in
#eval checkRows [pathBlock false, leafBlock 1 3 12 true, leafBlock 2 3 12 false]
  (fun j => decide (j < 2)) 256

/-- info: true -/
#guard_msgs in
#eval checkRows [pathBlock true, leafBlock 1 3 12 true, leafBlock 2 3 12 false]
  (fun j => decide (j < 2)) 256

-- A physically full trace may terminate on a duplicate header, without padding.
/-- info: true -/
#guard_msgs in
#eval checkRows ((List.range 32).map fun j => leafBlock j (if j = 0 then 1 else 2) 12 (decide (j ≠ 0)))
  (fun _ => true) 64

-- The first occurrence of a repeated key must also be empty.
/-- info: false -/
#guard_msgs in
#eval checkRows [leafBlock 0 1 13 false, leafBlock 1 2 12 true] (fun _ => true) 64

-- A duplicate flag cannot omit the all-occurrence repetition metadata.
/-- info: false -/
#guard_msgs in
#eval checkRows [leafBlock 0 1 12 false, leafBlock 1 2 12 true] (fun _ => false) 64

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupTable.constraints_degree' does not depend on any axioms -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupTable.constraints_degree

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupTable.expressions_width' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupTable.expressions_width

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupTable.counts' does not depend on any axioms -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupTable.counts

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupTable.patched_of_not_dup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupTable.patched_of_not_dup

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupTable.computed_constraints' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupTable.computed_constraints

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupRender.duplicate_to_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupRender.duplicate_to_root

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupRender.duplicate_physical_last' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupRender.duplicate_physical_last

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupRender.duplicate_to_padding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupRender.duplicate_to_padding

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupRender.candidate_rowT' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupRender.candidate_rowT

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupRender.row_traffic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupRender.row_traffic

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupRender.regN_local' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupRender.regN_local

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupRender.root_messages' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupRender.root_messages

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupRender.nonroot_messages' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupRender.nonroot_messages

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupRender.block_messages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupRender.block_messages

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupRender.recs_messages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupRender.recs_messages

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupRender.active_messages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupRender.active_messages

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupRender.all_messages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupRender.all_messages

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupRender.field_messages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupRender.field_messages

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupRender.last_size_cell' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupRender.last_size_cell

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupRender.size_messages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupRender.size_messages

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupRender.table_traffic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupRender.table_traffic

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupCompile.relD0a_block_widths' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupCompile.relD0a_block_widths

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupCompile.relD0a_blocks_nonempty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupCompile.relD0a_blocks_nonempty

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupCompile.relD0a_table_traffic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupCompile.relD0a_table_traffic

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupRender.computed_root_to_leaf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupRender.computed_root_to_leaf

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupRender.first_root_to_leaf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupRender.first_root_to_leaf

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupRender.leaf_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupRender.leaf_step

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupRender.path_lower_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupRender.path_lower_step

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupRender.path_upper_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupRender.path_upper_step

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupRender.path_window_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupRender.path_window_boundary

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupRender.leaf_to_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupRender.leaf_to_path

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupRender.path_to_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupRender.path_to_path

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupRender.leaf_physical_last' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupRender.leaf_physical_last

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupRender.path_physical_last' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupRender.path_physical_last

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupRender.padding_to_padding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupRender.padding_to_padding

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupRender.padding_physical_last' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupRender.padding_physical_last

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupRender.leaf_to_padding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupRender.leaf_to_padding

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupRender.path_to_padding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupRender.path_to_padding

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupRender.leaf_to_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupRender.leaf_to_root

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupRender.path_to_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupRender.path_to_root

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupRender.mult_bits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupRender.mult_bits

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupRender.kinds_first' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupRender.kinds_first

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupRender.next_last' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupRender.next_last

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupRender.kinds_adj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupRender.kinds_adj

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupRender.recs_adj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupRender.recs_adj

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.DedupRender.adjAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.DedupRender.adjAt
