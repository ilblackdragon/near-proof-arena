import ZkFormal.NearV3.Rcpt.Candidates.DedupTable

/-! Isolated carry-row partition prototype. Definitions and syntactic shape checks
alone do not establish traffic-once, local completeness, continuation soundness, or
admission. The carry bus remains parameterized; bus64 is reserved for future integration. -/
namespace ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable
open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl

/-- Candidate allocation: QV uses63, QSH uses29; the integrated AIR needs at least65 buses. -/
abbrev sourceCarryBus : Nat := 64

theorem sourceCarryBus_reserved : sourceCarryBus < 65 ∧ sourceCarryBus ≠ 63 ∧ sourceCarryBus ≠ 29 := by
  decide +kernel

/-- A full field row is authenticated at the overlap, with no new columns. -/
def carryMessage : List Expr := (List.range DedupTable.width).map c

/-- Only the first partition enforces global-first constraints. -/
def rightConstraints : List Expr := DedupTable.constraints.mapIdx fun i ex =>
  if i ∈ [14, 15, 16, 51] then k 0 else ex

/-- The first partition's final row is a carried copy checked in the second one.
The preceding transition into that row remains fully constrained. -/
def leftConstraints : List Expr := DedupTable.constraints.map fun ex =>
  .mul (not .isLast) ex

/-- `mult` is a binary digit list, so each digit is gated rather than adding a digit. -/
def leftInteractions (carryBus : Nat) : List Interaction :=
  (DedupTable.interactions.map fun it =>
    { it with mult := it.mult.map fun e => .mul (not .isLast) e }) ++
  [send carryBus .isLast carryMessage]

def rightInteractions (carryBus : Nat) : List Interaction :=
  DedupTable.interactions ++ [recv carryBus .isFirst carryMessage]

def leftTable (carryBus : Nat) : Table :=
  { width := DedupTable.width, constraints := leftConstraints,
    interactions := leftInteractions carryBus, maxLog := 23 }

def rightTable (carryBus : Nat) : Table :=
  { width := DedupTable.width, constraints := rightConstraints,
    interactions := rightInteractions carryBus, maxLog := 23 }

set_option maxRecDepth 32768 in
theorem left_degree : leftConstraints.all (fun e => decide (e.degree ≤ 5)) = true := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem right_degree : rightConstraints.all (fun e => decide (e.degree ≤ 4)) = true := by
  decide +kernel

theorem carry_width : carryMessage.length = 57 := by decide +kernel

set_option maxRecDepth 32768 in
theorem left_width : ((leftTable 0).exprs.all fun e => decide (e.colBound ≤ 57)) = true := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem right_width : ((rightTable 0).exprs.all fun e => decide (e.colBound ≤ 57)) = true := by
  decide +kernel

end ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable
