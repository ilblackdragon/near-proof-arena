import ZkFormal.NearV3.Rcpt.Candidates.SizeCountTables
import ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTraffic

/-! Four source partitions within the protocol's unchanged height limit.
Each boundary uses its own bus: a shared untagged carry bus would allow the
middle partitions to be permuted. This candidate is not yet a complete AIR. -/
namespace ZkFormal.NearV3.Rcpt.Candidates.SourceLog22
open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.Algebra
open DedupPartitionTable

def firstTable : Air.Table := { leftTable 64 with maxLog := 22 }

/-- A middle partition receives its first row, checks all logical transitions
except the copied last row, and passes that last row to its successor. -/
def middleConstraints : List Expr :=
  rightBaseConstraints.map fun ex => .mul (not .isLast) ex

def middleInteractions (incoming outgoing : Nat) : List Interaction :=
  leftInteractions outgoing ++ [recv incoming .isFirst carryMessage]

def middleTable (incoming outgoing : Nat) : Air.Table :=
  { width := DedupTable.width, constraints := middleConstraints,
    interactions := middleInteractions incoming outgoing, maxLog := 22 }

def lastTable : Air.Table := { rightTable 66 with maxLog := 22 }

/-- SIZE counts are extended consistently on every physical source partition. -/
def tables : List Air.Table :=
  [firstTable, middleTable 64 65, middleTable 65 66, lastTable].map SizeCount.sourceTable

def air : Air := ⟨tables, 67, 202⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem wellformed : tables.all (Table.wf air 6) = true := by decide +kernel

theorem height_cap : ∀ T ∈ tables, T.maxLog = 22 := by
  decide +kernel

/-- Four traces lose three rows to authenticated overlap and retain one terminal
padding row. The existing source envelope fits with 442940 rows to spare. -/
theorem source_capacity {n : Nat} (h : n ≤ 16334272) :
    n + 3 + 1 ≤ 4 * 2^22 ∧ 4 * 2^22 - (16334272 + 3 + 1) = 442940 := by
  omega

/-- Middle boundaries do not duplicate ordinary traffic. The incoming carry
receive and outgoing carry send are invisible on every other bus. -/
theorem middle_normal_row (tr : Trace Fp) (tt r : Nat) (pub : List Fp)
    (incoming outgoing : Nat) (bb : Nat) (sd : Bool)
    (hi : bb ≠ incoming) (ho : bb ≠ outgoing) :
    rowTraffic (middleInteractions incoming outgoing) tr tt r pub bb sd =
      if r+1=tr.height tt then [] else
        rowTraffic DedupTable.interactions tr tt r pub bb sd := by
  have hz (v : Fp) : (1 - 1) * v = 0 := by grind
  have hone (v : Fp) : (1 - 0) * v = v := by grind
  by_cases hr : r + 1 = tr.height tt
  all_goals simp [middleInteractions, leftInteractions, DedupTable.interactions,
    rowTraffic, recv, send, Interaction.multNat, Interaction.multNat.go,
    Interaction.msgVal, eval_mul, eval_not, eval_isLast, hr,
    Ne.symm hi, Ne.symm ho, hz, hone, show ¬(0 : Fp) = 1 by decide]
  all_goals rfl

set_option maxRecDepth 32768 in
/-- No erased first-row equation is accidentally retained by a middle table,
and its successor equations remain checked away from the overlap row. -/
theorem middle_constraint {tr : Trace Fp} {tt r incoming outgoing : Nat}
    {pub : List Fp} (h : TableLocal (middleTable incoming outgoing) tr tt pub)
    (hr : r < tr.height tt) (hl : r+1 ≠ tr.height tt)
    (ex : Expr) (he : ex ∈ rightBaseConstraints) : ex.eval tr tt r pub = 0 := by
  have hc := h.constr r hr (.mul (not .isLast) ex)
    (List.mem_map.mpr ⟨ex,he,rfl⟩)
  simp only [eval_mul,eval_not,eval_isLast,if_neg hl] at hc
  grind

/-- All three boundary buses are distinct and outside the existing 0..63 family. -/
theorem boundary_buses :
    ([64,65,66] : List Nat).Nodup ∧ ∀ b ∈ ([64,65,66] : List Nat), 64 ≤ b ∧ b < air.numBuses := by
  decide +kernel

end ZkFormal.NearV3.Rcpt.Candidates.SourceLog22
