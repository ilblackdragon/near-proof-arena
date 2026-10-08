import ZkFormal.NearV3.Render.Ups.CompactRowsCandidate

/-! Isolated compact UPS AIR candidate. No active table is changed. The rows
W0..W3 proceed directly to output part 1; fresh bytes are sent by the codec relay.
Honest local completeness and extraction for this candidate remain separate. -/
namespace ZkFormal.NearV3.Render.UpsRelay
open ZkFormal.Air ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

def compactRows : List Expr :=
  UpsV3.cRows.take 10 ++
  [c vb,
   .mul (c wt3) (not (n qb)), .mul (c wt3) (not (n pf)),
   .mul (c wt3) (sub (n j) (k 1)),
   .mul (c wt3) (sub (n (jo 1)) (k 1)),
   .mul (c wt3) (n (jo 2)), .mul (c wt3) (n (jo 3)), .mul (c wt3) (n (jo 4))] ++
  UpsV3.cRows.drop 23

def compactConstraints : List Expr :=
  cBool++compactRows++cConst++cWalk++cSeg++cPlan++cFields++cBytes++cDigest++cMem

/-- Index 5 is the sole old SPOST receive. Other interactions retain their
original gate/message expressions; vb is forced to zero by compactRows. -/
def compactInteractions : List Interaction :=
  UpsV3.interactions.take 5++UpsV3.interactions.drop 6

def compactTable : ZkFormal.Air.Table :=
  { UpsV3.table with constraints:=compactConstraints,interactions:=compactInteractions }

theorem compact_no_value_rows : c vb∈compactTable.constraints := by
  simp [compactTable,compactConstraints,compactRows]

theorem compact_log : compactTable.maxLog=22 := rfl

set_option maxHeartbeats 2000000 in
/-- Removing one receive does not increase running-product groups or degree. -/
theorem compact_shape : ZkFormal.Size.shapeOf 2 compactTable=ZkFormal.Size.shapeOf 2 UpsV3.table := by
  decide +kernel

theorem compact_interaction_count : compactTable.interactions.length=14 := by decide +kernel
end ZkFormal.NearV3.Render.UpsRelay
