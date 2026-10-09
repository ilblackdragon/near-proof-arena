import ZkFormal.NearV3.Candidates.CurrentFamily
import ZkFormal.NearV3.Candidates.ShaCarryKinds
open ZkFormal.Size ZkFormal.NearV3.Candidates
-- Replace SHA tables with actual checked candidate definitions. Bin-count changes
-- below are budget sensitivities, not complete global job allocations.
def packingTables (n : Nat) :=
  List.replicate n (ShaCarryKinds.table ZkFormal.Near.B_BYTES ZkFormal.Near.B_DIGEST) ++
    CurrentFamily.tables.drop 4
#eval ([3,4]:List Nat).map fun n =>
  (n,sizeOfWeq (ZkFormal.V2.G.pg 2) ((packingTables n).map (shapeOf 2)))
#eval (packingTables 4).all (fun t => t.wf ⟨packingTables 4,67,202⟩ 8)
