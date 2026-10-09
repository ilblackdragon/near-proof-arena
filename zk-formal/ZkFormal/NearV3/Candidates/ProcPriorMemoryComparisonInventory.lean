import ZkFormal.NearV3.Candidates.ProcPriorComparisonEnumeration
namespace ZkFormal.NearV3.Candidates.ProcPriorMemoryComparisonInventory
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ZkFormal.NearV3.Sched.Complete
open ZkFormal.NearV3.Assembly.CodecDigest
open ProcPriorNativeMemory ProcPriorComparisonRequests

theorem physical (xs : List Tagged) (hcap:xs.length<2^22) (t : Nat) (pub : List Fp) :
    (List.range (2^22)).flatMap (fun r=>rowTraffic (ProcPriorMemoryTable.interactions 67 68 69)
      (trace xs) t r pub 69 true)=(adjacent memoryPair xs).map cmpMsg := by
  rw [←ProcPriorComparisonEnumeration.physical memoryPair xs (2^22) (by omega),List.map_flatMap]
  apply flatMap_congr'
  intro r hr
  rw [ProcPriorMemoryComparisonRows.row xs hcap t r pub (List.mem_range.mp hr)]
  cases ha:xs[r]? <;> cases hb:xs[r+1]? <;>
    simp [ProcPriorComparisonEnumeration.atRow,ha,hb]

theorem count (bs : List NativeBlock) (hcap:(allRows bs).length<2^22)
    (t : Nat) (pub msg : List Fp) :
    tableBusCount (ProcPriorMemoryTable.interactions 67 68 69) (trace (allRows bs)) t pub 69 true msg=
      ((memory bs).map cmpMsg).count msg := by
  rw [tableBusCount_eq]
  change ((List.range (2^22)).flatMap _).count msg=_
  rw [physical _ hcap]
  rfl

theorem gated_count (bs : List NativeBlock) (hcap:(allRows bs).length<2^22)
    (t : Nat) (pub msg : List Fp) :
    tableBusCount (ProcPriorMemoryGated.table 67 68 69).interactions
      (ProcPriorMemoryGated.liftTrace (trace (allRows bs)) t pub) t pub 69 true msg=
      ((memory bs).map cmpMsg).count msg := by
  rw [ProcPriorMemoryGated.lift_table_traffic]
  exact count bs hcap t pub msg
end ZkFormal.NearV3.Candidates.ProcPriorMemoryComparisonInventory
