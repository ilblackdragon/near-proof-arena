import ZkFormal.NearV3.Candidates.ProcPriorIdComparisonRows
namespace ZkFormal.NearV3.Candidates.ProcPriorIdComparisonInventory
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ZkFormal.NearV3.Sched.Complete
open ZkFormal.NearV3.Assembly.CodecDigest
open ProcIdTaggedCells ProcPriorComparisonRequests

theorem physical (xs : List Tagged) (hcap:xs.length<2^22) (t : Nat) (pub : List Fp) :
    (List.range (2^22)).flatMap (fun r=>rowTraffic (ProcPriorIdTable.interactions 70 71 72 69)
      (ProcIdTaggedTrace.trace xs) t r pub 69 true)=(adjacent idPair xs).map cmpMsg := by
  rw [←ProcPriorComparisonEnumeration.physical idPair xs (2^22) (by omega),List.map_flatMap]
  apply flatMap_congr'
  intro r hr
  exact ProcPriorIdComparisonRows.row xs hcap t r pub (List.mem_range.mp hr)

theorem count (bs : List NativeBlock)
    (hcap:(ProcIdTaggedRows.rows (fun b=>b.pub.ids) bs).length<2^22)
    (t : Nat) (pub msg : List Fp) :
    tableBusCount (ProcPriorIdTable.interactions 70 71 72 69)
      (ProcIdTaggedTrace.trace (ProcIdTaggedRows.rows (fun b=>b.pub.ids) bs)) t pub 69 true msg=
      ((ids bs).map cmpMsg).count msg := by
  rw [tableBusCount_eq]
  change ((List.range (2^22)).flatMap _).count msg=_
  rw [physical _ hcap]
  rfl
end ZkFormal.NearV3.Candidates.ProcPriorIdComparisonInventory
