import ZkFormal.NearV3.Candidates.ProcCodecComparisonInventory
import ZkFormal.NearV3.Candidates.ProcNativeCodecComparisonBudget
namespace ZkFormal.NearV3.Candidates.ProcCodecComparisonPhysical
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Sched.Complete ZkFormal.NearV3.Assembly.CodecDigest

theorem block (b : NativeBlock) (hb:b.Valid) :
    ProcCodecComparisonInventory.traffic b.output.rows.toList=b.output.cmps.map cmpMsg :=
  ProcCodecComparisonInventory.generated _ _ _ _ _ _ _ hb.2.2.2.2

theorem physical (bs : List NativeBlock) (hlen:bs.length≤33)
    (hb:∀b∈bs,b.Valid ∧ b.run.n≤64) (t : Nat) (pub : List Fp) :
    (List.range (2^22)).flatMap (fun r=>rowTraffic ProcPriorCodecActual.table.interactions
      (SchedHeight.trace (nativeBlockRows bs) codecPad) t r pub B_SCMP true)=
      (ProcNativeCodecComparisonBudget.requests bs).map cmpMsg := by
  have hs:=native_block_rows_bound bs hb
  rw [ProcCodecConcatTraffic.blocks bs (by omega)]
  unfold ProcNativeCodecComparisonBudget.requests
  rw [List.map_flatMap]
  apply ZkFormal.Near.flatMap_congr'
  intro b hm
  exact block b (hb b hm).1

theorem count (bs : List NativeBlock) (hlen:bs.length≤33)
    (hb:∀b∈bs,b.Valid ∧ b.run.n≤64) (t : Nat) (pub msg : List Fp) :
    tableBusCount ProcPriorCodecActual.table.interactions
      (SchedHeight.trace (nativeBlockRows bs) codecPad) t pub B_SCMP true msg=
      ((ProcNativeCodecComparisonBudget.requests bs).map cmpMsg).count msg := by
  rw [tableBusCount_eq]
  exact congrArg (fun xs=>xs.count msg) (physical bs hlen hb t pub)
end ZkFormal.NearV3.Candidates.ProcCodecComparisonPhysical
