import ZkFormal.NearV3.Candidates.ProcPriorProcessTransport
namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 Candidates Sched Sched.Gen Sched.Complete
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

theorem prior_repaired_memory {cb : Bytes} {hint : Hint} {p : Prep} (hp:prepD0 cb hint=.ok p)
    (B : Nat) (bs : List NativeBlock) (hc:PriorCore p B bs) (t : Nat) (pub : List Fp) :
    TableLocal (ProcPriorProcessRepairedFamily.selected[11]!)
      (MemConcatCells.trace (bs.map NativeBlock.run)) t pub := by
  rw [ProcPriorProcessRepairedFamily.other_slot 11 (by decide)]
  exact prior_selected_memory hp B bs hc t pub

theorem prior_repaired_process {cb : Bytes} {hint : Hint} {p : Prep} (hp:prepD0 cb hint=.ok p)
    (B : Nat) (bs : List NativeBlock) (hc:PriorCore p B bs) (t : Nat) (pub : List Fp) :
    TableLocal (ProcPriorProcessRepairedFamily.selected[10]!)
      (ProcConcatGeometry.trace (bs.map NativeBlock.run)) t pub := by
  rw [ProcPriorProcessRepairedFamily.process_slot]
  exact prior_process_table hp B bs hc t pub

theorem prior_repaired_run_comparison_count {cb : Bytes} {hint : Hint} {p : Prep}
    (hp:prepD0 cb hint=.ok p) (B : Nat) (bs : List NativeBlock) (hc:PriorCore p B bs)
    (tm tp : Nat) (pub msg : List Fp) :
    tableBusCount (ProcPriorProcessRepairedFamily.selected[11]!).interactions
      (MemConcatCells.trace (bs.map NativeBlock.run)) tm pub B_SCMP true msg+
    tableBusCount (ProcPriorProcessRepairedFamily.selected[10]!).interactions
      (ProcConcatGeometry.trace (bs.map NativeBlock.run)) tp pub B_SCMP true msg=
      ((bs.flatMap (fun b=>b.run.cmps)).map cmpMsg).count msg := by
  rw [ProcPriorProcessTransport.count,ProcPriorProcessTransport.count]
  exact prior_selected_run_comparison_count hp B bs hc tm tp pub msg
end ZkFormal.NearV3.Assembly.CodecDigest
