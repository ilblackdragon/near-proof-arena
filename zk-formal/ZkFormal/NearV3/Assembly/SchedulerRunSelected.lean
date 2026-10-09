import ZkFormal.NearV3.Assembly.SchedulerRunMemoryLocal
import ZkFormal.NearV3.Assembly.SchedulerRunProcessLocal
import ZkFormal.NearV3.Candidates.ProcPriorComparatorRoutedFamily
namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 Candidates Sched Sched.Gen Sched.Complete
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem routed_memory_slot : ProcPriorComparatorRoutedFamily.selected[11]! =Mem.table := by decide +kernel

theorem routed_process_slot : ProcPriorComparatorRoutedFamily.selected[10]! =Proc.table := by decide +kernel

theorem routed_process_interactions :
    (ProcPriorComparatorRoutedFamily.selected[10]!).interactions=ProcBoundaryRepair.table.interactions := by decide +kernel

theorem routed_process_ne_repaired : ProcPriorComparatorRoutedFamily.selected[10]! =ProcBoundaryRepair.table → False := by decide +kernel

theorem prior_selected_memory {cb : Bytes} {hint : Hint} {p : Prep} (hp:prepD0 cb hint=.ok p)
    (B : Nat) (bs : List NativeBlock) (hc:PriorCore p B bs) (t : Nat) (pub : List Fp) :
    TableLocal (ProcPriorComparatorRoutedFamily.selected[11]!)
      (MemConcatCells.trace (bs.map NativeBlock.run)) t pub := by
  rw [routed_memory_slot]
  exact prior_memory_table hp B bs hc t pub

theorem prior_selected_run_comparison_count {cb : Bytes} {hint : Hint} {p : Prep}
    (hp:prepD0 cb hint=.ok p) (B : Nat) (bs : List NativeBlock) (hc:PriorCore p B bs)
    (tm tp : Nat) (pub msg : List Fp) :
    tableBusCount (ProcPriorComparatorRoutedFamily.selected[11]!).interactions
      (MemConcatCells.trace (bs.map NativeBlock.run)) tm pub B_SCMP true msg+
    tableBusCount (ProcPriorComparatorRoutedFamily.selected[10]!).interactions
      (ProcConcatGeometry.trace (bs.map NativeBlock.run)) tp pub B_SCMP true msg=
      ((bs.flatMap (fun b=>b.run.cmps)).map cmpMsg).count msg := by
  rw [routed_memory_slot,routed_process_interactions]
  exact prior_run_comparison_count hp B bs hc tm tp pub msg
end ZkFormal.NearV3.Assembly.CodecDigest
