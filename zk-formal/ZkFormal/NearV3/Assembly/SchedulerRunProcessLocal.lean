import ZkFormal.NearV3.Assembly.SchedulerRunComparisonTraffic
namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 Candidates Sched Sched.Gen Sched.Complete
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

theorem prior_run_index (p : Prep) (B : Nat) (bs : List NativeBlock) (hc:PriorCore p B bs)
    (i : Nat) (R : Run) (h:(bs.map NativeBlock.run)[i]?=some R) : R.tau=i := by
  rw [List.getElem?_map] at h
  obtain ⟨b,hb,rfl⟩:=Option.map_eq_some_iff.mp h
  exact (hc.indexed i b hb).2.1

theorem prior_process_table {cb : Bytes} {hint : Hint} {p : Prep} (hp:prepD0 cb hint=.ok p)
    (B : Nat) (bs : List NativeBlock) (hc:PriorCore p B bs) (t : Nat) (pub : List Fp) :
    TableLocal ProcBoundaryRepair.table (ProcConcatGeometry.trace (bs.map NativeBlock.run)) t pub := by
  apply ProcActualNativeComplete.list_local _ ?_ ?_ ?_ (prior_run_capacities hp B bs hc).2 t pub
  · intro R hR
    obtain ⟨sp,prev,hs,hr,_⟩:=prior_run_data hp B bs hc R hR
    exact ⟨ProcPreparedSequence.input sp prev,hs.params,hr⟩
  · intro R rest he
    exact prior_run_index p B bs hc 0 R (by rw [he];rfl)
  · intro pre R S post he
    have hR:R.tau=pre.length:=prior_run_index p B bs hc pre.length R (by
      rw [he,List.getElem?_append_right (by omega)]
      simp)
    have hS:S.tau=pre.length+1:=prior_run_index p B bs hc (pre.length+1) S (by
      rw [he,List.getElem?_append_right (by omega)]
      simp)
    omega
end ZkFormal.NearV3.Assembly.CodecDigest
