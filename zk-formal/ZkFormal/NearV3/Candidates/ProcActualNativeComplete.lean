import ZkFormal.NearV3.Candidates.ProcActualRun
import ZkFormal.NearV3.Candidates.ProcActualRoundOrder
import ZkFormal.NearV3.Candidates.ProcConcatLocal
import ZkFormal.NearV3.Candidates.ProcBoundaryLocal
import ZkFormal.NearV3.Candidates.ProcActualRunProjection
namespace ZkFormal.NearV3.Candidates.ProcActualNativeComplete
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete

/-- Complete native single-instance process rendering at the common log22,
with replay data derived from execution rather than supplied separately. -/
theorem single_local (I : Input) (R : Run)
    (hp : NearSpecV3.Scheduler.Params.calculate NearSpecV3.Scheduler.Config.pv86 I.ids.length=some I.p)
    (h : ActualRun.run I 0=.ok R) (hcap : (procVs R).length+1≤2^22)
    (t : Nat) (pub : List Fp) :
    TableLocal ProcBoundaryRepair.table (ProcHeightBits.trace R) t pub :=
  ProcBoundaryLocal.native_local R (ProcActualRoundOrder.runData I 0 R hp h)
    (ProcActualRunProjection.run_fields I 0 R h).1 hcap t pub

/-- All successful native scheduler instances compose, including independent
seeds and zero-round instances. Capacity and the global tau allocation remain
explicit; no replay-data, field-equation, or memory-bound premise is needed. -/
theorem list_local (rs : List Run)
    (hr : ∀R∈rs,∃I : Input,
      NearSpecV3.Scheduler.Params.calculate NearSpecV3.Scheduler.Config.pv86 I.ids.length=some I.p ∧
      ActualRun.run I R.tau=.ok R)
    (hfirst : ∀R rest,rs=R::rest → R.tau=0)
    (ht : ∀pre R S post,rs=pre++R::S::post → S.tau=R.tau+1)
    (hcap : (ProcConcatGeometry.rows rs).length+1≤2^22)
    (t : Nat) (pub : List Fp) :
    TableLocal ProcBoundaryRepair.table (ProcConcatGeometry.trace rs) t pub := by
  apply ProcConcatLocal.proc_local rs ?_ hfirst ht hcap t pub
  intro R hR
  rcases hr R hR with ⟨I,hp,h⟩
  exact ProcActualRoundOrder.runData I R.tau R hp h
end ZkFormal.NearV3.Candidates.ProcActualNativeComplete
