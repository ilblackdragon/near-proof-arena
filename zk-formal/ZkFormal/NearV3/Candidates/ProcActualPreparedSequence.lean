import ZkFormal.NearV3.Candidates.ProcPreparedSequence
import ZkFormal.NearV3.Candidates.ProcActualNativeSequence
namespace ZkFormal.NearV3.Candidates.ProcActualPreparedSequence
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcPreparedSequence
/-- Prepared public inputs and unmodified native prior states drive the corrected
run sequence. Successful execution yields the complete common-log22 process trace. -/
theorem prepared_local
    (ps : List (NearSpecV3.Scheduler.SchedPub × NearSpec.Bandwidth.State)) (rs : List Run)
    (hc : ps.length≤33) (hp : ∀p∈ps,SchedPubOk p.1)
    (h : ProcActualNativeSequence.runInputs (inputs ps) 0=.ok rs)
    (t : Nat) (pub : List Fp) :
    TableLocal ProcBoundaryRepair.table (ProcConcatGeometry.trace rs) t pub := by
  apply ProcActualNativeSequence.sequence_local (inputs ps) rs h (by simpa [inputs] using hc) ?_ t pub
  intro I hI
  rcases List.mem_map.mp hI with ⟨p,hp',rfl⟩
  exact input_bounds p.1 p.2 (hp p hp')
end ZkFormal.NearV3.Candidates.ProcActualPreparedSequence
