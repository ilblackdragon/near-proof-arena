import ZkFormal.NearV3.Candidates.ProcNativeSequence
namespace ZkFormal.NearV3.Candidates.ProcPreparedSequence
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

/-- The native generator input uses the prepared public fields and the actual
previous scheduler state. Request normalization is exactly existing instOf. -/
def input (sp : NearSpecV3.Scheduler.SchedPub) (prev : NearSpec.Bandwidth.State) : Input :=
  ⟨sp.ids,sp.params,sp.allowed,(instOf sp).raw,sp.seed,sp.allShardsHash,prev⟩

def inputs (ps : List (NearSpecV3.Scheduler.SchedPub × NearSpec.Bandwidth.State)) : List Input :=
  ps.map (fun p=>input p.1 p.2)

theorem input_bounds (sp : NearSpecV3.Scheduler.SchedPub) (prev : NearSpec.Bandwidth.State)
    (hs : SchedPubOk sp) :
    NearSpecV3.Scheduler.Params.calculate NearSpecV3.Scheduler.Config.pv86 (input sp prev).ids.length=some (input sp prev).p ∧
    (input sp prev).ids.length≤64 ∧ (input sp prev).raw.length≤4096 := by
  have hb := Complete.instOf_raw_le sp hs
  have hm := Nat.mul_le_mul hs.n64 hs.n64
  exact ⟨hs.params,hs.n64,by change (instOf sp).raw.length≤4096; omega⟩

/-- Prepared instances require no separate process capacity or ordinal
allocation premise. Successful generator execution is still explicit. -/
theorem prepared_local
    (ps : List (NearSpecV3.Scheduler.SchedPub × NearSpec.Bandwidth.State)) (rs : List Run)
    (hc : ps.length≤33) (hp : ∀p∈ps,SchedPubOk p.1)
    (h : ProcNativeSequence.runInputs (inputs ps) 0=.ok rs)
    (t : Nat) (pub : List Fp) :
    TableLocal ProcBoundaryRepair.table (ProcConcatGeometry.trace rs) t pub := by
  apply ProcNativeSequence.sequence_local (inputs ps) rs h (by simpa [inputs] using hc) ?_ t pub
  intro I hI
  rcases List.mem_map.mp hI with ⟨p,hp',rfl⟩
  exact input_bounds p.1 p.2 (hp p hp')
end ZkFormal.NearV3.Candidates.ProcPreparedSequence
