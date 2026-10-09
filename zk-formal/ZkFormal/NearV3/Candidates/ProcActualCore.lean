import ZkFormal.NearV3.Candidates.ProcActualInput
namespace ZkFormal.NearV3.Candidates.ProcActualCore
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen NearSpecV3.Scheduler

def decodePrevious (b : Option NearSpec.Bytes) : Option NearSpec.Bandwidth.State :=
  match b with | none=>some NearSpec.Bandwidth.State.initial | some b=>NearSpec.Bandwidth.State.decode b

theorem conversion (ids : List Nat) (p : Params) (hn : 1≤ids.length)
    (hp : Params.calculate Config.pv86 ids.length=some p)
    (raw : List (Nat×List BandwidthRequest)) :
    convertRaw (requestValues p) p.base ids raw=convRaw p ids.length (rawOf ids raw) := by
  simp only [convertRaw,convRaw,rawOf,List.filterMap_flatMap,List.filterMap_filterMap]
  congr 1
  funext x
  rcases x with ⟨sender,brs⟩
  simp only
  congr 1
  funext br
  simp only [convertRequestV,increases_eq_incsFrom hn hp]
  cases indexOf ids sender <;> cases indexOf ids br.toShard <;>
    simp only [Option.bind] <;> cases incsOf p br.bitmap <;> rfl

/-- Successful actual runCore constructs the repaired process model and retains
its exact decoded previous-state/authenticated-byte relationship. No canonical
previous record count, ordering, IDs, or uniqueness is required. -/
theorem process_exists (sp : SchedPub) (hs : SchedPubOk sp)
    (ha : sp.allowed.size=sp.ids.length*sp.ids.length)
    (hval : sp.values=requestValues sp.params)
    (oldBytes : Option NearSpec.Bytes) (out : Output) (h : runCore sp oldBytes=some out) :
    ∃prev st rs,decodePrevious oldBytes=some prev ∧
      ProcActualInput.process (ProcPreparedSequence.input sp prev)=.ok (st,rs) := by
  unfold runCore at h
  cases oldBytes <;> dsimp only at h
  all_goals
    obtain ⟨prev,hprev,hrest⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨stF,hproc,hout⟩ := Option.bind_eq_some_iff.mp hrest
    have hconv : convertRaw sp.values sp.params.base sp.ids sp.raw=
        convRaw sp.params sp.ids.length (instOf sp).raw := by
      rw [hval,conversion sp.ids sp.params hs.n1 hs.params,convRaw_instOf]
    rw [hconv] at hproc
    let I := ProcPreparedSequence.input sp prev
    have hproc' : processRequests sp.ids.length sp.allowed
        (ProcNativeGrant.native (ProcActualInput.initial I))
        (convRaw sp.params sp.ids.length (instOf sp).raw)=some stF := by
      rw [←ProcActualInput.initial_native I hs.n1 hs.params ha]
      exact hproc
    obtain ⟨st,rs,he,hst⟩ := ProcActualInput.prepared_process_exists sp hs ha prev stF hproc'
    exact ⟨prev,st,rs,hprev,he⟩
end ZkFormal.NearV3.Candidates.ProcActualCore
