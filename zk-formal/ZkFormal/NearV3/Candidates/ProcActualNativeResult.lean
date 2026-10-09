import ZkFormal.NearV3.Candidates.ProcActualPublic
namespace ZkFormal.NearV3.Candidates.ProcActualNativeResult
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen NearSpecV3.Scheduler

/-- Native output after the process stage, including distribution and exact encoding. -/
def finish (sp : SchedPub) (prev : NearSpec.Bandwidth.State) (st : St) : Output :=
  let st := distribute sp.ids.length sp.allowed st
  let sid (i : Nat) := sp.ids.getD i 0
  let links := List.range (sp.ids.length * sp.ids.length)
  let newLinks := links.map fun l =>
    NearSpec.Bandwidth.LinkAllowance.mk (sid (l / sp.ids.length)) (sid (l % sp.ids.length)) st.allowance[l]!
  let newState : NearSpec.Bandwidth.State :=
    ⟨newLinks, NearSpec.sha256 (prev.sanityHash ++ sp.allShardsHash)⟩
  ⟨newState.encode, links.map fun l =>
    ((sid (l / sp.ids.length), sid (l % sp.ids.length)), st.granted[l]!), sp.params⟩

/-- Native acceptance produces a corrected process whose final state reconstructs
exactly the native output. Previous bytes are decoded without canonicalization. -/
theorem process_output (sp : SchedPub) (hs : SchedPubOk sp)
    (ha : sp.allowed.size=sp.ids.length*sp.ids.length)
    (hval : sp.values=requestValues sp.params)
    (oldBytes : Option NearSpec.Bytes) (out : Output) (h : runCore sp oldBytes=some out) :
    ∃prev st rs,ProcActualCore.decodePrevious oldBytes=some prev ∧
      ProcActualInput.process (ProcPreparedSequence.input sp prev)=.ok (st,rs) ∧
      finish sp prev (ProcNativeGrant.native st)=out := by
  unfold runCore at h
  cases oldBytes <;> dsimp only at h
  all_goals
    obtain ⟨prev,hprev,hrest⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨stF,hproc,hout⟩ := Option.bind_eq_some_iff.mp hrest
    have hconv : convertRaw sp.values sp.params.base sp.ids sp.raw=
        convRaw sp.params sp.ids.length (instOf sp).raw := by
      rw [hval,ProcActualCore.conversion sp.ids sp.params hs.n1 hs.params,convRaw_instOf]
    rw [hconv] at hproc
    let I := ProcPreparedSequence.input sp prev
    have hproc' : processRequests sp.ids.length sp.allowed
        (ProcNativeGrant.native (ProcActualInput.initial I))
        (convRaw sp.params sp.ids.length (instOf sp).raw)=some stF := by
      rw [←ProcActualInput.initial_native I hs.n1 hs.params ha]
      exact hproc
    obtain ⟨st,rs,he,hst⟩ := ProcActualInput.prepared_process_exists sp hs ha prev stF hproc'
    refine ⟨prev,st,rs,hprev,he,?_⟩
    rw [hst]
    exact Option.some.inj hout
/-- Public inputs obtained from the actual apply context discharge conversion
and allowed-grid premises of the native output connection. -/
theorem scheduled_process_output (ctx : NearSpecV3.ApplyCtx) (sp : SchedPub)
    (hs : SchedPubOk sp) (hpub : NearSpecV3.schedPub ctx=some sp)
    (oldBytes : Option NearSpec.Bytes) (out : Output) (h : runCore sp oldBytes=some out) :
    ∃prev st rs,ProcActualCore.decodePrevious oldBytes=some prev ∧
      ProcActualInput.process (ProcPreparedSequence.input sp prev)=.ok (st,rs) ∧
      finish sp prev (ProcNativeGrant.native st)=out :=
  process_output sp hs (ProcActualPublic.schedPub_fields ctx sp hpub).1
    (ProcActualPublic.schedPub_fields ctx sp hpub).2 oldBytes out h

end ZkFormal.NearV3.Candidates.ProcActualNativeResult
