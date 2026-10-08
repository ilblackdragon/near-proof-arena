import ZkFormal.NearV3.Rcpt.Candidates.NativeWriteDepth
import ZkFormal.NearV3.Rcpt.Candidates.NativeExecutionRebasedKeys

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Render.UpsGen Assembly

/-- One ordered scheduler inventory uses exactly the concrete old-record forest
and reaches every actual native poststate. The old-post payload map is shared. -/
theorem native_rebased_upserts_keys {k : WalkD0} {w : StateWitness} {m : MainExecutionV3}
    {steps : List ImplicitStepV3} {last : Bytes} (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (hl : k.L.numShards≤64) :
    ∃writes,∃oldPost : PTrie,∃us : List SchedulerUpsertWitness,
      writes.map Prod.fst=(appliedReceipts k w).map (fun r=>accountKeyPath r.receiverId) ∧
      SizedAccountRun m.pre writes oldPost ∧
      us.map (fun u=>(u.pre,u.run.output))=(oldPost,m.result.trie)::steps.map (fun s=>(s.pre,s.post)) ∧
      (∀u∈us,u.Valid ∧ u.value.length≤98341) ∧
      let rs:=nativeReplayForest m steps oldPost writes
      (∀r∈rs,r.Valid) ∧
      (records (forestOldInputs rs) (forestNodes 0 0 0 (m.pre::steps.map ImplicitStepV3.pre))).map (fun s=>s.v.ser true)=
        ((rs.map ReplayTree.post).flatMap occs).map (fun t=>(nodeEnc t).map UInt8.toNat) := by
  obtain ⟨writes,oldPost,mid,so,u,hu,hctx,hpre,hvalue,houtput,hvalid,hs,hkeys,hr,hfinal,hforest,hbytes⟩:=
    native_execution_rebased_payloads_keys hm hv
  obtain ⟨us,hpairs,hgood⟩:=implicit_exact_upserts hv hl
  have hlen:=SchedulerUpsertWitness.value_bound hvalid (by rw [hctx];exact hl)
  refine ⟨writes,oldPost,u::us,hkeys,hr,?_,?_,hforest,hbytes⟩
  · simp only [List.map_cons,hpre,houtput,hpairs]
  · intro x hx
    rcases List.mem_cons.mp hx with rfl|hx
    · exact ⟨hvalid,hlen⟩
    · exact hgood x hx

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
