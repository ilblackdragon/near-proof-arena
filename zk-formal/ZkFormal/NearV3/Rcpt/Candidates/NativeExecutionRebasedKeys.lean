import ZkFormal.NearV3.Rcpt.Candidates.ChosenRebasedWitness

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Render.UpsGen Assembly

/-- Actual native execution supplies the complete same-forest post-payload
constructor; its original node serializations and structural final root use the
same receipt replay and the same scheduler result. -/
theorem native_execution_rebased_payloads_keys {k : WalkD0} {w : StateWitness} {m : MainExecutionV3}
    {steps : List ImplicitStepV3} {last : Bytes} (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last) :
    ∃writes,∃oldPost mid : PTrie,∃so : SchedOut,∃u : SchedulerUpsertWitness,
      schedulerUpsertWitness (m.ctx k) oldPost=.ok u ∧
      u.ctx=m.ctx k ∧ u.pre=oldPost ∧ u.value=so.state ∧ u.run.output=m.result.trie ∧ u.Valid ∧
      schedStep prims (m.ctx k) m.pre=.ok (mid,so) ∧
      writes.map Prod.fst=(appliedReceipts k w).map (fun r=>accountKeyPath r.receiverId) ∧
      SizedAccountRun m.pre writes oldPost ∧
      oldPost.upsert keyBwState so.state=some m.result.trie ∧
      let rs:=nativeReplayForest m steps oldPost writes
      (∀r∈rs,r.Valid) ∧
      (records (forestOldInputs rs) (forestNodes 0 0 0 (m.pre::steps.map ImplicitStepV3.pre))).map (fun s=>s.v.ser true)=
        ((rs.map ReplayTree.post).flatMap occs).map (fun t=>(nodeEnc t).map UInt8.toNat) := by
  have hw : m.pre.wf=true := by
    rw [hm.pre]
    exact (built_spec w.main.values trieFuel k.slotB2.prevStateRoot _ hm.root_length).2.1
  obtain ⟨writes,oldPost,mid,so,hs,hkeys,hr,hp,hpost,hlen,hfinal⟩:=
    newchunk_old_tree_reconstruct (TrieShape.of_wf _ hw) hw hm.run
  have hvalid : ∀r∈nativeReplayForest m steps oldPost writes,r.Valid := by
    intro r hmem
    simp only [nativeReplayForest,List.mem_cons,List.mem_map] at hmem
    rcases hmem with rfl|⟨s,hs,rfl⟩
    · exact hr
    · exact .nil _
  have hwell : ∀r∈nativeReplayForest m steps oldPost writes,r.pre.wf=true := by
    intro r hmem
    simp only [nativeReplayForest,List.mem_cons,List.mem_map] at hmem
    rcases hmem with rfl|⟨s,hs,rfl⟩
    · exact hw
    · obtain ⟨hpre,hroot,_⟩:=hv.input_facts s hs
      dsimp only
      rw [hpre]
      exact (built_spec s.witness.values trieFuel s.root _ hroot).2.1
  obtain ⟨u,hu,hctx,hpre,hvalue,houtput,huvalid⟩:=chosen_rebased_witness hs hr (by
    intro q hq
    rw [hkeys] at hq
    obtain ⟨r,_,rfl⟩:=List.mem_map.mp hq
    simp [keyBwState,accountKeyPath,nibbles]) hfinal
  refine ⟨writes,oldPost,mid,so,u,hu,hctx,hpre,hvalue,houtput,huvalid,hs,hkeys,hr,hfinal,hvalid,?_⟩
  simpa only [nativeReplayForest_pre] using forestOldInputs_all_bytes _ hvalid hwell 0

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
