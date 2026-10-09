import ZkFormal.NearV3.Rcpt.Candidates.NativeForestInputs

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Render.UpsGen Assembly

/-- The main tree carries receipt writes; implicit transitions perform no
receipt writes and therefore retain their original old-record trees. -/
def nativeReplayForest (m : MainExecutionV3) (steps : List ImplicitStepV3)
    (oldPost : PTrie) (writes : List (List Nat×Bytes)) : List ReplayTree :=
  ⟨m.pre,oldPost,writes⟩::steps.map (fun s=>⟨s.pre,s.pre,[]⟩)

theorem nativeReplayForest_pre (m : MainExecutionV3) (steps : List ImplicitStepV3)
    (oldPost : PTrie) (writes : List (List Nat×Bytes)) :
    (nativeReplayForest m steps oldPost writes).map ReplayTree.pre=m.pre::steps.map ImplicitStepV3.pre := by
  simp [nativeReplayForest,List.map_map,Function.comp_def]

/-- Actual native execution supplies the complete same-forest post-payload
constructor; its original node serializations and structural final root use the
same receipt replay and the same scheduler result. -/
theorem native_execution_payloads {k : WalkD0} {w : StateWitness} {m : MainExecutionV3}
    {steps : List ImplicitStepV3} {last : Bytes} (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last) :
    ∃writes,∃oldPost mid : PTrie,∃so : SchedOut,
      schedStep prims (m.ctx k) m.pre=.ok (mid,so) ∧
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
  refine ⟨writes,oldPost,mid,so,hs,hr,hfinal,hvalid,?_⟩
  simpa only [nativeReplayForest_pre] using forestOldInputs_all_bytes _ hvalid hwell 0

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
