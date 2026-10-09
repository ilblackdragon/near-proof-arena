import ZkFormal.NearV3.Rcpt.Candidates.ReplayHeadPhysical
import ZkFormal.NearV3.Rcpt.Candidates.AcceptedRebasedOrigins

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Render Render.UpsGen Assembly

/-- Payload-correct physical HEAD witness for the SAME chosen receipt replay.
Every digest width, ID/length bound, capacity and request count is derived. -/
theorem accepted_replay_head {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (h : checkD0a B0 cb wb=.ok ())
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    {oldPost : PTrie} {writes : List (List Nat×Bytes)} (hr : SizedAccountRun m.pre writes oldPost)
    (keys : List ZkFormal.Near.Msg) (hkeys : keys.length<Algebra.P) (t : Nat) (pub : List Fp) :
    let hs:=assignHeadUses keys (forestWalkHeads 0 0 ((nativeReplayForest m steps oldPost writes).map (fun r=>(r.pre,r.post))))
    HeadOk hs ∧ TableLocal {HeadV3.table with maxLog:=22} (replayHeadTrace hs) t pub ∧
      TableTraffic HeadV3.interactions (replayHeadTrace hs) t pub (headTraffic hs) := by
  have hc : checkD0 cb wb=.ok () := by
    have hh:=((relD0a_iff B0 cb wb).mpr h).1
    unfold RelD0 acceptsD0 at hh
    split at hh <;> simp_all
  obtain ⟨_,_,_,_,_,hcount⟩:=checkD0_native_steps hk hw hc
  have hlen : steps.length≤31 := by
    have hs:=hv.length
    simp only [List.length_zip] at hs
    omega
  let rs:=nativeReplayForest m steps oldPost writes
  have hrs : ∀r∈rs,r.Valid := by
    intro r hm
    simp only [rs,nativeReplayForest,List.mem_cons,List.mem_map] at hm
    rcases hm with rfl|⟨s,hs,rfl⟩
    · exact hr
    · exact SizedAccountRun.nil _
  have hwell : ∀r∈rs,r.pre.wf=true := by
    intro r hmem
    simp only [rs,nativeReplayForest,List.mem_cons,List.mem_map] at hmem
    rcases hmem with rfl|⟨s,hs,rfl⟩
    · change m.pre.wf=true
      rw [hm.pre];exact (built_spec _ trieFuel _ _ hm.root_length).2.1
    · exact (hv.input_facts s hs).2.2
  have hbytes : preBytes (rs.map ReplayTree.pre)≤2000000 := by
    simpa only [rs,nativeReplayForest_pre,NearSpecV3.B0] using checkD0a_preBytes hk hw h hm hv
  have hok:=assigned_replay_head_ok rs hrs hwell hbytes
    (by simp [rs,nativeReplayForest])
    (by simp only [rs,nativeReplayForest,List.length_cons,List.length_map];omega) keys hkeys
  exact ⟨hok,replayHeadTrace_complete _ hok t pub⟩

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
