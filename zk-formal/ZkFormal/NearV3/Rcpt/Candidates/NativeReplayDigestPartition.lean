import ZkFormal.NearV3.Rcpt.Candidates.NativeDigestHeads
import ZkFormal.NearV3.Rcpt.Candidates.NativeDigestRoots

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Render.UpsGen Assembly

theorem replay_digest_partition (rs : List ReplayTree) (hv : ∀r∈rs,r.Valid)
    (hn : ∀r∈rs,isNode r.pre=true) (tau : Nat) :
    (headRecvs (forestWalkHeads tau 0 (rs.map (fun r=>(r.pre,r.post)))) B_DIGEST++
      (records (forestOldInputs rs) (forestNodes tau 0 0 (rs.map ReplayTree.pre))).flatMap childDigests).Perm
      ((forestOccurrenceOwners 0 (rs.map ReplayTree.pre)).flatMap (ownerDigests (forestOldInputs rs))) := by
  have hh:=forest_head_digest_records (forestOldInputs rs) (rs.map (fun r=>(r.pre,r.post))) tau 0
    (by intro p hp;obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hp;exact (hv r hr).forget.skeleton)
    (by intro p hp;obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hp;exact hn r hr)
    (by simpa only [List.map_map,Function.comp_def] using forestOldInputs_children rs)
  simp only [List.map_map,Function.comp_def] at hh
  rw [hh]
  exact forest_digest_partition (forestOldInputs rs) (rs.map ReplayTree.pre) tau 0 0

/-- Same native receipt replay and implicit trace: no independent root or
child-payload validity premise remains in occurrence ownership. -/
theorem native_replay_digest_partition {k : WalkD0} {w : StateWitness} {m : MainExecutionV3}
    {steps : List ImplicitStepV3} {last : Bytes} (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    {oldPost : PTrie} {writes : List (List Nat×Bytes)} (hr : SizedAccountRun m.pre writes oldPost) :
    let rs:=nativeReplayForest m steps oldPost writes
    (headRecvs (forestWalkHeads 0 0 (rs.map (fun r=>(r.pre,r.post)))) B_DIGEST++
      (records (forestOldInputs rs) (forestNodes 0 0 0 (rs.map ReplayTree.pre))).flatMap childDigests).Perm
      ((forestOccurrenceOwners 0 (rs.map ReplayTree.pre)).flatMap (ownerDigests (forestOldInputs rs))) := by
  apply replay_digest_partition
  · intro r hmem
    simp only [nativeReplayForest,List.mem_cons,List.mem_map] at hmem
    rcases hmem with rfl|⟨s,hs,rfl⟩
    · exact hr
    · exact SizedAccountRun.nil _
  · exact replay_roots_revealed hm hv oldPost writes

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
