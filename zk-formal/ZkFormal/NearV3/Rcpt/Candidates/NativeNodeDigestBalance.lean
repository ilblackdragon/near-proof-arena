import ZkFormal.NearV3.Rcpt.Candidates.NativeDigestBoundJobs
import ZkFormal.NearV3.Rcpt.Candidates.NativeDigestPhysical

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Render Render.UpsGen Assembly

/-- Actual HEAD/node DIGEST consumption equals all concrete node SHA outputs,
plus exactly the remaining value-slot requests. No node occurrence is omitted
or contracted when equal byte strings repeat. -/
theorem native_node_digest_balance {k : WalkD0} {w : StateWitness} {m : MainExecutionV3}
    {steps : List ImplicitStepV3} {last : Bytes} (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    {oldPost : PTrie} {writes : List (List Nat×Bytes)} (hr : SizedAccountRun m.pre writes oldPost)
    (q : UseRequests) (cs : List Candidates.StoreDuplicateChain.Entry)
    (trh : Trace Fp) (th tn : Nat) (pub msg : List Fp) (keys : List ZkFormal.Near.Msg)
    (hhead : TableTraffic HeadV3.interactions trh th pub
      (headTraffic (assignHeadUses keys (forestWalkHeads 0 0
        ((nativeReplayForest m steps oldPost writes).map (fun r=>(r.pre,r.post)))))))
    (hn : NodeOk (assignList q 0 (records (forestOldInputs (nativeReplayForest m steps oldPost writes))
      (Candidates.ChainMetadata.assign cs 0 (initializeList 0
        (forestNodes 0 0 0 ((nativeReplayForest m steps oldPost writes).map ReplayTree.pre))))))) :
    let rs:=nativeReplayForest m steps oldPost writes
    let ss:=assignList q 0 (records (forestOldInputs rs)
      (Candidates.ChainMetadata.assign cs 0 (initializeList 0 (forestNodes 0 0 0 (rs.map ReplayTree.pre)))))
    tableBusCount HeadV3.interactions trh th pub B_DIGEST false msg+
      tableBusCount SizeCount.nodeTable.interactions (Candidates.TrieCountHeight.node ss pub) tn pub B_DIGEST false msg=
      ((Sha.Gen.expectedDigests (jobsToSha (nativeNodeShaJobsFrom 0 ss))).map Msg.toFp).count msg+
      ((ss.flatMap slotDigests).map Msg.toFp).count msg := by
  let rs:=nativeReplayForest m steps oldPost writes
  have hvalid : ∀r∈rs,r.Valid := by
    intro r hh
    simp only [rs,nativeReplayForest,List.mem_cons,List.mem_map] at hh
    rcases hh with rfl|⟨s,hs,rfl⟩
    · exact hr
    · exact SizedAccountRun.nil _
  have hwell : ∀r∈rs,r.pre.wf=true := by
    intro r hh
    simp only [rs,nativeReplayForest,List.mem_cons,List.mem_map] at hh
    rcases hh with rfl|⟨s,hs,rfl⟩
    · change m.pre.wf=true
      rw [hm.pre];exact (built_spec _ trieFuel _ _ hm.root_length).2.1
    · exact (hv.input_facts s hs).2.2
  have hj:=pipeline_node_job_digests rs hvalid hwell q cs (fun s hs=>hn.wf.wf s hs)
  have hp:=(native_replay_digest_partition hm hv hr).map Msg.toFp
  have hc:=hp.count_eq msg
  simp only [List.map_append,List.count_append] at hc
  dsimp only
  rw [(hhead B_DIGEST msg).2,physical_node_digest_split _ hn tn pub msg,hj,
    pipeline_child_digests]
  have hh : headRecvs (assignHeadUses keys (forestWalkHeads 0 0 (rs.map (fun r=>(r.pre,r.post))))) B_DIGEST=
      headRecvs (forestWalkHeads 0 0 (rs.map (fun r=>(r.pre,r.post)))) B_DIGEST := by
    simp only [headRecvs,ite_true,assignHeadUses,List.flatMap_map]
  change _+(_+_)=_+_
  simp only [headTraffic]
  rw [hh]
  dsimp only [rs] at *
  omega

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
