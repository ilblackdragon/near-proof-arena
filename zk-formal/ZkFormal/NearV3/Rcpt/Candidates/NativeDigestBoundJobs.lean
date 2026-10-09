import ZkFormal.NearV3.Rcpt.Candidates.NativeDigestJobs
import ZkFormal.NearV3.Rcpt.Candidates.NativeDigestMetadata
import ZkFormal.NearV3.Rcpt.Candidates.NativePostShaLength

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen Assembly

theorem post_bindings_of_map {u : Inputs} {n : Nat} {ss : List NodeS3} {ts : List PTrie}
    (he : ss.map (fun s=>s.v.ser true)=ts.map (fun t=>(nodeEnc t).map UInt8.toNat))
    (hc : ChildPayloads u n ts) : postChildBindings u n ss := by
  intro i s hs
  have hl:=congrArg List.length he
  simp only [List.length_map] at hl
  have hi : i<ts.length:=by have hh:=(List.getElem?_eq_some_iff.mp hs).1;omega
  have ht : ts[i]?=some ts[i]:=List.getElem?_eq_getElem hi
  have hh:=congrArg (fun xs=>xs[i]?) he
  simp only [List.getElem?_map,hs,ht,Option.map_some,Option.some.injEq] at hh
  rw [hc i ts[i] ht]
  exact hh

/-- Concrete replay arrays bind both SHA preimages on the same final views;
node metadata may differ, but the actual NodeV payload is retained exactly. -/
theorem replay_node_job_digests (rs : List ReplayTree) (hv : ∀r∈rs,r.Valid)
    (hw : ∀r∈rs,r.pre.wf=true) (ss : List NodeS3)
    (he : ss.map NodeS3.v=(records (forestOldInputs rs)
      (forestNodes 0 0 0 (rs.map ReplayTree.pre))).map NodeS3.v)
    (hn : ∀s∈ss,s.v.wf) :
    Sha.Gen.expectedDigests (jobsToSha (nativeNodeShaJobsFrom 0 ss))=
      (forestOccurrenceOwners 0 (rs.map ReplayTree.pre)).flatMap (ownerDigests (forestOldInputs rs)) := by
  have hb : ∀t∈rs.map ReplayTree.pre,t.wf=true := by
    intro t ht;obtain ⟨r,hr,rfl⟩:=List.mem_map.mp ht;exact hw r hr
  have hpre:=congrArg (List.map (NodeV3.ser false)) he
  simp only [List.map_map,Function.comp_def] at hpre
  have hp:=records_pre (forestOldInputs rs) (forestNodes 0 0 0 (rs.map ReplayTree.pre))
  have hpre':=hpre.trans (hp.trans (forestNodes_bytes false 0 0 0 _ hb))
  have hpost:=congrArg (List.map (NodeV3.ser true)) he
  simp only [List.map_map,Function.comp_def] at hpost
  have hpost':=hpost.trans (forestOldInputs_all_bytes rs hv hw 0)
  rw [forestOccurrenceOwners_indexed]
  apply node_jobs_digests _ _ _ _ hpre'
  · exact post_bindings_of_map hpost' (forestOldInputs_children rs)
  · intro s hs;exact node_post_length s.v (hn s hs)
  · intro t ht
    obtain ⟨r,hr,ht⟩:=List.mem_flatMap.mp ht
    exact occs_isNode r t ht

/-- Applied to the actual counter/duplicate/post-byte pipeline, without a
caller-supplied serialization equality. -/
theorem pipeline_node_job_digests (rs : List ReplayTree) (hv : ∀r∈rs,r.Valid)
    (hw : ∀r∈rs,r.pre.wf=true) (q : UseRequests)
    (cs : List Candidates.StoreDuplicateChain.Entry)
    (hn : ∀s∈assignList q 0 (records (forestOldInputs rs)
      (Candidates.ChainMetadata.assign cs 0 (initializeList 0 (forestNodes 0 0 0 (rs.map ReplayTree.pre))))),s.v.wf) :
    let ss:=assignList q 0 (records (forestOldInputs rs)
      (Candidates.ChainMetadata.assign cs 0 (initializeList 0 (forestNodes 0 0 0 (rs.map ReplayTree.pre)))))
    Sha.Gen.expectedDigests (jobsToSha (nativeNodeShaJobsFrom 0 ss))=
      (forestOccurrenceOwners 0 (rs.map ReplayTree.pre)).flatMap (ownerDigests (forestOldInputs rs)) := by
  apply replay_node_job_digests rs hv hw _ ?_ hn
  exact (usage_node_views q _ 0).trans (records_node_views _
    ((chain_node_views cs _ 0).trans (initialize_node_views _ 0)))

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
