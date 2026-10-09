import ZkFormal.NearV3.Candidates.PostMetadataPayloads
import ZkFormal.NearV3.Candidates.NativePostShaOk
import ZkFormal.NearV3.Rcpt.Candidates.NativeExecutionPayloads

namespace ZkFormal.NearV3.Candidates.NativeBoundPost
open NearSpec NearSpecV3 ZkFormal.Near Assembly Render Render.UpsGen Rcpt.Candidates Rcpt.Candidates.NodePostUpdate

/-- One accepted native execution supplies the concrete final old-record bytes,
valid rendered inputs and valid hash jobs. Structural UPS reconstruction is
retained explicitly; the old-record root is not confused with the final root. -/
theorem accepted {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (hc : checkD0a B0 cb wb=.ok ())
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (q : UseRequests) (he : q.edges.length<Algebra.P)
    (hb : q.bmaps.length<Algebra.P) (hu : q.windows.length<Algebra.P) :
    ∃writes,∃oldPost mid : PTrie,∃so : SchedOut,
      schedStep prims (m.ctx k) m.pre=.ok (mid,so) ∧
      SizedAccountRun m.pre writes oldPost ∧
      oldPost.upsert keyBwState so.state=some m.result.trie ∧
      let rs:=nativeReplayForest m steps oldPost writes
      let u:=forestOldInputs rs
      let ts:=m.pre::steps.map ImplicitStepV3.pre
      let vs:=initializeList 0 (forestNodes 0 0 0 ts)
      let es:=seedValuesFrom 0 (forestBytes ts)
      let cs:=StoreClassPartition.chain (CombinedStoreOccurrences.allOccurrences vs (NativeStoreProvenance.valueTau ts) es)
      let ns:=assignList q 0 (records u (ChainMetadata.assign cs 0 vs))
      let vals:=ChainMetadata.assignValues cs es
      NodeOk ns ∧ ValWf vals ∧
      ns.map (fun s=>s.v.ser true)=((rs.map ReplayTree.post).flatMap occs).map
        (fun t=>(nodeEnc t).map UInt8.toNat) ∧
      ZkFormal.Sha.MsgsOk (jobsToSha (nativeShaJobs ns vals)) := by
  obtain ⟨writes,oldPost,mid,so,hs,hr,hfinal,hvalid,hbytes⟩:=native_execution_payloads hm hv
  refine ⟨writes,oldPost,mid,so,hs,hr,hfinal,?_⟩
  have hinputs:=NativeExecutionPost.assigned_inputs hk hw hc (by decide) hm hv
    (forestOldInputs (nativeReplayForest m steps oldPost writes)) q he hb hu
  refine ⟨hinputs.1,hinputs.2,?_,NativePostShaOk.accepted hk hw hc hm hv _ q he hb hu⟩
  rw [PostMetadataPayloads.post_bytes]
  exact hbytes

end ZkFormal.NearV3.Candidates.NativeBoundPost
