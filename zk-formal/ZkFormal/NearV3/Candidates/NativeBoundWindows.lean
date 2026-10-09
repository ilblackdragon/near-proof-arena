import ZkFormal.NearV3.Candidates.NativePostWindowBinding

namespace ZkFormal.NearV3.Candidates.NativeBoundWindows
open NearSpec NearSpecV3 ZkFormal.Near Assembly Render Render.UpsGen Rcpt.Candidates Rcpt.Candidates.NodePostUpdate

/-- Actual accepted execution supplies physical UPB provider counts whose bytes
are the same chosen oldPost forest used by the native final-state reconstruction.
Reader inventory coverage remains a separate obligation. -/
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
      ZkFormal.Sha.MsgsOk (jobsToSha (nativeShaJobs ns vals)) ∧
      ∀clock pub msg,
        Air.tableBusCount SizeCount.nodeTable.interactions
          (TrieCountHeight.node ns pub) clock pub B_UPB false msg=
        (((ns.zip (List.range ns.length)).flatMap fun (s,n)=>
          (List.range (s.v.ser false).length).map fun p=>
            NativePostWindowBinding.nativeWindowKey ((rs.map ReplayTree.post).flatMap occs) n p s++
            [q.windows.count (NativePostWindowBinding.nativeWindowKey
              ((rs.map ReplayTree.post).flatMap occs) n p s)]).map Msg.toFp).count msg := by
  obtain ⟨writes,oldPost,mid,so,hs,hr,hfinal,hn,hvals,hbytes,hsha⟩:=
    NativeBoundPost.accepted hk hw hc hm hv q he hb hu
  refine ⟨writes,oldPost,mid,so,hs,hr,hfinal,hn,hvals,hbytes,hsha,?_⟩
  intro clock pub msg
  have hwindows:=NativePostWindowBinding.physical_windows q _ _ hn hbytes he hb hu clock pub msg
  simpa only [NativePostWindowBinding.assign_idempotent] using hwindows

end ZkFormal.NearV3.Candidates.NativeBoundWindows
