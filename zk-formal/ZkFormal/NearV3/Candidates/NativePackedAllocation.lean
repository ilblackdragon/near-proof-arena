import ZkFormal.NearV3.Candidates.NativeBoundPost
import ZkFormal.NearV3.Candidates.FourPackedSha

namespace ZkFormal.NearV3.Candidates.NativePackedAllocation
open NearSpec NearSpecV3 ZkFormal.Near Assembly Render Render.UpsGen Rcpt.Candidates Rcpt.Candidates.NodePostUpdate

/-- The accepted execution's concrete native payloads enter the executable
four-bin packed SHA construction. Other family byte/budget contracts remain
explicit until their same-execution physical producers are integrated. -/
theorem accepted {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (hc : checkD0a B0 cb wb=.ok ())
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (q : UseRequests) (he : q.edges.length<Algebra.P)
    (hb : q.bmaps.length<Algebra.P) (hu : q.windows.length<Algebra.P)
    (scheduler receipt source : List Sha.Gen.Msg)
    (hSchedRows : (Sha.Gen.honestRows scheduler).length≤1663260)
    (hReceiptRows : (Sha.Gen.honestRows receipt).length≤1373299)
    (hSourceRows : (Sha.Gen.honestRows source).length≤8932712)
    (hSourceMax : ∀M∈source,(Sha.Gen.msgRows M).length≤35)
    (hOtherBytes : ∀M∈scheduler++receipt++source,∀b∈M.bytes,b<256)
    (pub : List Algebra.Fp) :
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
      let native:=jobsToSha (nativeShaJobs ns vals)
      let bs:=FourPackedSha.bins scheduler native receipt source
      bs.length=4 ∧ (∀t,(PackedShaBins.trace bs).log t=22) ∧
      (∀t∈List.range 4,TableLocal (ShaCarryKinds.table B_BYTES B_DIGEST) (PackedShaBins.trace bs) t pub) ∧
      (∀msg,PackedShaBins.unionCount bs pub (List.range 4) false B_BYTES msg=
        ((Sha.Gen.expectedBytes (scheduler++native++receipt++source)).map Msg.toFp).count msg) ∧
      (∀msg,PackedShaBins.unionCount bs pub (List.range 4) true B_DIGEST msg=
        ((Sha.Gen.expectedDigests (scheduler++native++receipt++source)).map Msg.toFp).count msg) := by
  obtain ⟨writes,oldPost,mid,so,hs,hr,hfinal,hn,hvals,hbytes,hsha⟩:=
    NativeBoundPost.accepted hk hw hc hm hv q he hb hu
  refine ⟨writes,oldPost,mid,so,hs,hr,hfinal,hn,hvals,hbytes,?_⟩
  apply FourPackedSha.complete _ _ _ _ hSchedRows _ hReceiptRows hSourceRows hSourceMax _ pub
  · rw [jobsToSha_rows]
    exact NativePostShaBudget.accepted hk hw hc hm hv _ q he hb hu
  · intro M hM b hbyte
    simp only [List.mem_append] at hM
    rcases hM with ((hM|hM)|hM)|hM
    · exact hOtherBytes M (by simp only [List.mem_append];exact Or.inl (Or.inl hM)) b hbyte
    · exact hsha.bytes M hM b hbyte
    · exact hOtherBytes M (by simp only [List.mem_append];exact Or.inl (Or.inr hM)) b hbyte
    · exact hOtherBytes M (by simp only [List.mem_append];exact Or.inr hM) b hbyte

end ZkFormal.NearV3.Candidates.NativePackedAllocation
