import ZkFormal.NearV3.Candidates.AcceptedSourceShaContract

namespace ZkFormal.NearV3.Candidates.NativeSourcePackedAllocation
open NearSpec NearSpecV3 ZkFormal.Near Assembly Render Render.UpsGen Rcpt.Candidates Rcpt.Candidates.NodePostUpdate

/-- The source and native allocator contracts both come from the same accepted
witness. Only scheduler and receipt job contracts remain external here. -/
theorem accepted {cb wb raw : Bytes} {codes : List Bytes} {hint : Hint} {p : Prep} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (hc : checkD0a B0 cb wb=.ok ())
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (q : UseRequests) (he : q.edges.length<Algebra.P)
    (hb : q.bmaps.length<Algebra.P) (hu : q.windows.length<Algebra.P)
    (hprep : prepD0 cb hint=.ok p)
    (hfile : decodeWitnessFile wb=.ok (raw,codes)) (hraw : decodeStateWitness raw=.ok w)
    (scheduler receipt : List Sha.Gen.Msg)
    (hSchedRows : (Sha.Gen.honestRows scheduler).length≤1663260)
    (hReceiptRows : (Sha.Gen.honestRows receipt).length≤1373299)
    (hOtherBytes : ∀M∈scheduler++receipt,∀b∈M.bytes,b<256)
    (pub : List Algebra.Fp) :
    let source:=sourceShaMessages p.lists w.entries
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
  obtain ⟨hrows,hmax,hbytes⟩:=AcceptedSourceShaContract.accepted hc hprep hfile hraw
  apply NativePackedAllocation.accepted hk hw hc hm hv q he hb hu scheduler receipt
    (sourceShaMessages p.lists w.entries) hSchedRows hReceiptRows hrows hmax ?_ pub
  intro M hM b hb
  rcases List.mem_append.mp hM with hM|hM
  · exact hOtherBytes M hM b hb
  · exact hbytes M hM b hb

end ZkFormal.NearV3.Candidates.NativeSourcePackedAllocation
