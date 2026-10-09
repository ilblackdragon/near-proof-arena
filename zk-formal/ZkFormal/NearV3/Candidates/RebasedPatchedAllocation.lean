import ZkFormal.NearV3.Candidates.RebasedCompactPackedAllocation
import ZkFormal.NearV3.Candidates.PatchedCompactAllocation

namespace ZkFormal.NearV3.Candidates.RebasedPatchedAllocation
open NearSpec NearSpecV3 ZkFormal.Near Assembly Render Render.UpsGen Rcpt.Candidates Rcpt.Candidates.NodePostUpdate

/-- The accepted native allocation uses a single ranked compact trace, preserving
its full SHA byte composition. Provider coverage remains a separate obligation. -/
theorem accepted {cb wb raw : Bytes} {codes : List Bytes} {hint : Hint} {p : Prep} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (hc : checkD0a B0 cb wb=.ok ())
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (q : UseRequests) (he : q.edges.length<Algebra.P)
    (hb : q.bmaps.length<Algebra.P) (hu : q.windows.length<Algebra.P)
    (hprep : prepD0 cb hint=.ok p)
    (hfile : decodeWitnessFile wb=.ok (raw,codes)) (hraw : decodeStateWitness raw=.ok w)
    (receipt : List Sha.Gen.Msg)
    (hReceiptRows : (Sha.Gen.honestRows receipt).length≤1373299)
    (hReceiptBytes : ∀M∈receipt,∀b∈M.bytes,b<256)
    (baseI : Nat→UpsInst) (base : Nat→Nat→UpsPartI)
    (tn tv tu : Nat) (pub : List Algebra.Fp) :
    let source:=sourceShaMessages p.lists w.entries
    ∃writes,∃oldPost : PTrie,∃us : List SchedulerUpsertWitness,∃insts : List UpsInst,
      SizedAccountRun m.pre writes oldPost ∧
      us.map (fun u=>(u.pre,u.run.output))=(oldPost,m.result.trie)::steps.map (fun s=>(s.pre,s.post)) ∧
      (∀u∈us,u.Valid) ∧ insts.length=us.length ∧
      TableLocal Render.UpsRelay.compactTable (patchWindowCounters (CompactHeight.trace insts) tu (physicalWindowRank (CompactHeight.trace insts) tu)) tu pub ∧
      let scheduler:=schedulerShaJobs 0 us++schedulerSanityJobs 0 us 
      
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
        Air.tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node ns pub) tn pub B_BYTES true msg+
        Air.tableBusCount SizeCount.valTable.interactions (TrieCountHeight.value vals pub) tv pub B_BYTES true msg+
        SourceLog22.boundaryCount (NativeSourceFour.trace (DedupCompile.blocks p.lists w.entries)
          (sourceRepeated p.lists)) 0 1 2 3 pub B_BYTES true msg+
        Air.tableBusCount Render.UpsRelay.compactTable.interactions (patchWindowCounters (CompactHeight.trace insts) tu (physicalWindowRank (CompactHeight.trace insts) tu)) tu pub B_BYTES true msg+
        ((Sha.Gen.expectedBytes (SchedulerShaSplit.freshJobs 0 us++schedulerSanityJobs 0 us++receipt)).map Msg.toFp).count msg) ∧
      (∀msg,PackedShaBins.unionCount bs pub (List.range 4) true B_DIGEST msg=
        ((Sha.Gen.expectedDigests (scheduler++native++receipt++source)).map Msg.toFp).count msg) := by
  obtain ⟨writes,oldPost,us,insts,hr,hpairs,hvalid,hinstLen,hlocal,hnode,hval,hser,hcount,hclock,hsha,hbytes,hdig⟩:=
    RebasedCompactPackedAllocation.accepted hk hw hc hm hv q he hb hu hprep hfile hraw
      receipt hReceiptRows hReceiptBytes baseI base tn tv tu pub
  refine ⟨writes,oldPost,us,insts,hr,hpairs,hvalid,hinstLen,
    patchWindowCounters_local hlocal _,hnode,hval,hser,hcount,hclock,hsha,?_,hdig⟩
  intro msg
  rw [WindowPatchOtherTraffic.count hlocal _ B_BYTES (by decide)]
  exact hbytes msg

end ZkFormal.NearV3.Candidates.RebasedPatchedAllocation
