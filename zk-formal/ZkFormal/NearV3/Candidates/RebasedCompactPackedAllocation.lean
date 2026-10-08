import ZkFormal.NearV3.Candidates.NativeSourceByteBalance
import ZkFormal.NearV3.Rcpt.Candidates.NativeRebasedPhysicalBounds
import ZkFormal.NearV3.Assembly.ShaOwnedBatch
import ZkFormal.NearV3.Candidates.SchedulerPhysicalShaSplit
import ZkFormal.NearV3.Rcpt.Candidates.ChosenRebasedInstances

namespace ZkFormal.NearV3.Candidates.RebasedCompactPackedAllocation
open NearSpec NearSpecV3 ZkFormal.Near Assembly Render Render.UpsGen Rcpt.Candidates Rcpt.Candidates.NodePostUpdate

/-- The SAME native forest and rebased scheduler witnesses supply locally valid
compact UPS and packed SHA traces. Actual node/value/source/compact producers
leave only fresh codec values, sanity and receipt bytes as residual inventory. -/
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
      TableLocal Render.UpsRelay.compactTable (CompactHeight.trace insts) tu pub ∧
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
        Air.tableBusCount Render.UpsRelay.compactTable.interactions (CompactHeight.trace insts) tu pub B_BYTES true msg+
        ((Sha.Gen.expectedBytes (SchedulerShaSplit.freshJobs 0 us++schedulerSanityJobs 0 us++receipt)).map Msg.toFp).count msg) ∧
      (∀msg,PackedShaBins.unionCount bs pub (List.range 4) true B_DIGEST msg=
        ((Sha.Gen.expectedDigests (scheduler++native++receipt++source)).map Msg.toFp).count msg) := by
  have hd : checkD0 cb wb=.ok () := by
    have hh:=((relD0a_iff B0 cb wb).mpr hc).1
    unfold RelD0 acceptsD0 at hh
    split at hh <;> simp_all
  obtain ⟨_,_,_,_,_,hcount⟩:=checkD0_native_steps hk hw hd
  have hlen : steps.length≤31 := by
    have hh:=hv.length
    simp only [List.length_zip] at hh
    omega
  have hwell : ∀t∈m.pre::steps.map ImplicitStepV3.pre,t.wf=true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl|ht
    · rw [hm.pre];exact (built_spec _ trieFuel _ _ hm.root_length).2.1
    · obtain ⟨s,hs,rfl⟩:=List.mem_map.mp ht
      exact (hv.input_facts s hs).2.2
  obtain ⟨writes,oldPost,us,hr,hpairs,hpos,hlen,hgood,hpre,hout,hval,hforest,hpost⟩:=
    native_rebased_physical_bounds hk hw hc hm hv hlen hwell
  obtain ⟨insts,hinstLen,hinst⟩:=chosen_exact_instances hgood hpre hout baseI base
  have ha : ∀tau x I,us[tau]?=some x→insts[tau]?=some I→
      AllocatedNativeInstance us tau x I ∧ NativeShaFamily x I := by
    intro tau x I hx hI
    exact ⟨(hinst tau x I hx hI).1,(hinst tau x I hx hI).2.1⟩
  have hcompact:=SchedulerPhysicalShaSplit.allocated hinstLen hpos hlen ha hout tu pub
  let u:=forestOldInputs (nativeReplayForest m steps oldPost writes)
  have hinputs:=NativeExecutionPost.assigned_inputs hk hw hc (by decide) hm hv u q he hb hu
  have hnative:=NativePostShaOk.accepted hk hw hc hm hv u q he hb hu
  have hnativeRows:=NativePostShaBudget.accepted hk hw hc hm hv u q he hb hu
  have hschedRows:=schedulerBatch_rows us hlen (fun x hx=>(hgood x hx).1)
    (fun x hx=>(hgood x hx).2.2.1) hout hval
  obtain ⟨hsourceRows,hsourceMax,hsourceBytes⟩:=AcceptedSourceShaContract.accepted hc hprep hfile hraw
  have hschedBytes : ∀M∈schedulerShaJobs 0 us++schedulerSanityJobs 0 us,∀b∈M.bytes,b<256 := by
    intro M hM b hb
    rcases List.mem_append.mp hM with hM|hM
    · exact schedulerShaJobs_bytes 0 us M hM b hb
    · exact schedulerSanityJobs_bytes 0 us M hM b hb
  have hfour:=FourPackedSha.complete (schedulerShaJobs 0 us++schedulerSanityJobs 0 us) _ receipt
    (sourceShaMessages p.lists w.entries) hschedRows (by rw [jobsToSha_rows];exact hnativeRows)
    hReceiptRows hsourceRows hsourceMax (by
      intro M hM b hb
      simp only [List.mem_append] at hM
      rcases hM with ((hM|hM)|hM)|hM
      · exact hschedBytes M (List.mem_append.mpr hM) b hb
      · exact hnative.bytes M hM b hb
      · exact hReceiptBytes M hM b hb
      · exact hsourceBytes M hM b hb) pub
  refine ⟨writes,oldPost,us,insts,hr,hpairs,(fun x hx=>(hgood x hx).1),hinstLen,hcompact.1,hinputs.1,hinputs.2,?_,
    hfour.1,hfour.2.1,hfour.2.2.1,?_,hfour.2.2.2.2⟩
  · rw [PostMetadataPayloads.post_bytes]
    exact hpost
  · intro msg
    have hbytes:=NativeSourceByteBalance.producers hc hprep hfile hraw _ _ hinputs.1 hinputs.2 _ receipt
      _ tn tv pub msg (hfour.2.2.2.1 msg)
    have hs:=hcompact.2 msg
    dsimp only [u] at hbytes
    simp only [Sha.Gen.expectedBytes,List.flatMap_append,List.map_append,List.count_append] at hbytes hs ⊢
    omega

end ZkFormal.NearV3.Candidates.RebasedCompactPackedAllocation
