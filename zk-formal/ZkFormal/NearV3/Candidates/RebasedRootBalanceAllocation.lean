import ZkFormal.NearV3.Rcpt.Candidates.PreparedRootChain
import ZkFormal.NearV3.Rcpt.Candidates.NativeRootBalance
import ZkFormal.NearV3.Rcpt.Candidates.NativeRootHeader
import ZkFormal.NearV3.Rcpt.Candidates.NativeMidrootBalance
import ZkFormal.NearV3.Rcpt.Candidates.AcceptedReplayHead
import ZkFormal.NearV3.Candidates.PackedShaFacts
import ZkFormal.NearV3.Rcpt.Candidates.AcceptedReplaySharedBalance
import ZkFormal.NearV3.Candidates.PhysicalWindowRequests
import ZkFormal.NearV3.Candidates.WindowPatchOtherTraffic
import ZkFormal.NearV3.Candidates.NativeSourceByteBalance
import ZkFormal.NearV3.Rcpt.Candidates.NativeRebasedPhysicalBounds
import ZkFormal.NearV3.Assembly.ShaOwnedBatch
import ZkFormal.NearV3.Candidates.SchedulerPhysicalShaSplit
import ZkFormal.NearV3.Rcpt.Candidates.ChosenRebasedInstances

namespace ZkFormal.NearV3.Candidates.RebasedRootBalanceAllocation
open NearSpec NearSpecV3 ZkFormal.Near Assembly Render Render.UpsGen Rcpt.Candidates Rcpt.Candidates.NodePostUpdate
open Render.UpsRelay

open ZkFormal.Air (tableBusCount)
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000

/-- SAME accepted native allocation and actual query walks choose shared walk
prefixes and EDGE/BMAP requests. Full UPB/MIDROOT conservation, native indexed ROOT outputs and endorsed native
endpoints, and four packed SHA tables
use these same objects. Correct replay HEAD is rendered at log22; fresh codec/sanity/receipt
byte producers remain residual. No complete prover claim. -/
theorem accepted {cb wb raw : Bytes} {codes : List Bytes} {hint : Hint} {p : Prep} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (hc : checkD0a B0 cb wb=.ok ())
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (resolve : Qv.Candidates.CombinedWalkGen.Resolve) (tw : Nat)
    (hprep : prepD0 cb hint=.ok p)
    (hfile : decodeWitnessFile wb=.ok (raw,codes)) (hraw : decodeStateWitness raw=.ok w)
    (receipt : List Sha.Gen.Msg)
    (hReceiptRows : (Sha.Gen.honestRows receipt).length≤1373299)
    (hReceiptBytes : ∀M∈receipt,∀b∈M.bytes,b<256)
    (baseI : Nat→UpsInst) (base : Nat→Nat→UpsPartI)
    (th tn tv tu : Nat) (pub : List Algebra.Fp) :
    let source:=sourceShaMessages p.lists w.entries
    ∃writes,∃oldPost : PTrie,∃us : List SchedulerUpsertWitness,∃rawInsts : List UpsInst,
    ∃v : Qv.MainValues,∃ws : List WalkR,
      v.Valid ∧ v.Reads m.pre m.pre m.pre ∧
      nativeQueryWalks ((m.pre,m.result.trie)::steps.map (fun s=>(s.pre,s.post)))
        (allLookupQueries (appliedReceipts k w) m.pre v (steps.map ImplicitStepV3.pre) resolve)=some ws ∧
      TableLocal {WalkV3.table with maxLog:=22} (nativeWalkTrace (rankWalks [] ws)) tw pub ∧
      TableTraffic WalkV3.interactions (nativeWalkTrace (rankWalks [] ws)) tw pub (walkTraffic3 (rankWalks [] ws)) ∧
      let insts:=physicalPrefixUps (ws.flatMap (·.steps)) rawInsts
      let edges:=walkEdgeKeys (ws++upsWalkInventory rawInsts)
      let bmaps:=walkBmapKeys (ws++upsWalkInventory rawInsts)
      let q : UseRequests:=⟨edges,bmaps,PhysicalWindowRequests.keys (CompactHeight.trace insts) tu⟩
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
      TableLocal SizeCount.nodeTable (TrieCountHeight.node ns pub) tn pub ∧
      (∀msg,Air.tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node ns pub) tn pub B_UPB true msg+
        Air.tableBusCount Render.UpsRelay.compactTable.interactions (patchWindowCounters (CompactHeight.trace insts) tu (physicalWindowRank (CompactHeight.trace insts) tu)) tu pub B_UPB true msg=
        Air.tableBusCount Render.UpsRelay.compactTable.interactions (patchWindowCounters (CompactHeight.trace insts) tu (physicalWindowRank (CompactHeight.trace insts) tu)) tu pub B_UPB false msg+
        Air.tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node ns pub) tn pub B_UPB false msg) ∧
      (let nodeTrace:=TrieCountHeight.node ns pub
       let upsTrace:=patchWindowCounters (CompactHeight.trace insts) tu (physicalWindowRank (CompactHeight.trace insts) tu)
       let hs:=assignHeadUses edges (forestWalkHeads 0 0 ((nativeReplayForest m steps oldPost writes).map (fun r=>(r.pre,r.post))))
       let trh:=replayHeadTrace hs
       TableLocal {HeadV3.table with maxLog:=22} trh th pub ∧
       TableTraffic HeadV3.interactions trh th pub (headTraffic hs) ∧
      ∀msg,
        tableBusCount HeadV3.interactions trh th pub B_EDGE true msg+
        tableBusCount SizeCount.nodeTable.interactions nodeTrace tn pub B_EDGE true msg+
        tableBusCount WalkV3.interactions (nativeWalkTrace (rankWalks [] ws)) tw pub B_EDGE true msg+
        tableBusCount Render.UpsRelay.compactTable.interactions upsTrace tu pub B_EDGE true msg=
        tableBusCount HeadV3.interactions trh th pub B_EDGE false msg+
        tableBusCount SizeCount.nodeTable.interactions nodeTrace tn pub B_EDGE false msg+
        tableBusCount WalkV3.interactions (nativeWalkTrace (rankWalks [] ws)) tw pub B_EDGE false msg+
        tableBusCount Render.UpsRelay.compactTable.interactions upsTrace tu pub B_EDGE false msg ∧
        tableBusCount SizeCount.nodeTable.interactions nodeTrace tn pub B_BMAP true msg+
        tableBusCount WalkV3.interactions (nativeWalkTrace (rankWalks [] ws)) tw pub B_BMAP true msg+
        tableBusCount Render.UpsRelay.compactTable.interactions upsTrace tu pub B_BMAP true msg=
        tableBusCount SizeCount.nodeTable.interactions nodeTrace tn pub B_BMAP false msg+
        tableBusCount WalkV3.interactions (nativeWalkTrace (rankWalks [] ws)) tw pub B_BMAP false msg+
        tableBusCount Render.UpsRelay.compactTable.interactions upsTrace tu pub B_BMAP false msg) ∧
      (let hs:=assignHeadUses edges (forestWalkHeads 0 0 ((nativeReplayForest m steps oldPost writes).map (fun r=>(r.pre,r.post))))
       let trh:=replayHeadTrace hs
       let tru:=patchWindowCounters (CompactHeight.trace insts) tu (physicalWindowRank (CompactHeight.trace insts) tu)
       ∀msg,tableBusCount HeadV3.interactions trh th pub B_MIDROOT true msg+
         tableBusCount Render.UpsRelay.compactTable.interactions tru tu pub B_MIDROOT true msg=
         tableBusCount HeadV3.interactions trh th pub B_MIDROOT false msg+
         tableBusCount Render.UpsRelay.compactTable.interactions tru tu pub B_MIDROOT false msg) ∧
      (let tru:=patchWindowCounters (CompactHeight.trace insts) tu (physicalWindowRank (CompactHeight.trace insts) tu)
       ∀msg,tableBusCount Render.UpsRelay.compactTable.interactions tru tu pub B_ROOT true msg=
         ((nativeRootRecords 0 (m.result.trie::steps.map ImplicitStepV3.post)).map Msg.toFp).count msg) ∧
      (let hs:=assignHeadUses edges (forestWalkHeads 0 0 ((nativeReplayForest m steps oldPost writes).map (fun r=>(r.pre,r.post))))
       let trh:=replayHeadTrace hs
       let tru:=patchWindowCounters (CompactHeight.trace insts) tu (physicalWindowRank (CompactHeight.trace insts) tu)
       ∀msg,([Msg.toFp ([0]++p.hdr.prevStateRoot.map UInt8.toNat)]).count msg+
         tableBusCount HeadV3.interactions trh th pub B_ROOT true msg+
         tableBusCount Render.UpsRelay.compactTable.interactions tru tu pub B_ROOT true msg=
         tableBusCount HeadV3.interactions trh th pub B_ROOT false msg+
         tableBusCount Render.UpsRelay.compactTable.interactions tru tu pub B_ROOT false msg+
         ([Msg.toFp ([p.hdr.K+1]++p.hdr.postStateRoot.map UInt8.toNat)]).count msg) ∧
      last=k.H.prevStateRoot ∧
      (([0]++k.slotB2.prevStateRoot.map UInt8.toNat)::
        nativeRootRecords 0 (m.result.trie::steps.map ImplicitStepV3.post)=
        nativeInputRoots 0 (m.pre::steps.map ImplicitStepV3.pre)++
          [[steps.length+1]++k.H.prevStateRoot.map UInt8.toNat]) ∧
      ns.map (fun s=>s.v.ser true)=((rs.map ReplayTree.post).flatMap occs).map
        (fun t=>(nodeEnc t).map UInt8.toNat) ∧
      let native:=jobsToSha (nativeShaJobs ns vals)
      let bs:=FourPackedSha.bins scheduler native receipt source
      ShaFacts (PackedShaBins.unionCount bs pub (List.range 4) true)
        (PackedShaBins.unionCount bs pub (List.range 4) false) ∧
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
  obtain ⟨writes,oldPost,us,rawInsts,v,ws,hvvalid,hvreads,hws,hwlocal,hwtraffic,he,hb,hr,hpairs,hpos,hlen,hgood,hpre,hout,hval,hcount,hinst,hforest,hpost,hcovere,hcoverb,hbalance⟩:=
    accepted_replay_shared_balance hk hw hc hm hv resolve tw pub baseI base
  let previous:=ws.flatMap (·.steps)
  let edges:=walkEdgeKeys (ws++upsWalkInventory rawInsts)
  let bmaps:=walkBmapKeys (ws++upsWalkInventory rawInsts)
  let insts:=physicalPrefixUps previous rawInsts
  have hmeta:=physicalPrefixUps_origins (fun tau u I hu hI=>by
    obtain ⟨a,sha,ex,ci,dispatch,root,hroot,origin⟩:=hinst tau u I hu hI
    exact ⟨a,sha,root,hroot,origin⟩) previous
  have hinstLen : insts.length=us.length:=hmeta.1.trans hcount
  have ha : ∀tau x I,us[tau]?=some x→insts[tau]?=some I→
      AllocatedNativeInstance us tau x I ∧ NativeShaFamily x I := by
    intro tau x I hx hI
    exact ⟨(hmeta.2 tau x I hx hI).1,(hmeta.2 tau x I hx hI).2.1⟩
  have hhead:=accepted_replay_head hk hw hc hm hv hr edges he th pub
  have hcompact:=SchedulerPhysicalShaSplit.allocated hinstLen hpos hlen ha hout tu pub
  have hpreEq : us.map SchedulerUpsertWitness.pre=
      (nativeReplayForest m steps oldPost writes).map ReplayTree.post := by
    have hh:=congrArg (List.map Prod.fst) hpairs
    simpa [nativeReplayForest,List.map_map,Function.comp_def] using hh
  have hcap : compactR insts+1≤2^22 := by
    rw [compact_rows_exact hinstLen (fun tau u I hu hI=>(ha tau u I hu hI).1)]
    exact compact_rows_fit hlen hout
  have hmid:=native_midroot_balance (nativeReplayForest m steps oldPost writes) us rawInsts
    hforest hpreEq hcount (fun u hu=>(hgood u hu).2.1)
    (fun tau u I hu hI=>by
      obtain ⟨a,sha,ex,ci,dispatch,root,hroot,origin⟩:=hinst tau u I hu hI
      exact ⟨a,root,hroot,origin⟩) previous edges (by change compactR insts≤2^22;omega)
    _ th tu pub hhead.2.2 hcompact.1 (physicalWindowRank (CompactHeight.trace insts) tu)
  have hc0 : checkD0 cb wb=.ok () := by
    unfold checkD0a at hc
    obtain ⟨u,hu,_⟩:=ReexecV3D0.bind_ok' hc
    cases u;exact hu
  have hlast:=accepted_last_root hk hw hc0 hm hv
  have hchain:=accepted_root_chain hk hw hc0 hm hv
  have hpostLen : ∀I∈rawInsts,I.post.length=32 := by
    intro I hI
    obtain ⟨i,hib,he⟩:=List.mem_iff_getElem.mp hI
    have hui : i<us.length:=by omega
    have hi:=hinst i us[i] I (by simp [hui]) (by simp [hib,he])
    rw [hi.1.2.2.1,List.length_map]
    have hvu:=(hgood us[i] (List.getElem_mem hui)).1
    exact traceUpsert_output_hash_length hvu.1
  have houtputs : us.map (fun u=>u.run.output)=m.result.trie::steps.map ImplicitStepV3.post := by
    have hh:=congrArg (List.map Prod.snd) hpairs
    simpa only [List.map_map,List.map_cons,Function.comp_def] using hh
  have hroots:=allocated_root_records us rawInsts hcount (fun tau u I hu hI=>(hinst tau u I hu hI).1)
  rw [houtputs] at hroots
  have hroot : ∀msg,tableBusCount Render.UpsRelay.compactTable.interactions
      (patchWindowCounters (CompactHeight.trace insts) tu (physicalWindowRank (CompactHeight.trace insts) tu)) tu pub B_ROOT true msg=
      ((nativeRootRecords 0 (m.result.trie::steps.map ImplicitStepV3.post)).map Msg.toFp).count msg := by
    intro msg
    rw [compact_patched_root_send previous rawInsts hpostLen (by change compactR insts≤2^22;omega)
      tu pub hcompact.1 _ msg,hroots]
  have hepd:=prepared_trace_root_endpoints hprep hk hw hc0 hv
  have hrootbalance:=native_root_balance hk hw hc0 hm hv oldPost writes us rawInsts
    (fun u hu=>(hgood u hu).1) hcount (fun tau u I hu hI=>(hinst tau u I hu hI).1)
    houtputs previous edges (by change compactR insts≤2^22;omega) _ th tu pub hhead.2.2
    hcompact.1 (physicalWindowRank (CompactHeight.trace insts) tu)
  let q : UseRequests:=⟨edges,bmaps,PhysicalWindowRequests.keys (CompactHeight.trace insts) tu⟩
  have hu0 := PhysicalWindowRequests.field_bound (tr:=CompactHeight.trace insts) (t:=tu) (pub:=pub) hcompact.1
  have hu : q.windows.length<Algebra.P := by
    dsimp only [q]
    exact hu0
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
  let ts:=m.pre::steps.map ImplicitStepV3.pre
  let vs:=initializeList 0 (forestNodes 0 0 0 ts)
  let es:=seedValuesFrom 0 (forestBytes ts)
  let cs:=StoreClassPartition.chain (CombinedStoreOccurrences.allOccurrences vs (NativeStoreProvenance.valueTau ts) es)
  let ns:=assignList q 0 (records u (ChainMetadata.assign cs 0 vs))
  let vals:=ChainMetadata.assignValues cs es
  have hAllBytes : ∀M∈(schedulerShaJobs 0 us++schedulerSanityJobs 0 us)++
      jobsToSha (nativeShaJobs ns vals)++receipt++sourceShaMessages p.lists w.entries,∀b∈M.bytes,b<256 := by
      intro M hM b hb
      simp only [List.mem_append] at hM
      rcases hM with ((hM|hM)|hM)|hM
      · exact hschedBytes M (List.mem_append.mpr hM) b hb
      · exact hnative.bytes M hM b hb
      · exact hReceiptBytes M hM b hb
      · exact hsourceBytes M hM b hb
  have halloc:=FourPackedSha.allocation (schedulerShaJobs 0 us++schedulerSanityJobs 0 us) _ receipt
    (sourceShaMessages p.lists w.entries) hschedRows (by rw [jobsToSha_rows];exact hnativeRows)
    hReceiptRows hsourceRows hsourceMax hAllBytes
  have hFacts:=PackedShaFacts.facts _ pub halloc.2.2
  rw [halloc.1] at hFacts
  have hfour:=FourPackedSha.complete (schedulerShaJobs 0 us++schedulerSanityJobs 0 us) _ receipt
    (sourceShaMessages p.lists w.entries) hschedRows (by rw [jobsToSha_rows];exact hnativeRows)
    hReceiptRows hsourceRows hsourceMax hAllBytes pub
  refine ⟨writes,oldPost,us,rawInsts,v,ws,hvvalid,hvreads,hws,hwlocal,hwtraffic,hr,hpairs,(fun x hx=>(hgood x hx).1),hinstLen,patchWindowCounters_local hcompact.1 _,hinputs.1,hinputs.2,(hbalance tu tn).2.1,(hbalance tu tn).2.2.2.1,⟨hhead.2.1,hhead.2.2,(hbalance tu tn).2.2.2.2 _ th hhead.2.2⟩,hmid,hroot,(by simpa only [hepd.1,hepd.2.1,hepd.2.2] using hrootbalance),hlast,hchain,?_,
    hFacts,hfour.1,hfour.2.1,hfour.2.2.1,?_,hfour.2.2.2.2⟩
  · rw [PostMetadataPayloads.post_bytes]
    exact hpost
  · intro msg
    rw [WindowPatchOtherTraffic.count hcompact.1 _ B_BYTES (by decide)]
    have hbytes:=NativeSourceByteBalance.producers hc hprep hfile hraw _ _ hinputs.1 hinputs.2 _ receipt
      _ tn tv pub msg (hfour.2.2.2.1 msg)
    have hs:=hcompact.2 msg
    dsimp only [ns,vals,cs,vs,es,ts,u,q,edges,bmaps,insts,previous] at hbytes
    simp only [Sha.Gen.expectedBytes,List.flatMap_append,List.map_append,List.count_append] at hbytes hs ⊢
    omega

end ZkFormal.NearV3.Candidates.RebasedRootBalanceAllocation
