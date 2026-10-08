import ZkFormal.NearV3.Candidates.NativeDigestConservation
import ZkFormal.NearV3.Assembly.SourcePhysicalDigests
import ZkFormal.NearV3.Candidates.ReceiptSourcePublicBody
import ZkFormal.NearV3.Candidates.ReceiptPublicByteCount
import ZkFormal.NearV3.Candidates.RebasedValueWriteKeys

namespace ZkFormal.NearV3.Candidates.NativeReceiptWriteKeys
open NearSpec NearSpecV3 ZkFormal.Near Assembly Render Render.UpsGen Rcpt.Candidates Rcpt.Candidates.NodePostUpdate
open Render.UpsRelay ZkFormal.Air RcptSkeleton RcptV3Proof Sched RcptV3
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- The receipt trace and four SHA bins share the same accepted native execution,
canonical receipt blocks and exact duplicate-gated receipt job objects. No supplied
receipt SHA batch, row bound or byte-range premise remains. Native account inputs
and global cross-family constraints still need their complete constructor. -/
theorem accepted {cb wb raw : Bytes} {codes : List Bytes} {p : Prep} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {implicitSteps : List ImplicitStepV3} {last : Bytes}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (hc : checkD0a B0 cb wb=.ok ())
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) implicitSteps last)
    (resolve : Qv.Candidates.CombinedWalkGen.Resolve) (tw : Nat)
    (hprep : prepD0 cb (nativeHint k w m)=.ok p)
    (hfile : decodeWitnessFile wb=.ok (raw,codes)) (hraw : decodeStateWitness raw=.ok w)
    (baseI : Nat→UpsInst) (base : Nat→Nat→UpsPartI)
    (th tn tv tu : Nat) (AP : V2.AirP) (overhead : Nat)
    (hseg : AP.pubSegs=Public.preparedSegments)
    (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (constants : ReceiptPlan→Nat→Algebra.Fp) (digests : ReceiptPlan→Nat→List Algebra.Fp)
    (fallback : ReceiptPlan→Coord→Nat→Algebra.Fp) (headerFallback : ListPlan→Coord→Nat→Algebra.Fp)
    (as : List AcctV) (hAcct : as=[] ∨ AcctWf as) (hac : as.length≤8192)
    (hab : ∀M∈accountShaJobs as,∀b∈M.bytes,b<256) (trA : Trace Algebra.Fp) (tA : Nat) :
    let pub:=ZkFormal.Udr.pubOf Algebra.Fp (Public.preparedBytes (RoutingBoundedLayout.boundedPrep p k.L k.H.shardId) overhead)
    (∀msg,tableBusCount AccountEmpty.table.interactions trA tA pub B_BYTES true msg=
      cnt (acctV3Sends as B_BYTES) msg) →
    let lists:=sourceInputLists (m.ctx k) p.lists w.entries
    ∃mid so depositSteps,schedStep prims (m.ctx k) m.pre=.ok (mid,so) ∧
      nativeDepositLedger (m.ctx k) ⟨mid,[],[],0,0⟩ (lists.flatten.map Input.receipt)=some depositSteps ∧
      let trR:=RoutingQCandidate.patchTrace (booleanReceiptTrace k.H.shardId (m.ctx k) lists 22
          (completeReceiptConstants (m.ctx k) k accountId
            (depositConstants (depositPlanAccount depositSteps) (depositAgeConstants (depositPlanPrevious lists) constants)))
          pub (nativeDigests (m.ctx k) digests)
          (completeReceiptAux (m.ctx k) k lists accountId accessId
            (depositFinalAux (depositPlanPrevious lists) (depositPlanAccount depositSteps) fallback))
          (completeReceiptHeaders (depositHeaderAux headerFallback))) 0
      TableLocal ReceiptCandidateRouting.candidateTable trR 0 pub ∧
      TableLocal MerkleEmpty.table (MerkleRender.outcomeTrace m.result.outcomes pub) T_MRK pub ∧
      ∃bs e,ListChain trR 0 0 bs e ∧
        let ls:=bs.map (ListBlock.view trR 0)
        TableTraffic ReceiptCandidateRouting.candidateTable.interactions trR 0 pub (rcptTraffic3 pub ls) ∧
        (flatR ls).map (fun x=>x.leaf)=MerkleRender.outcomePreimages m.result.outcomes ∧
        (∀x∈flatR ls,x.peoh=(sha256 (x.peo.map UInt8.ofNat)).map UInt8.toNat) ∧
        (∀x∈flatR ls,x.hr=true→x.rfid=
          (sha256 ((x.rid++pubBytes pub PH_HEIGHT 8++List.replicate 8 0).map UInt8.ofNat)).map UInt8.toNat) ∧
        (∀msg,tableBusCount ReceiptCandidateRouting.candidateTable.interactions trR 0 pub B_MPOS true msg+
          tableBusCount MerkleEmpty.table.interactions (MerkleRender.outcomeTrace m.result.outcomes pub)
            T_MRK pub B_MPOS true msg=
          tableBusCount MerkleEmpty.table.interactions (MerkleRender.outcomeTrace m.result.outcomes pub)
            T_MRK pub B_MPOS false msg) ∧
        (∀msg,cnt (Sha.Gen.expectedDigests (jobsToSha (ReceiptDigestPartition.jobs pub ls))) msg=
          tableBusCount ReceiptCandidateRouting.candidateTable.interactions trR 0 pub B_DIGEST false msg+
            cnt (ReceiptDigestPartition.leafDigests ls) msg) ∧
        (∀msg,cnt (Sha.Gen.expectedDigests (jobsToSha
          (ReceiptDigestPartition.jobs pub ls++merkleShaJobs (MerkleRender.outcomePreimages m.result.outcomes)))) msg=
          tableBusCount ReceiptCandidateRouting.candidateTable.interactions trR 0 pub B_DIGEST false msg+
          tableBusCount MerkleEmpty.table.interactions (MerkleRender.outcomeTrace m.result.outcomes pub)
            T_MRK pub B_DIGEST false msg) ∧
        (∀msg,cnt (Sha.Gen.expectedDigests (ReceiptGatedShaJobs.jobs pub ls as (Public.sourceDup p.lists))) msg=
          tableBusCount ReceiptCandidateRouting.candidateTable.interactions trR 0 pub B_DIGEST false msg+
          tableBusCount MerkleEmpty.table.interactions (MerkleRender.outcomeTrace m.result.outcomes pub)
            T_MRK pub B_DIGEST false msg+
          cnt (Sha.Gen.expectedDigests
            (sourceRcShaJobs k.H.shardId p.lists w.entries++jobsToSha (accountShaJobs as))) msg) ∧
        ReceiptGatedShaJobs.rcJobs pub ls (Public.sourceDup p.lists)=
          sourceRcShaJobs k.H.shardId p.lists w.entries ∧
        (Sha.Gen.honestRows (ReceiptGatedShaJobs.jobs pub ls as (Public.sourceDup p.lists))).length≤1373299 ∧
        (∀M∈ReceiptGatedShaJobs.jobs pub ls as (Public.sourceDup p.lists),∀b∈M.bytes,b<256) ∧
        (∀msg,cnt (Sha.Gen.expectedBytes (ReceiptGatedShaJobs.jobs pub ls as (Public.sourceDup p.lists))) msg+
          V2.pubCount AP pub B_BYTES false msg=
          tableBusCount ReceiptCandidateRouting.candidateTable.interactions trR 0 pub B_BYTES true msg+
          tableBusCount AccountEmpty.table.interactions trA tA pub B_BYTES true msg+
          tableBusCount MerkleEmpty.table.interactions (MerkleRender.outcomeTrace m.result.outcomes pub)
            T_MRK pub B_BYTES true msg) ∧
        let receipt:=ReceiptGatedShaJobs.jobs pub ls as (Public.sourceDup p.lists)
    let source:=sourceShaMessages p.lists w.entries
    ∃writes,∃oldPost : PTrie,∃us : List SchedulerUpsertWitness,∃rawInsts : List UpsInst,
    ∃v : Qv.MainValues,∃ws : List WalkR,
      v.Valid ∧ v.Reads m.pre m.pre m.pre ∧
      nativeQueryWalks ((m.pre,m.result.trie)::implicitSteps.map (fun s=>(s.pre,s.post)))
        (allLookupQueries (appliedReceipts k w) m.pre v (implicitSteps.map ImplicitStepV3.pre) resolve)=some ws ∧
      TableLocal {WalkV3.table with maxLog:=22} (nativeWalkTrace (rankWalks [] ws)) tw pub ∧
      TableTraffic WalkV3.interactions (nativeWalkTrace (rankWalks [] ws)) tw pub (walkTraffic3 (rankWalks [] ws)) ∧
      let insts:=physicalPrefixUps (ws.flatMap (·.steps)) rawInsts
      let edges:=walkEdgeKeys (ws++upsWalkInventory rawInsts)
      let bmaps:=walkBmapKeys (ws++upsWalkInventory rawInsts)
      let q : UseRequests:=⟨edges,bmaps,PhysicalWindowRequests.keys (CompactHeight.trace insts) tu⟩
      writes.map Prod.fst=(appliedReceipts k w).map (fun r=>accountKeyPath r.receiverId) ∧
      SizedAccountRun m.pre writes oldPost ∧
      us.map (fun u=>(u.pre,u.run.output))=(oldPost,m.result.trie)::implicitSteps.map (fun s=>(s.pre,s.post)) ∧
      (∀u∈us,u.Valid) ∧ insts.length=us.length ∧
      TableLocal Render.UpsRelay.compactTable (patchWindowCounters (CompactHeight.trace insts) tu (physicalWindowRank (CompactHeight.trace insts) tu)) tu pub ∧
      let scheduler:=schedulerShaJobs 0 us++schedulerSanityJobs 0 us 
      
      let rs:=nativeReplayForest m implicitSteps oldPost writes
      let u:=forestOldInputs rs
      let ts:=m.pre::implicitSteps.map ImplicitStepV3.pre
      let vs:=initializeList 0 (forestNodes 0 0 0 ts)
      let es:=seedValuesFrom 0 (forestBytes ts)
      let cs:=StoreClassPartition.chain (CombinedStoreOccurrences.allOccurrences vs (NativeStoreProvenance.valueTau ts) es)
      let ns:=assignList q 0 (records u (ChainMetadata.assign cs 0 vs))
      let vals:=ChainMetadata.assignValues cs es
      NodeOk ns ∧ ValWf vals ∧
      TableLocal SizeCount.nodeTable (TrieCountHeight.node ns pub) tn pub ∧
      (let hs:=assignHeadUses edges (forestWalkHeads 0 0 ((nativeReplayForest m implicitSteps oldPost writes).map (fun r=>(r.pre,r.post))))
       let trh:=replayHeadTrace hs
       ∀msg,tableBusCount HeadV3.interactions trh th pub B_DIGEST false msg+
         tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node ns pub) tn pub B_DIGEST false msg=
         ((Sha.Gen.expectedDigests (jobsToSha (nativeNodeShaJobsFrom 0 ns))).map Msg.toFp).count msg+
         ((ns.flatMap slotDigests).map Msg.toFp).count msg) ∧
      TableLocal EmptyValue.table (TrieCountHeight.value vals pub) tv pub ∧
      (∀msg,tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node ns pub) tn pub B_DIGEST false msg=
        ((ns.flatMap childDigests).map Msg.toFp).count msg+
        (((nativeValueShaJobs vals).map ZkFormal.Near.Render.digestMsg).map Msg.toFp).count msg+
        tableBusCount EmptyValue.table.interactions (TrieCountHeight.value vals pub) tv pub B_DIGEST true msg+
        ((ns.flatMap postSlotDigests).map Msg.toFp).count msg) ∧
      (∀msg,Air.tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node ns pub) tn pub B_UPB true msg+
        Air.tableBusCount Render.UpsRelay.compactTable.interactions (patchWindowCounters (CompactHeight.trace insts) tu (physicalWindowRank (CompactHeight.trace insts) tu)) tu pub B_UPB true msg=
        Air.tableBusCount Render.UpsRelay.compactTable.interactions (patchWindowCounters (CompactHeight.trace insts) tu (physicalWindowRank (CompactHeight.trace insts) tu)) tu pub B_UPB false msg+
        Air.tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node ns pub) tn pub B_UPB false msg) ∧
      (let nodeTrace:=TrieCountHeight.node ns pub
       let upsTrace:=patchWindowCounters (CompactHeight.trace insts) tu (physicalWindowRank (CompactHeight.trace insts) tu)
       let hs:=assignHeadUses edges (forestWalkHeads 0 0 ((nativeReplayForest m implicitSteps oldPost writes).map (fun r=>(r.pre,r.post))))
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
      (let hs:=assignHeadUses edges (forestWalkHeads 0 0 ((nativeReplayForest m implicitSteps oldPost writes).map (fun r=>(r.pre,r.post))))
       let trh:=replayHeadTrace hs
       let tru:=patchWindowCounters (CompactHeight.trace insts) tu (physicalWindowRank (CompactHeight.trace insts) tu)
       ∀msg,tableBusCount HeadV3.interactions trh th pub B_MIDROOT true msg+
         tableBusCount Render.UpsRelay.compactTable.interactions tru tu pub B_MIDROOT true msg=
         tableBusCount HeadV3.interactions trh th pub B_MIDROOT false msg+
         tableBusCount Render.UpsRelay.compactTable.interactions tru tu pub B_MIDROOT false msg) ∧
      (let tru:=patchWindowCounters (CompactHeight.trace insts) tu (physicalWindowRank (CompactHeight.trace insts) tu)
       ∀msg,tableBusCount Render.UpsRelay.compactTable.interactions tru tu pub B_ROOT true msg=
         ((nativeRootRecords 0 (m.result.trie::implicitSteps.map ImplicitStepV3.post)).map Msg.toFp).count msg) ∧
      (let hs:=assignHeadUses edges (forestWalkHeads 0 0 ((nativeReplayForest m implicitSteps oldPost writes).map (fun r=>(r.pre,r.post))))
       let trh:=replayHeadTrace hs
       let tru:=patchWindowCounters (CompactHeight.trace insts) tu (physicalWindowRank (CompactHeight.trace insts) tu)
       ∀msg,V2.pubCount AP pub B_ROOT true msg+
         tableBusCount HeadV3.interactions trh th pub B_ROOT true msg+
         tableBusCount Render.UpsRelay.compactTable.interactions tru tu pub B_ROOT true msg=
         tableBusCount HeadV3.interactions trh th pub B_ROOT false msg+
         tableBusCount Render.UpsRelay.compactTable.interactions tru tu pub B_ROOT false msg+
         V2.pubCount AP pub B_ROOT false msg) ∧
      last=k.H.prevStateRoot ∧
      (([0]++k.slotB2.prevStateRoot.map UInt8.toNat)::
        nativeRootRecords 0 (m.result.trie::implicitSteps.map ImplicitStepV3.post)=
        nativeInputRoots 0 (m.pre::implicitSteps.map ImplicitStepV3.pre)++
          [[implicitSteps.length+1]++k.H.prevStateRoot.map UInt8.toNat]) ∧
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
      (∀msg,PackedShaBins.unionCount bs pub (List.range 4) false B_BYTES msg+V2.pubCount AP pub B_BYTES false msg=
        Air.tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node ns pub) tn pub B_BYTES true msg+
        Air.tableBusCount EmptyValue.table.interactions (TrieCountHeight.value vals pub) tv pub B_BYTES true msg+
        SourceLog22.boundaryCount (NativeSourceFour.trace (DedupCompile.blocks p.lists w.entries)
          (sourceRepeated p.lists)) 0 1 2 3 pub B_BYTES true msg+
        Air.tableBusCount Render.UpsRelay.compactTable.interactions (patchWindowCounters (CompactHeight.trace insts) tu (physicalWindowRank (CompactHeight.trace insts) tu)) tu pub B_BYTES true msg+
        ((Sha.Gen.expectedBytes (SchedulerShaSplit.freshJobs 0 us++schedulerSanityJobs 0 us)).map Msg.toFp).count msg+
        tableBusCount ReceiptCandidateRouting.candidateTable.interactions trR 0 pub B_BYTES true msg+
        tableBusCount AccountEmpty.table.interactions trA tA pub B_BYTES true msg+
        tableBusCount MerkleEmpty.table.interactions (MerkleRender.outcomeTrace m.result.outcomes pub)
          T_MRK pub B_BYTES true msg) ∧
      (∀msg,PackedShaBins.unionCount bs pub (List.range 4) true B_DIGEST msg=
        ((Sha.Gen.expectedDigests (scheduler++native++receipt++source)).map Msg.toFp).count msg) ∧
      (let trh:=replayHeadTrace (assignHeadUses edges (forestWalkHeads 0 0
        ((nativeReplayForest m implicitSteps oldPost writes).map (fun r=>(r.pre,r.post)))))
       ∀msg,PackedShaBins.unionCount bs pub (List.range 4) true B_DIGEST msg+
        tableBusCount EmptyValue.table.interactions (TrieCountHeight.value vals pub) tv pub B_DIGEST true msg+
        ((ns.flatMap postSlotDigests).map Msg.toFp).count msg=
        tableBusCount HeadV3.interactions trh th pub B_DIGEST false msg+
        tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node ns pub) tn pub B_DIGEST false msg+
        tableBusCount ReceiptCandidateRouting.candidateTable.interactions trR 0 pub B_DIGEST false msg+
        tableBusCount MerkleEmpty.table.interactions (MerkleRender.outcomeTrace m.result.outcomes pub)
          T_MRK pub B_DIGEST false msg+
        SourceLog22.boundaryCount (NativeSourceFour.trace (DedupCompile.blocks p.lists w.entries)
          (sourceRepeated p.lists)) 0 1 2 3 pub B_DIGEST false msg+
        cnt (Sha.Gen.expectedDigests (scheduler++jobsToSha (accountShaJobs as))) msg) := by
  dsimp only
  intro hA
  obtain ⟨mid,so,depositSteps,hsched,hledger,hlocal,hmerkle,blocks,e,hchain,ht,hleaf,hpeo,hrid,hpos,hdig,hmdig,hfull,hrc,hrows,hbytes,hrefund,hphysical⟩ :=
    ReceiptSourcePublicBody.native hprep hk hraw hw ((relD0a_iff B0 cb wb).mpr hc) hm
      overhead accountId accessId constants digests fallback headerFallback as hAcct hac hab trA tA hA
  have hpublic : ∀msg,V2.pubCount AP
      (ZkFormal.Udr.pubOf Algebra.Fp (Public.preparedBytes (RoutingBoundedLayout.boundedPrep p k.L k.H.shardId) overhead))
      B_BYTES false msg=cnt (emitAt K_RF 8 ((p.body.drop 8).map UInt8.toNat)) msg :=
    ReceiptPublicByteCount.accepted AP hprep hk hw hc hm overhead hseg
  have hphysical' := hphysical
  simp only [←hpublic] at hphysical'
  have halloc:=RebasedValueWriteKeys.accepted hk hw hc hm hv resolve tw hprep hfile hraw
    _ hrows hbytes baseI base th tn tv tu AP overhead hseg
  obtain ⟨writes,oldPost,us,rawInsts,v,ws,hvvalid,hvreads,hquery,hwalklocal,hwalktraffic,
    hkeys,hrun,hpairs,hus,hinstlen,huplocal,hnode,hval,hnodeLocal,hnodeDig,hvalLocal,hvalDig,
    hupb,hshared,hmid,hroot,hpubroot,hlast,hrootchain,hpost,hshaFacts,hbs,hlog,hshalocal,hshaBytes,hshaDig⟩:=halloc
  refine ⟨mid,so,depositSteps,hsched,hledger,hlocal,hmerkle,blocks,e,hchain,ht,hleaf,hpeo,hrid,hpos,
    hdig,hmdig,hfull,hrc,hrows,hbytes,hphysical',writes,oldPost,us,rawInsts,v,ws,
    hvvalid,hvreads,hquery,hwalklocal,hwalktraffic,hkeys,hrun,hpairs,hus,hinstlen,huplocal,
    hnode,hval,hnodeLocal,hnodeDig,hvalLocal,hvalDig,hupb,hshared,hmid,hroot,hpubroot,
    hlast,hrootchain,hpost,hshaFacts,hbs,hlog,hshalocal,hshaBytes,?_,hshaDig,?_⟩
  · intro msg
    rw [show EmptyValue.table.interactions=SizeCount.valTable.interactions++[EmptyValue.emptyInteraction] from rfl]
    rw [EmptyValue.other_counts SizeCount.valTable _ tv _ B_BYTES true msg (Or.inl (by decide))]
    have hs:=hshaBytes msg
    have hr:=hphysical' msg
    simp only [Sha.Gen.expectedBytes,List.flatMap_append,List.map_append,List.count_append,cnt] at hs hr ⊢
    omega

  · intro msg
    have hn:=NativeDigestConservation.physical _ _ _ th tn tv _ msg hnode (hnodeDig msg) (hvalDig msg)
    have hs:=hshaDig msg
    have hr:=hfull msg
    have hsrc:=physical_source_digest_balance hc hprep hk hfile hraw
      (ZkFormal.Udr.pubOf Algebra.Fp (Public.preparedBytes (RoutingBoundedLayout.boundedPrep p k.L k.H.shardId) overhead)) msg
    simp only [Sha.Gen.expectedDigests,List.filter_append,List.map_append,List.count_append,cnt] at hn hs hr hsrc ⊢
    omega

end ZkFormal.NearV3.Candidates.NativeReceiptWriteKeys
