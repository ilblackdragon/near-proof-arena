import ZkFormal.NearV3.Candidates.NativeQueueShardBalance
import ZkFormal.NearV3.Candidates.NativeLookupKeyBalance
import ZkFormal.NearV3.Candidates.NativeRepairedQueueLocal
import ZkFormal.NearV3.Candidates.NativeLookupFinalBalance
import ZkFormal.NearV3.Candidates.NativeCombinedBytePartition
import ZkFormal.NearV3.Candidates.NativeAccessKeyPhysicalBalance
import ZkFormal.NearV3.Rcpt.Candidates.NativeReceiptMemBalance
import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountMemContext
import ZkFormal.NearV3.Candidates.NativeReceiptAccountIds
import ZkFormal.NearV3.Candidates.NativeAccessBytePartition
import ZkFormal.NearV3.Candidates.NativeValueByteInventory
import ZkFormal.NearV3.Candidates.NativeAccountSlotBalance
import ZkFormal.NearV3.Rcpt.Candidates.AcceptedNativeAccountDigest
import ZkFormal.NearV3.Candidates.NativeAccountReplayAgreement
import ZkFormal.NearV3.Candidates.NativeDigestConservation
import ZkFormal.NearV3.Assembly.SourcePhysicalDigests
import ZkFormal.NearV3.Candidates.ReceiptSourcePublicBody
import ZkFormal.NearV3.Candidates.ReceiptPublicByteCount
import ZkFormal.NearV3.Candidates.RebasedSchedulerDigests

namespace ZkFormal.NearV3.Candidates.NativeReceiptShardBytes
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
    (hids:accountId=NativeReceiptAccountIds.accountId m.pre (appliedReceipts k w))
    (haccess:accessId=NativeReceiptAccessIds.accessId m.pre)
    (constants : ReceiptPlan→Nat→Algebra.Fp) (digests : ReceiptPlan→Nat→List Algebra.Fp)
    (fallback : ReceiptPlan→Coord→Nat→Algebra.Fp) (headerFallback : ListPlan→Coord→Nat→Algebra.Fp)
    (as : List AcctV) (hAcct : as=[] ∨ AcctWf as) (hac : as.length≤8192)
    (hab : ∀M∈accountShaJobs as,∀b∈M.bytes,b<256)
    (haccounts : ∀(writes : List (List Nat×Bytes))(oldPost : PTrie)(us : List SchedulerUpsertWitness),
      SizedAccountRun m.pre writes oldPost→
      us.map (fun u=>(u.pre,u.run.output))=(oldPost,m.result.trie)::implicitSteps.map (fun s=>(s.pre,s.post))→
      (∀u∈us,u.Valid)→nativeAccountViews m.pre oldPost (appliedReceipts k w)=some as)
    (trA trK : Trace Algebra.Fp) (tA tK : Nat) :
    let pub:=ZkFormal.Udr.pubOf Algebra.Fp (Public.preparedBytes (RoutingBoundedLayout.boundedPrep p k.L k.H.shardId) overhead)
    TableTraffic AccountEmpty.table.interactions trA tA pub (acctV3Traffic as) →
    TableTraffic AkeyV3.interactions trK tK pub (akeyTraffic (NativeAccessKeyProviders.providers m.pre (appliedReceipts k w))) →
    let lists:=sourceInputLists (m.ctx k) p.lists w.entries
    ∃mid so depositSteps,schedStep prims (m.ctx k) m.pre=.ok (mid,so) ∧
      nativeDepositLedger (m.ctx k) ⟨mid,[],[],0,0⟩ (lists.flatten.map Input.receipt)=some depositSteps ∧
      let trR:=RoutingQCandidate.patchTrace (booleanReceiptTrace k.H.shardId (m.ctx k) lists 22
          (completeReceiptConstants (m.ctx k) k accountId
            (depositConstants (depositPlanAccount depositSteps) (depositAgeConstants (depositPlanPrevious lists) constants)))
          pub (nativeDigests (m.ctx k) digests)
          (completeReceiptAux (m.ctx k) k lists accountId accessId
            (depositFinalAux (depositPlanPrevious lists) (depositPlanAccount depositSteps) (NativeAccessKeyRanks.rankAux m.pre (appliedReceipts k w) fallback)))
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
        (∀msg,tableBusCount ReceiptCandidateRouting.candidateTable.interactions trR 0 pub B_MEM true msg+
          tableBusCount AccountEmpty.table.interactions trA tA pub B_MEM true msg=
          tableBusCount ReceiptCandidateRouting.candidateTable.interactions trR 0 pub B_MEM false msg+
          tableBusCount AccountEmpty.table.interactions trA tA pub B_MEM false msg) ∧
        (∀msg,tableBusCount AkeyV3.interactions trK tK pub B_AKC true msg+
          tableBusCount ReceiptCandidateRouting.candidateTable.interactions trR 0 pub B_AKC true msg=
          tableBusCount ReceiptCandidateRouting.candidateTable.interactions trR 0 pub B_AKC false msg+
          tableBusCount AkeyV3.interactions trK tK pub B_AKC false msg) ∧
        let receipt:=ReceiptGatedShaJobs.jobs pub ls as (Public.sourceDup p.lists)
    let source:=sourceShaMessages p.lists w.entries
    ∃writes,∃oldPost : PTrie,∃us : List SchedulerUpsertWitness,∃rawInsts : List UpsInst,
    ∃v : Qv.MainValues,∃ws : List WalkR,
      v.Valid ∧ v.Reads m.pre m.pre m.pre ∧
      nativeQueryWalks ((m.pre,m.result.trie)::implicitSteps.map (fun s=>(s.pre,s.post)))
        (allLookupQueries (appliedReceipts k w) m.pre v (implicitSteps.map ImplicitStepV3.pre) resolve)=some ws ∧
      TableLocal {WalkV3.table with maxLog:=22} (nativeWalkTrace (rankWalks [] ws)) tw pub ∧
      TableTraffic WalkV3.interactions (nativeWalkTrace (rankWalks [] ws)) tw pub (walkTraffic3 (rankWalks [] ws)) ∧
      TableLocal QueueKeyRepair.table
        (Qv.Candidates.CombinedWalkGen.mixedTrace
          (Qv.Candidates.CombinedWalkGen.plan m.pre v (implicitSteps.map ImplicitStepV3.pre)
            (NativeQueueIds.resolve m.pre v (implicitSteps.map ImplicitStepV3.pre)))
          (queueRecords (queueForestProviders 0 0 (queueInputs m.pre v (implicitSteps.map ImplicitStepV3.pre)))) 22)
        0 pub ∧
      (∀msg,tableBusCount QueueKeyRepair.interactions
        (Qv.Candidates.CombinedWalkGen.mixedTrace
          (Qv.Candidates.CombinedWalkGen.plan m.pre v (implicitSteps.map ImplicitStepV3.pre)
            (NativeQueueIds.resolve m.pre v (implicitSteps.map ImplicitStepV3.pre)))
          (queueRecords (queueForestProviders 0 0 (queueInputs m.pre v (implicitSteps.map ImplicitStepV3.pre)))) 22)
        0 pub Qv.Candidates.ValueTable.B_QVC true msg=
        tableBusCount QueueKeyRepair.interactions
        (Qv.Candidates.CombinedWalkGen.mixedTrace
          (Qv.Candidates.CombinedWalkGen.plan m.pre v (implicitSteps.map ImplicitStepV3.pre)
            (NativeQueueIds.resolve m.pre v (implicitSteps.map ImplicitStepV3.pre)))
          (queueRecords (queueForestProviders 0 0 (queueInputs m.pre v (implicitSteps.map ImplicitStepV3.pre)))) 22)
        0 pub Qv.Candidates.ValueTable.B_QVC false msg) ∧
      (∀msg,tableBusCount WalkV3.interactions (nativeWalkTrace (rankWalks [] ws)) tw pub B_FINAL true msg=
        tableBusCount ReceiptCandidateRouting.candidateTable.interactions trR 0 pub B_FINAL false msg+
        tableBusCount QueueKeyRepair.interactions
          (Qv.Candidates.CombinedWalkGen.mixedTrace
            (Qv.Candidates.CombinedWalkGen.plan m.pre v (implicitSteps.map ImplicitStepV3.pre)
              (NativeQueueIds.resolve m.pre v (implicitSteps.map ImplicitStepV3.pre)))
            (queueRecords (queueForestProviders 0 0 (queueInputs m.pre v (implicitSteps.map ImplicitStepV3.pre)))) 22)
          0 pub B_FINAL false msg) ∧
      (∀msg,tableBusCount ReceiptCandidateRouting.candidateTable.interactions trR 0 pub B_KEYNIB true msg+
        tableBusCount QueueKeyRepair.interactions
          (Qv.Candidates.CombinedWalkGen.mixedTrace
            (Qv.Candidates.CombinedWalkGen.plan m.pre v (implicitSteps.map ImplicitStepV3.pre)
              (NativeQueueIds.resolve m.pre v (implicitSteps.map ImplicitStepV3.pre)))
            (queueRecords (queueForestProviders 0 0 (queueInputs m.pre v (implicitSteps.map ImplicitStepV3.pre)))) 22)
          0 pub B_KEYNIB true msg=
        tableBusCount WalkV3.interactions (nativeWalkTrace (rankWalks [] ws)) tw pub B_KEYNIB false msg) ∧
      (∀msg,tableBusCount QueueKeyRepair.interactions
        (Qv.Candidates.CombinedWalkGen.mixedTrace
          (Qv.Candidates.CombinedWalkGen.plan m.pre v (implicitSteps.map ImplicitStepV3.pre)
            (NativeQueueIds.resolve m.pre v (implicitSteps.map ImplicitStepV3.pre)))
          (queueRecords (queueForestProviders 0 0 (queueInputs m.pre v (implicitSteps.map ImplicitStepV3.pre)))) 22)
        0 pub B_QSH true msg=
        tableBusCount QueueKeyRepair.interactions
        (Qv.Candidates.CombinedWalkGen.mixedTrace
          (Qv.Candidates.CombinedWalkGen.plan m.pre v (implicitSteps.map ImplicitStepV3.pre)
            (NativeQueueIds.resolve m.pre v (implicitSteps.map ImplicitStepV3.pre)))
          (queueRecords (queueForestProviders 0 0 (queueInputs m.pre v (implicitSteps.map ImplicitStepV3.pre)))) 22)
        0 pub B_QSH false msg) ∧
      let insts:=physicalPrefixUps (ws.flatMap (·.steps)) rawInsts
      let edges:=walkEdgeKeys (ws++upsWalkInventory rawInsts)
      let bmaps:=walkBmapKeys (ws++upsWalkInventory rawInsts)
      let q : UseRequests:=⟨edges,bmaps,PhysicalWindowRequests.keys (CompactHeight.trace insts) tu⟩
      writes.map Prod.fst=(appliedReceipts k w).map (fun r=>accountKeyPath r.receiverId) ∧
      SizedAccountRun m.pre writes oldPost ∧
      us.map (fun u=>(u.pre,u.run.output))=(oldPost,m.result.trie)::implicitSteps.map (fun s=>(s.pre,s.post)) ∧
      (∀u∈us,u.Valid) ∧ insts.length=us.length ∧
      TableLocal Render.UpsRelay.compactTable (patchWindowCounters (CompactHeight.trace insts) tu (physicalWindowRank (CompactHeight.trace insts) tu)) tu pub ∧
      (∀msg,tableBusCount Render.UpsRelay.compactTable.interactions
        (patchWindowCounters (CompactHeight.trace insts) tu (physicalWindowRank (CompactHeight.trace insts) tu))
        tu pub B_DIGEST false msg=cnt (Sha.Gen.expectedDigests (schedulerShaJobs 0 us)) msg) ∧
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
      (∀msg,tableBusCount AccountEmpty.table.interactions trA tA pub B_VSLOT true msg=
        tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node ns pub) tn pub B_VSLOT false msg) ∧
      (let hs:=assignHeadUses edges (forestWalkHeads 0 0 ((nativeReplayForest m implicitSteps oldPost writes).map (fun r=>(r.pre,r.post))))
       let trh:=replayHeadTrace hs
       ∀msg,tableBusCount HeadV3.interactions trh th pub B_DIGEST false msg+
         tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node ns pub) tn pub B_DIGEST false msg=
         ((Sha.Gen.expectedDigests (jobsToSha (nativeNodeShaJobsFrom 0 ns))).map Msg.toFp).count msg+
         ((ns.flatMap slotDigests).map Msg.toFp).count msg) ∧
      TableLocal EmptyValue.table (TrieCountHeight.value vals pub) tv pub ∧
      (∀msg,tableBusCount AccountEmpty.table.interactions trA tA pub B_VBYTES true msg+
        tableBusCount AkeyV3.interactions trK tK pub B_VBYTES true msg+
        cnt (((NativeAccessBytePartition.remaining m.pre writes).filter
          (fun i=>!(decide (i∈NativeAccessKeyProviders.selected m.pre (appliedReceipts k w))))).flatMap
            (fun i=>emitAt i 0 (((NearSpecV3.valsOf m.pre).getD i []).map UInt8.toNat))) msg+
        cnt (NativeValueByteInventory.requests (NearSpecV3.valsOf m.pre).length
          (forestBytes (implicitSteps.map ImplicitStepV3.pre))) msg=
        tableBusCount EmptyValue.table.interactions (TrieCountHeight.value vals pub) tv pub B_VBYTES false msg) ∧
      (∀msg,tableBusCount AccountEmpty.table.interactions trA tA pub B_VBYTES true msg+
        tableBusCount AkeyV3.interactions trK tK pub B_VBYTES true msg+
        tableBusCount QueueKeyRepair.interactions
          (Qv.Candidates.CombinedWalkGen.mixedTrace
            (Qv.Candidates.CombinedWalkGen.plan m.pre v (implicitSteps.map ImplicitStepV3.pre)
              (NativeQueueIds.resolve m.pre v (implicitSteps.map ImplicitStepV3.pre)))
            (queueRecords (queueForestProviders 0 0 (queueInputs m.pre v (implicitSteps.map ImplicitStepV3.pre)))) 22)
          0 pub B_VBYTES true msg+
        cnt (NativeCombinedBytePartition.remaining m.pre (appliedReceipts k w) writes v
          (implicitSteps.map ImplicitStepV3.pre)) msg=
        tableBusCount EmptyValue.table.interactions (TrieCountHeight.value vals pub) tv pub B_VBYTES false msg) ∧
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
        tableBusCount EmptyValue.table.interactions (TrieCountHeight.value vals pub) tv pub B_DIGEST true msg=
        tableBusCount HeadV3.interactions trh th pub B_DIGEST false msg+
        tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node ns pub) tn pub B_DIGEST false msg+
        tableBusCount ReceiptCandidateRouting.candidateTable.interactions trR 0 pub B_DIGEST false msg+
        tableBusCount MerkleEmpty.table.interactions (MerkleRender.outcomeTrace m.result.outcomes pub)
          T_MRK pub B_DIGEST false msg+
        SourceLog22.boundaryCount (NativeSourceFour.trace (DedupCompile.blocks p.lists w.entries)
          (sourceRepeated p.lists)) 0 1 2 3 pub B_DIGEST false msg+
        cnt (Sha.Gen.expectedDigests scheduler) msg) := by
  dsimp only
  intro htraffic hkeytraffic
  have hA:=fun msg=>(htraffic B_BYTES msg).1
  obtain ⟨mid,so,depositSteps,hsched,hledger,hlocal,hmerkle,blocks,e,hchain,ht,hleaf,hpeo,hrid,hpos,hdig,hmdig,hfull,hrc,hrows,hbytes,hrefund,hphysical⟩ :=
    ReceiptSourcePublicBody.native hprep hk hraw hw ((relD0a_iff B0 cb wb).mpr hc) hm
      overhead accountId accessId constants digests (NativeAccessKeyRanks.rankAux m.pre (appliedReceipts k w) fallback) headerFallback as hAcct hac hab trA tA hA
  have hpublic : ∀msg,V2.pubCount AP
      (ZkFormal.Udr.pubOf Algebra.Fp (Public.preparedBytes (RoutingBoundedLayout.boundedPrep p k.L k.H.shardId) overhead))
      B_BYTES false msg=cnt (emitAt K_RF 8 ((p.body.drop 8).map UInt8.toNat)) msg :=
    ReceiptPublicByteCount.accepted AP hprep hk hw hc hm overhead hseg
  have hphysical' := hphysical
  simp only [←hpublic] at hphysical'
  have halloc:=RebasedSchedulerDigests.accepted hk hw hc hm hv resolve tw hprep hfile hraw
    _ hrows hbytes baseI base th tn tv tu AP overhead hseg
  obtain ⟨writes,oldPost,us,rawInsts,v,ws,hvvalid,hvreads,hquery,hwalklocal,hwalktraffic,
    hkeys,hrun,hpairs,hus,hinstlen,huplocal,hschedulerDigest,hnode,hval,hnodeLocal,hnodeDig,hvalLocal,hvalDig,
    hupb,hshared,hmid,hroot,hpubroot,hlast,hrootchain,hpost,hshaFacts,hbs,hlog,hshalocal,hshaBytes,hshaDig⟩:=halloc
  obtain ⟨state,hup⟩:=NativeAccountReplayAgreement.allocated_upsert us oldPost m.result.trie _ hpairs hus
  let ts:=m.pre::implicitSteps.map ImplicitStepV3.pre
  let vs:=initializeList 0 (forestNodes 0 0 0 ts)
  let es:=seedValuesFrom 0 (forestBytes ts)
  let cs:=StoreClassPartition.chain (CombinedStoreOccurrences.allOccurrences vs (NativeStoreProvenance.valueTau ts) es)
  let q : UseRequests:=⟨walkEdgeKeys (ws++upsWalkInventory rawInsts),walkBmapKeys (ws++upsWalkInventory rawInsts),
    PhysicalWindowRequests.keys (CompactHeight.trace (physicalPrefixUps (ws.flatMap (·.steps)) rawInsts)) tu⟩
  let ns:=assignList q 0 (records (forestOldInputs (nativeReplayForest m implicitSteps oldPost writes)) (ChainMetadata.assign cs 0 vs))
  have hp:=native_main_account_digest_balance hm hrun hkeys hup
    (haccounts writes oldPost us hrun hpairs hus) implicitSteps q cs
  have hslot:=fun msg=>NativeAccountSlotBalance.physical as ns trA tA tn _ msg hnode htraffic hp
  have hprebytes:=fun msg=>NativeValueByteInventory.account_partition hkeys
    (haccounts writes oldPost us hrun hpairs hus) (implicitSteps.map ImplicitStepV3.pre) cs
    (⟨hval⟩ : Render.ValOk _) trA tA tv _ msg htraffic
  have hwell:m.pre.wf=true:=by
    rw [hm.pre]
    exact (built_spec w.main.values trieFuel k.slotB2.prevStateRoot _ hm.root_length).2.1
  have hrel:RelD0a B0 cb wb:=(relD0a_iff B0 cb wb).mpr hc
  obtain ⟨_,hls,hlwf,_,_,_⟩:=ReceiptSourceInputs.admitted (m.ctx k) hrel hprep hk hw hraw
  obtain ⟨hgas,_⟩:=ReceiptSourceInputs.gas hrel hprep hk hm
  have hledger':nativeDepositLedger (m.ctx k) ⟨mid,[],[],0,0⟩ (appliedReceipts k w)=some depositSteps:=by
    simpa only [hls] using hledger
  obtain ⟨limits,after,happly,hout,horder,hvalid,hpread⟩:=newchunk_mem_context
    (TrieShape.of_wf _ hwell) hm.run hsched hledger'
  have hpostread:∀account,oldPost.find (accountKeyPath account)=after.1.trie.find (accountKeyPath account):=by
    intro account
    rw [hout]
    exact (ZkFormal.NearV3.find_upsert_ne (SizedAccountRun.wf hrun hwell) (by decide)
      (by simp [keyBwState,accountKeyPath,nibbles]) hup).symm
  have hcount:=(forest_allocation_counts (m.pre::implicitSteps.map ImplicitStepV3.pre)
    (checkD0a_preBytes hk hw hc hm hv)).2
  have hvals:(NearSpecV3.valsOf m.pre).length<Algebra.P:=by
    simp only [forestBytes,List.flatMap_cons,List.length_append] at hcount
    rw [native_valsOf_eq]
    unfold Algebra.P
    omega
  have hmem:=native_receipt_account_mem_balance k.H.shardId (m.ctx k) k
    (sourceInputLists (m.ctx k) p.lists w.entries) 22 constants _ (nativeDigests (m.ctx k) digests)
    accessId (NativeAccessKeyRanks.rankAux m.pre (appliedReceipts k w) fallback) (completeReceiptHeaders (depositHeaderAux headerFallback)) m.pre oldPost as
    ⟨mid,[],[],0,0⟩ depositSteps (by rw [hls];exact haccounts writes oldPost us hrun hpairs hus)
    hvals (by rw [hls];exact hm.run) hgas hledger (by rw [hls];exact horder) hvalid hpread
    0 limits after (by rw [hls];exact happly) hrun.forget.skeleton hpostread hlwf (by decide)
    trA tA AccountEmpty.table.interactions htraffic
  have hids':accountId=(fun rp:ReceiptPlan=>accountSlot m.pre
    (((sourceInputLists (m.ctx k) p.lists w.entries).flatten.map Input.receipt).map
      (fun r=>accountKeyPath r.receiverId)) rp.receiptIndex):=by
    rw [hids,hls];rfl
  simp only [←hids'] at hmem
  have hmem':=hmem (ReceiptCandidateProof.repaired_local_base hlocal) blocks e hchain
  have hcounter:=NativeAccessKeyRanks.physical_balance k.H.shardId (m.ctx k) k
    (sourceInputLists (m.ctx k) p.lists w.entries) 22
    (completeReceiptConstants (m.ctx k) k accountId
      (depositConstants (depositPlanAccount depositSteps)
        (depositAgeConstants (depositPlanPrevious (sourceInputLists (m.ctx k) p.lists w.entries)) constants)))
    _ (nativeDigests (m.ctx k) digests) accountId
    (depositPlanPrevious (sourceInputLists (m.ctx k) p.lists w.entries)) (depositPlanAccount depositSteps)
    fallback (completeReceiptHeaders (depositHeaderAux headerFallback)) m.pre hlwf (by decide)
    trK tK (by rw [hls];exact hkeytraffic)
  simp only [hls,←haccess] at hcounter
  have hcounter':=hcounter (ReceiptCandidateProof.repaired_local_base hlocal) blocks e hchain
  obtain ⟨hqvalid,hqfit⟩:=NativeQueueCounters.accepted_records hk hw hc hm hv v hvvalid hvreads
  have hqholds:=NativeQueueLookupBinding.native_holds hv v hvvalid hvreads
  have hquery':nativeQueryWalks ((m.pre,m.result.trie)::implicitSteps.map (fun s=>(s.pre,s.post)))
      (allLookupQueries (appliedReceipts k w) m.pre v (implicitSteps.map ImplicitStepV3.pre)
        (NativeQueueIds.resolve m.pre v (implicitSteps.map ImplicitStepV3.pre)))=some ws:=by
    simpa only [allLookupQueries,NativeQueueIds.queries_independent m.pre v
      (implicitSteps.map ImplicitStepV3.pre) resolve (NativeQueueIds.resolve m.pre v (implicitSteps.map ImplicitStepV3.pre))] using hquery
  have hfinal:=NativeReceiptQueryInventory.physical_final_balance k.H.shardId (m.ctx k) k
    (sourceInputLists (m.ctx k) p.lists w.entries) 22
    (depositConstants (depositPlanAccount depositSteps)
      (depositAgeConstants (depositPlanPrevious (sourceInputLists (m.ctx k) p.lists w.entries)) constants))
    _ (nativeDigests (m.ctx k) digests)
    (depositFinalAux (depositPlanPrevious (sourceInputLists (m.ctx k) p.lists w.entries))
      (depositPlanAccount depositSteps) (NativeAccessKeyRanks.rankAux m.pre (appliedReceipts k w) fallback))
    (completeReceiptHeaders (depositHeaderAux headerFallback)) hlwf (by decide)
    m.pre oldPost m.result.trie (implicitSteps.map (fun s=>(s.pre,s.post))) as
    (by rw [hls];exact haccounts writes oldPost us hrun hpairs hus) hvals v
    (by simpa only [List.map_map,Function.comp_def] using hqholds) _ hqvalid 22
    (by simpa only [List.map_map,Function.comp_def] using hqfit) ws
    (by simpa only [hls,List.map_map,Function.comp_def] using hquery') []
    (nativeWalkTrace (rankWalks [] ws)) tw hwalktraffic
  simp only [hls,←hids,←haccess,List.map_map,Function.comp_def] at hfinal
  have hfinal':=hfinal (ReceiptCandidateProof.repaired_local_base hlocal) blocks e hchain
  have hqueue:=NativeRepairedQueueLocal.accepted hk hw hc hm hv hprep v hvvalid hvreads overhead
  have hfinalRepair:=hfinal'
  simp only [←QueueKeyRepair.nonkey_count _ _ _ B_FINAL (by decide)] at hfinalRepair
  have hkey:=NativeReceiptQueryInventory.physical_key_balance k.H.shardId (m.ctx k) k
    (sourceInputLists (m.ctx k) p.lists w.entries) 22
    (depositConstants (depositPlanAccount depositSteps)
      (depositAgeConstants (depositPlanPrevious (sourceInputLists (m.ctx k) p.lists w.entries)) constants))
    _ (nativeDigests (m.ctx k) digests) accountId
    (completeReceiptAux (m.ctx k) k (sourceInputLists (m.ctx k) p.lists w.entries) accountId accessId
      (depositFinalAux (depositPlanPrevious (sourceInputLists (m.ctx k) p.lists w.entries))
        (depositPlanAccount depositSteps) (NativeAccessKeyRanks.rankAux m.pre (appliedReceipts k w) fallback)))
    (completeReceiptHeaders (depositHeaderAux headerFallback)) hlwf (by decide)
    m.pre v (implicitSteps.map ImplicitStepV3.pre)
    (NativeQueueIds.resolve m.pre v (implicitSteps.map ImplicitStepV3.pre))
    (queueRecords (queueForestProviders 0 0 (queueInputs m.pre v (implicitSteps.map ImplicitStepV3.pre)))) 22
    (by omega)
    ((m.pre,m.result.trie)::implicitSteps.map (fun s=>(s.pre,s.post))) ws
    (by simpa only [hls] using hquery') [] (nativeWalkTrace (rankWalks [] ws)) tw hwalktraffic
  have hkey':=hkey (ReceiptCandidateProof.repaired_local_base hlocal) blocks e hchain
  have hshard:=NativeQueueShardBalance.accepted hk hw hc hm hv v hvvalid hvreads
    (ZkFormal.Udr.pubOf Algebra.Fp (Public.preparedBytes (RoutingBoundedLayout.boundedPrep p k.L k.H.shardId) overhead))
  refine ⟨mid,so,depositSteps,hsched,hledger,hlocal,hmerkle,blocks,e,hchain,ht,hleaf,hpeo,hrid,hpos,
    hdig,hmdig,hfull,hrc,hrows,hbytes,hphysical',hmem',hcounter',writes,oldPost,us,rawInsts,v,ws,
    hvvalid,hvreads,hquery,hwalklocal,hwalktraffic,hqueue.1,hqueue.2,hfinalRepair,hkey',hshard,hkeys,hrun,hpairs,hus,hinstlen,huplocal,hschedulerDigest,
    hnode,hval,hnodeLocal,hslot,hnodeDig,hvalLocal,?_,?_,hvalDig,hupb,hshared,hmid,hroot,hpubroot,
    hlast,hrootchain,hpost,hshaFacts,hbs,hlog,hshalocal,hshaBytes,?_,hshaDig,?_⟩
  · intro msg
    have hwell:m.pre.wf=true:=by
      rw [hm.pre]
      exact (built_spec w.main.values trieFuel k.slotB2.prevStateRoot _ hm.root_length).2.1
    have hvalid:=NativeAccessKeyValidation.newchunk_valid (TrieShape.of_wf _ hwell) hm.run
    have hkbytes:=NativeAccessBytePartition.physical_split hkeys hvalid trK tK _ msg hkeytraffic
    have habytes:=hprebytes msg
    dsimp only [cs,vs,es,ts] at habytes
    dsimp only [NativeAccessBytePartition.remaining] at hkbytes ⊢
    omega
  · intro msg
    have hvalid:=NativeAccessKeyValidation.newchunk_valid (TrieShape.of_wf _ hwell) hm.run
    rw [QueueKeyRepair.nonkey_count _ _ _ B_VBYTES (by decide)]
    exact NativeCombinedBytePartition.physical_partition hk hw hc hm hv v hvvalid hvreads
      hkeys (haccounts writes oldPost us hrun hpairs hus) hvalid cs (⟨hval⟩ : Render.ValOk _)
      trA trK tA tK tv _ msg htraffic hkeytraffic
  · intro msg
    rw [show EmptyValue.table.interactions=SizeCount.valTable.interactions++[EmptyValue.emptyInteraction] from rfl]
    rw [EmptyValue.other_counts SizeCount.valTable _ tv _ B_BYTES true msg (Or.inl (by decide))]
    have hs:=hshaBytes msg
    have hr:=hphysical' msg
    simp only [Sha.Gen.expectedBytes,List.flatMap_append,List.map_append,List.count_append,cnt] at hs hr ⊢
    omega

  · intro msg
    have hn:=NativeDigestConservation.physical _ _ _ th tn tv _ msg hnode (hnodeDig msg) (hvalDig msg)
    have hacount : cnt (Sha.Gen.expectedDigests (jobsToSha (accountShaJobs as))) msg=
        ((ns.flatMap postSlotDigests).map Msg.toFp).count msg := by
      rw [ReceiptDigestPartition.jobs_digests]
      exact (hp.map Msg.toFp).count_eq msg
    dsimp only [ns,q,cs,vs,es,ts] at hacount
    have hs:=hshaDig msg
    have hr:=hfull msg
    have hsrc:=physical_source_digest_balance hc hprep hk hfile hraw
      (ZkFormal.Udr.pubOf Algebra.Fp (Public.preparedBytes (RoutingBoundedLayout.boundedPrep p k.L k.H.shardId) overhead)) msg
    simp only [Sha.Gen.expectedDigests,List.filter_append,List.map_append,List.count_append,cnt] at hn hs hr hsrc hacount ⊢
    omega

end ZkFormal.NearV3.Candidates.NativeReceiptShardBytes
