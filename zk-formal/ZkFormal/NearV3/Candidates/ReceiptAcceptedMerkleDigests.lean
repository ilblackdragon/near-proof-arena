import ZkFormal.NearV3.Candidates.ReceiptPreparedMerkleDigests
import ZkFormal.NearV3.Candidates.ReceiptPreparedFinalPublic
import ZkFormal.NearV3.Candidates.ReceiptGatedShaJobs
import ZkFormal.NearV3.Assembly.RcptGasPrepared

namespace ZkFormal.NearV3.Candidates.ReceiptAcceptedMerkleDigests
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Assembly
open RcptSkeleton RcptV3Proof Rcpt.Candidates Sched RcptV3

/-- Receipt/Merkle local and digest balance for the same accepted native run and
actual normalized prepared public bytes. All public header bindings used here are derived from nativeHint preparation
and checker acceptance; account traffic and native input-plan correspondences remain explicit. -/
theorem native {cb wb raw : Bytes} {p : Prep} {k : WalkD0}
    {w : StateWitness} {m : MainExecutionV3}
    (hp : prepD0 cb (nativeHint k w m)=.ok p) (hk : walkD0 cb=.ok k)
    (hd : decodeStateWitness raw=.ok w) (hdecode : decodeW wb=.ok w)
    (hc : checkD0 cb wb=.ok ()) (hm : m.NativeValid k w)
    (overhead : Nat) (lists : List (List Input))
    (hsource : lists.length=p.lists.length)
    (hls : lists.flatten.map Input.receipt=appliedReceipts k w)
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (hne : lists≠[])
    (hn : ∀xs∈lists,∀x∈xs,AccountId.isNamed x.receipt.receiverId=true)
    (hflags : ∀xs∈lists,∀x∈xs,x.refund=nativeRefund (m.ctx k) x.receipt)
    (hgas : (m.ctx k).gasLimit≤maxGasLimitD0)
    (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (constants : ReceiptPlan→Nat→Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hprice : (m.ctx k).gasPrice<256^16)
    (as : List AcctV) (trA : Trace Fp) (tA : Nat) :
    let pub:=ZkFormal.Udr.pubOf Fp (Public.preparedBytes
      (RoutingBoundedLayout.boundedPrep p k.L k.H.shardId) overhead)
    (∀msg,tableBusCount AccountEmpty.table.interactions trA tA pub B_BYTES true msg=
      cnt (acctV3Sends as B_BYTES) msg) →
    ∃mid so steps,schedStep prims (m.ctx k) m.pre=.ok (mid,so) ∧
      nativeDepositLedger (m.ctx k) ⟨mid,[],[],0,0⟩ (lists.flatten.map Input.receipt)=some steps ∧
      let trR:=RoutingQCandidate.patchTrace (booleanReceiptTrace k.H.shardId (m.ctx k) lists 22
          (completeReceiptConstants (m.ctx k) k accountId
            (depositConstants (depositPlanAccount steps) (depositAgeConstants (depositPlanPrevious lists) constants)))
          pub (nativeDigests (m.ctx k) digests)
          (completeReceiptAux (m.ctx k) k lists accountId accessId
            (depositFinalAux (depositPlanPrevious lists) (depositPlanAccount steps) fallback))
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
            (ReceiptGatedShaJobs.rcJobs pub ls (Public.sourceDup p.lists)++jobsToSha (accountShaJobs as))) msg) ∧
        ∀msg,cnt (Sha.Gen.expectedBytes (ReceiptGatedShaJobs.jobs pub ls as (Public.sourceDup p.lists))) msg+
          cnt (refundFragments (flatR ls)) msg=
          tableBusCount ReceiptCandidateRouting.candidateTable.interactions trR 0 pub B_BYTES true msg+
          tableBusCount AccountEmpty.table.interactions trA tA pub B_BYTES true msg+
          tableBusCount MerkleEmpty.table.interactions (MerkleRender.outcomeTrace m.result.outcomes pub)
            T_MRK pub B_BYTES true msg := by
  dsimp only
  intro hA
  obtain ⟨mid,so,steps,hsched,hledger,hlocal,hmerkle,blocks,e,hchain,ht,hleaf,hpeo,hrid,hpos,hdig,hmdig,hfull,hbytes⟩ :=
    ReceiptPreparedMerkleDigests.native hp hk hd hdecode hc hm k.H.shardId overhead lists
    hsource hls hw hne hn hflags hgas accountId accessId constants digests fallback headerFallback hprice
    as trA tA (ReceiptPreparedFinalPublic.final_public overhead lists hp hk hdecode hc hm hls hw hflags)
    (ReceiptPreparedFinalPublic.own_public overhead hp hk hdecode hc hm) hA

  have hout : m.result.outcomes.length≤4481 := by
    rw [applyNewChunk_outcomes prims hm.run,List.length_map]
    exact applyNewChunk_receipt_bound hm.run hgas
  refine ⟨mid,so,steps,hsched,hledger,hlocal,hmerkle,blocks,e,hchain,ht,hleaf,hpeo,hrid,hpos,hdig,hmdig,?_,?_⟩
  · intro msg
    exact ReceiptGatedShaJobs.physical _ _ m.result.outcomes hout hleaf
      (ReceiptNativeMerkleDigests.bounded_native_outcome overhead hp hk hdecode hc hm)
      (ReceiptDigestPartition.extracted_rid_lengths _ 0 blocks) hpeo hrid _ 0 ht as (Public.sourceDup p.lists) msg
  · intro msg
    rw [ReceiptGatedShaJobs.bytes_unchanged]
    exact hbytes msg

end ZkFormal.NearV3.Candidates.ReceiptAcceptedMerkleDigests
