import ZkFormal.NearV3.Candidates.ReceiptNativeMerklePositions
import ZkFormal.NearV3.Candidates.ReceiptDigestPartition
import ZkFormal.NearV3.Candidates.ReceiptNativeMerkleBytes
import ZkFormal.NearV3.Assembly.RcptCanonicalRefundDigest
import ZkFormal.NearV3.Assembly.RcptHeightPrepared
import ZkFormal.NearV3.Assembly.RcptCanonicalPeoDigest
import ZkFormal.NearV3.Candidates.ReceiptMerkleShaBytes
import ZkFormal.NearV3.Assembly.RcptCanonicalNativeLeaves
import ZkFormal.NearV3.Assembly.RcptCandidateRepairedTraffic

namespace ZkFormal.NearV3.Candidates.ReceiptNativeDigestBalance
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Assembly
open RcptSkeleton RcptV3Proof Rcpt.Candidates Sched RcptV3

theorem native {cb bs : Bytes} {hint : Hint} {p : Prep} {k : WalkD0} {w : StateWitness}
    (hp : prepD0 cb hint=.ok p) (hk : walkD0 cb=.ok k) (hd : decodeStateWitness bs=.ok w) (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hsource : lists.length=p.lists.length)
    (hls : lists.flatten.map Input.receipt=appliedReceipts k w)
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (hne : lists≠[])
    (hn : ∀xs∈lists,∀x∈xs,AccountId.isNamed x.receipt.receiverId=true)
    (hflags : ∀xs∈lists,∀x∈xs,x.refund=nativeRefund ctx x.receipt)
    {t : PTrie} {out : MainOut}
    (hrun : applyNewChunk prims ctx t (lists.flatten.map Input.receipt)=.ok out)
    (hgas : ctx.gasLimit≤maxGasLimitD0)
    (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hheight : HeightPublicBytes ctx pub) (hgp : GasPublicBytes ctx pub) (hprice : ctx.gasPrice<256^16)
    (hpub : FinalPublicBytes lists out pub)
    (hown : ∀j,j<8→pub.getD (PH_OWN+j) 0=Fp.ofNat (((u64 own).getD j 0).toNat))
    (as : List AcctV) (trA : Trace Fp) (tA : Nat)
    (hA : ∀msg,tableBusCount AccountEmpty.table.interactions trA tA pub B_BYTES true msg=
      cnt (acctV3Sends as B_BYTES) msg) :
    ∃mid so steps,schedStep prims ctx t=.ok (mid,so) ∧
      nativeDepositLedger ctx ⟨mid,[],[],0,0⟩ (lists.flatten.map Input.receipt)=some steps ∧
      let trR:=RoutingQCandidate.patchTrace (booleanReceiptTrace own ctx lists 22
          (completeReceiptConstants ctx k accountId
            (depositConstants (depositPlanAccount steps) (depositAgeConstants (depositPlanPrevious lists) constants)))
          pub (nativeDigests ctx digests)
          (completeReceiptAux ctx k lists accountId accessId
            (depositFinalAux (depositPlanPrevious lists) (depositPlanAccount steps) fallback))
          (completeReceiptHeaders (depositHeaderAux headerFallback))) 0
      TableLocal ReceiptCandidateRouting.candidateTable trR 0 pub ∧
      ∃bs e,ListChain trR 0 0 bs e ∧
        let ls:=bs.map (ListBlock.view trR 0)
        TableTraffic ReceiptCandidateRouting.candidateTable.interactions trR 0 pub (rcptTraffic3 pub ls) ∧
        (flatR ls).map (fun x=>x.leaf)=MerkleRender.outcomePreimages out.outcomes ∧
        (∀x∈flatR ls,x.peoh=(sha256 (x.peo.map UInt8.ofNat)).map UInt8.toNat) ∧
        (∀x∈flatR ls,x.hr=true→x.rfid=
          (sha256 ((x.rid++pubBytes pub PH_HEIGHT 8++List.replicate 8 0).map UInt8.ofNat)).map UInt8.toNat) ∧
        (∀msg,tableBusCount ReceiptCandidateRouting.candidateTable.interactions trR 0 pub B_MPOS true msg+
          tableBusCount MerkleEmpty.table.interactions (MerkleRender.outcomeTrace out.outcomes pub)
            T_MRK pub B_MPOS true msg=
          tableBusCount MerkleEmpty.table.interactions (MerkleRender.outcomeTrace out.outcomes pub)
            T_MRK pub B_MPOS false msg) ∧
        (∀msg,cnt (Sha.Gen.expectedDigests (jobsToSha (ReceiptDigestPartition.jobs pub ls))) msg=
          tableBusCount ReceiptCandidateRouting.candidateTable.interactions trR 0 pub B_DIGEST false msg+
            cnt (ReceiptDigestPartition.leafDigests ls) msg) ∧
        ∀msg,cnt (Sha.Gen.expectedBytes (jobsToSha (receiptShaJobs pub ls as))) msg+
          cnt (refundFragments (flatR ls)) msg=
          tableBusCount ReceiptCandidateRouting.candidateTable.interactions trR 0 pub B_BYTES true msg+
          tableBusCount AccountEmpty.table.interactions trA tA pub B_BYTES true msg+
          tableBusCount MerkleEmpty.table.interactions (MerkleRender.outcomeTrace out.outcomes pub)
            T_MRK pub B_BYTES true msg := by
  obtain ⟨mid,so,steps,hm,hl,ho,hv,hlocal⟩:=booleanReceiptTrace_native_repaired_tableLocal
    hp hk hd own ctx lists hsource hls hw hne hn hflags hrun hgas accountId accessId constants pub
    (nativeDigests ctx digests) fallback headerFallback hgp hprice hpub hown
  have hout : out.outcomes.length≤4481 := by
    rw [applyNewChunk_outcomes prims hrun,List.length_map]
    exact applyNewChunk_receipt_bound hrun hgas
  obtain ⟨blocks,e,hchain,ht,hleaf,hbytes⟩:=ReceiptNativeMerkleBytes.physical prims own ctx t lists out hrun 22 _ pub
    (refundDigests ctx digests) _ _ hw (by decide) hlocal hout as trA tA hA
  have hpDigest:=canonical_peo_digests own ctx k lists accountId accessId 22 _ pub digests
    (depositFinalAux (depositPlanPrevious lists) (depositPlanAccount steps) fallback) _
    hw hflags (by decide) hlocal blocks e hchain
  have hrDigest:=canonical_refund_digests own ctx k lists accountId accessId 22 _ pub digests
    (depositFinalAux (depositPlanPrevious lists) (depositPlanAccount steps) fallback) _
    hw hheight (by decide) hlocal blocks e hchain
  refine ⟨mid,so,steps,hm,hl,hlocal,blocks,e,hchain,ht,hleaf,hpDigest,hrDigest,ReceiptNativeMerklePositions.physical _ 0 pub blocks out.outcomes hout hleaf ht,?_,hbytes⟩
  exact ReceiptDigestPartition.physical pub _ (ReceiptDigestPartition.extracted_rid_lengths _ 0 blocks)
    hpDigest hrDigest _ 0 ht

theorem bounded_native_height {cb : Bytes} {hint : Hint} {p : Prep} {k : WalkD0}
    {w : StateWitness} {m : MainExecutionV3} (overhead : Nat)
    (hp : prepD0 cb hint=.ok p) (hk : walkD0 cb=.ok k) (hm : m.NativeValid k w) :
    HeightPublicBytes (m.ctx k) (ZkFormal.Udr.pubOf Fp
      (Public.preparedBytes (RoutingBoundedLayout.boundedPrep p k.L k.H.shardId) overhead)) :=
  prepared_HeightPublicBytes _ overhead (m.ctx k) (prepD0_roots (p:=p) hp) (prepD0_native_height (p:=p) hp hk hm)

end ZkFormal.NearV3.Candidates.ReceiptNativeDigestBalance
