import ZkFormal.NearV3.Candidates.ReceiptNativeMerkleDigests
import ZkFormal.NearV3.Candidates.ReceiptFullDigestResidual
import ZkFormal.NearV3.Assembly.RcptGasPrepared

namespace ZkFormal.NearV3.Candidates.ReceiptPreparedMerkleDigests
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Assembly
open RcptSkeleton RcptV3Proof Rcpt.Candidates Sched RcptV3

/-- Receipt/Merkle local and digest balance for the same accepted native run and
actual normalized prepared public bytes. Public height, price and outcome-root
bindings are derived; final receipt body/count/token and own-shard bindings remain explicit. -/
theorem native {cb wb raw : Bytes} {hint : Hint} {p : Prep} {k : WalkD0}
    {w : StateWitness} {m : MainExecutionV3}
    (hp : prepD0 cb hint=.ok p) (hk : walkD0 cb=.ok k)
    (hd : decodeStateWitness raw=.ok w) (hdecode : decodeW wb=.ok w)
    (hc : checkD0 cb wb=.ok ()) (hm : m.NativeValid k w)
    (own overhead : Nat) (lists : List (List Input))
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
    FinalPublicBytes lists m.result pub →
    (∀j,j<8→pub.getD (PH_OWN+j) 0=Fp.ofNat (((u64 own).getD j 0).toNat)) →
    (∀msg,tableBusCount AccountEmpty.table.interactions trA tA pub B_BYTES true msg=
      cnt (acctV3Sends as B_BYTES) msg) →
    ∃mid so steps,schedStep prims (m.ctx k) m.pre=.ok (mid,so) ∧
      nativeDepositLedger (m.ctx k) ⟨mid,[],[],0,0⟩ (lists.flatten.map Input.receipt)=some steps ∧
      let trR:=RoutingQCandidate.patchTrace (booleanReceiptTrace own (m.ctx k) lists 22
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
        (∀msg,cnt (Sha.Gen.expectedDigests (jobsToSha (receiptShaJobs pub ls as))) msg=
          tableBusCount ReceiptCandidateRouting.candidateTable.interactions trR 0 pub B_DIGEST false msg+
          tableBusCount MerkleEmpty.table.interactions (MerkleRender.outcomeTrace m.result.outcomes pub)
            T_MRK pub B_DIGEST false msg+
          cnt (Sha.Gen.expectedDigests (jobsToSha
            (ReceiptFullDigestResidual.rcJobs pub ls++accountShaJobs as))) msg) ∧
        ∀msg,cnt (Sha.Gen.expectedBytes (jobsToSha (receiptShaJobs pub ls as))) msg+
          cnt (refundFragments (flatR ls)) msg=
          tableBusCount ReceiptCandidateRouting.candidateTable.interactions trR 0 pub B_BYTES true msg+
          tableBusCount AccountEmpty.table.interactions trA tA pub B_BYTES true msg+
          tableBusCount MerkleEmpty.table.interactions (MerkleRender.outcomeTrace m.result.outcomes pub)
            T_MRK pub B_BYTES true msg := by
  dsimp only
  intro hpub hown hA
  have hrun : applyNewChunk prims (m.ctx k) m.pre (lists.flatten.map Input.receipt)=.ok m.result := by
    rw [hls]
    exact hm.run
  have hgp := prepared_GasPublicBytes (RoutingBoundedLayout.boundedPrep p k.L k.H.shardId)
    overhead (m.ctx k) (by exact prepD0_roots (p:=p) hp)
    (by change p.hdr.gasPrice=(m.ctx k).gasPrice; exact prepD0_native_gasPrice hp hk hm)
  obtain ⟨mid,so,steps,hsched,hledger,hlocal,hmerkle,blocks,e,hchain,ht,hleaf,hpeo,hrid,hpos,hdig,hmdig,hbytes⟩ :=
    ReceiptNativeMerkleDigests.native hp hk hd own (m.ctx k) lists hsource hls hw hne hn hflags
    hrun hgas accountId accessId constants _ digests fallback headerFallback
    (ReceiptNativeMerkleDigests.bounded_native_outcome overhead hp hk hdecode hc hm)
    (ReceiptNativeMerkleDigests.bounded_native_height overhead hp hk hm)
    hgp hprice hpub hown as trA tA hA

  have hout : m.result.outcomes.length≤4481 := by
    rw [applyNewChunk_outcomes prims hm.run,List.length_map]
    exact applyNewChunk_receipt_bound hm.run hgas
  refine ⟨mid,so,steps,hsched,hledger,hlocal,hmerkle,blocks,e,hchain,ht,hleaf,hpeo,hrid,hpos,hdig,hmdig,?_,hbytes⟩
  intro msg
  exact ReceiptFullDigestResidual.physical _ _ m.result.outcomes hout hleaf
    (ReceiptNativeMerkleDigests.bounded_native_outcome overhead hp hk hdecode hc hm)
    (ReceiptDigestPartition.extracted_rid_lengths _ 0 blocks) hpeo hrid _ 0 ht as msg

end ZkFormal.NearV3.Candidates.ReceiptPreparedMerkleDigests
