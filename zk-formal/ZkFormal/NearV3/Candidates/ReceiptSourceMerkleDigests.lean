import ZkFormal.NearV3.Candidates.ReceiptAcceptedMerkleDigests
import ZkFormal.NearV3.Candidates.ReceiptGatedShaBytes
import ZkFormal.NearV3.Assembly.RcptShaByteContract
import ZkFormal.NearV3.Assembly.RcptCanonicalShaCapacity
import ZkFormal.NearV3.Candidates.ReceiptSourceInputs
import ZkFormal.NearV3.Candidates.ReceiptSourceDigestBridge
import ZkFormal.NearV3.Candidates.ReceiptPreparedFinalPublic
import ZkFormal.NearV3.Candidates.ReceiptGatedShaJobs
import ZkFormal.NearV3.Assembly.RcptGasPrepared

namespace ZkFormal.NearV3.Candidates.ReceiptSourceMerkleDigests
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Assembly
open RcptSkeleton RcptV3Proof Rcpt.Candidates Sched RcptV3

/-- Receipt/Merkle local and digest balance for the same accepted native run and
actual normalized prepared public bytes. All public header bindings used here are derived from nativeHint preparation
and checker acceptance; account traffic and native input-plan correspondences remain explicit. -/
theorem native {budget : Nat} {cb wb raw : Bytes} {p : Prep} {k : WalkD0}
    {w : StateWitness} {m : MainExecutionV3}
    (hp : prepD0 cb (nativeHint k w m)=.ok p) (hk : walkD0 cb=.ok k)
    (hd : decodeStateWitness raw=.ok w) (hdecode : decodeW wb=.ok w)
    (ha : RelD0a budget cb wb) (hm : m.NativeValid k w)
    (overhead : Nat)
    (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (constants : ReceiptPlan→Nat→Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (as : List AcctV) (hAcct : as=[] ∨ AcctWf as) (hac : as.length≤8192)
    (hab : ∀M∈accountShaJobs as,∀b∈M.bytes,b<256) (trA : Trace Fp) (tA : Nat) :
    let lists:=sourceInputLists (m.ctx k) p.lists w.entries
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
            (sourceRcShaJobs k.H.shardId p.lists w.entries++jobsToSha (accountShaJobs as))) msg) ∧
        ReceiptGatedShaJobs.rcJobs pub ls (Public.sourceDup p.lists)=
          sourceRcShaJobs k.H.shardId p.lists w.entries ∧
        (Sha.Gen.honestRows (ReceiptGatedShaJobs.jobs pub ls as (Public.sourceDup p.lists))).length≤1373299 ∧
        (∀M∈ReceiptGatedShaJobs.jobs pub ls as (Public.sourceDup p.lists),∀b∈M.bytes,b<256) ∧
        ∀msg,cnt (Sha.Gen.expectedBytes (ReceiptGatedShaJobs.jobs pub ls as (Public.sourceDup p.lists))) msg+
          cnt (refundFragments (flatR ls)) msg=
          tableBusCount ReceiptCandidateRouting.candidateTable.interactions trR 0 pub B_BYTES true msg+
          tableBusCount AccountEmpty.table.interactions trA tA pub B_BYTES true msg+
          tableBusCount MerkleEmpty.table.interactions (MerkleRender.outcomeTrace m.result.outcomes pub)
            T_MRK pub B_BYTES true msg := by
  dsimp only
  intro hA
  have hc : checkD0 cb wb=.ok () := by
    have h:=ha.1
    unfold RelD0 acceptsD0 at h
    cases he : checkD0 cb wb with
    | error e => simp [he] at h
    | ok u => cases u;rfl
  obtain ⟨hsource,hls,hw,hne,hn,hflags⟩:=ReceiptSourceInputs.admitted (m.ctx k) ha hp hk hdecode hd
  obtain ⟨hgas,hprice⟩:=ReceiptSourceInputs.gas ha hp hk hm
  obtain ⟨mid,so,steps,hsched,hledger,hlocal,hmerkle,blocks,e,hchain,ht,hleaf,hpeo,hrid,hpos,hdig,hmdig,hfull,hbytes⟩ :=
    ReceiptAcceptedMerkleDigests.native hp hk hd hdecode hc hm overhead
      (sourceInputLists (m.ctx k) p.lists w.entries) hsource hls hw hne hn hflags hgas
      accountId accessId constants digests fallback headerFallback hprice as trA tA hA
  have hpre := canonical_source_rc_jobs k.H.shardId (m.ctx k) p.lists w.entries 22 _ _
    (nativeDigests (m.ctx k) digests) _ _ hw (by decide)
    (ReceiptPreparedFinalPublic.own_public overhead hp hk hdecode hc hm) hlocal blocks e hchain
  have hrc := ReceiptSourceDigestBridge.jobs_source _ _ k.H.shardId p.lists w.entries hpre
  have hrun : applyNewChunk prims (m.ctx k) m.pre
      ((sourceInputLists (m.ctx k) p.lists w.entries).flatten.map Input.receipt)=.ok m.result := by
    rw [hls];exact hm.run
  have hcap:=canonical_native_sha_capacity k.H.shardId (m.ctx k) k
    (sourceInputLists (m.ctx k) p.lists w.entries) accountId accessId 22 _ _ digests _ _
    hw hflags (by decide) hlocal blocks e hchain hp hsource hrun hgas as hAcct hac
  have hbytesRange:=canonical_native_sha_job_bytes k.H.shardId (m.ctx k) k
    (sourceInputLists (m.ctx k) p.lists w.entries) accountId accessId 22 _ _ digests _ _
    hw hflags (ReceiptNativeMerkleDigests.bounded_native_height overhead hp hk hm) (by decide)
    hlocal blocks e hchain (ReceiptPreparedFinalPublic.own_public overhead hp hk hdecode hc hm) as hab
  refine ⟨mid,so,steps,hsched,hledger,hlocal,hmerkle,blocks,e,hchain,ht,hleaf,hpeo,hrid,hpos,hdig,hmdig,?_,hrc,?_,ReceiptGatedShaBytes.bytes _ _ as _ hbytesRange,hbytes⟩
  · intro msg
    simpa only [hrc] using hfull msg
  · rw [ReceiptGatedShaJobs.rows_unchanged,jobsToSha_rows]
    exact hcap

end ZkFormal.NearV3.Candidates.ReceiptSourceMerkleDigests
