import ZkFormal.NearV3.Assembly.RcptCandidateRepairedTraffic
import ZkFormal.NearV3.Rcpt.Candidates.ReceiptJobOrder
import ZkFormal.NearV3.Rcpt.Candidates.ShaJobBridge
namespace ZkFormal.NearV3.Candidates.ReceiptDigestPartition
open ZkFormal.Near Rcpt.Candidates

theorem jobs_digests (jobs : List Render.Msg) :
    Sha.Gen.expectedDigests (jobsToSha jobs)=jobs.map Render.digestMsg := by
  induction jobs with
  | nil=>rfl
  | cons j js ih=>simpa [jobsToSha,Sha.Gen.expectedDigests,Render.digestMsg,Render.shaN,Render.ofNats,Render.toNats] using congrArg (List.cons (Render.digestMsg j)) ih

theorem receipt (pub : List Algebra.Fp) (r : Nat) (x : RcptE)
    (hlen : x.rid.length=32)
    (hp : x.peoh=(NearSpec.sha256 (x.peo.map UInt8.ofNat)).map UInt8.toNat)
    (hr : x.hr=true→x.rfid=(NearSpec.sha256
      ((x.rid++pubBytes pub PH_HEIGHT 8++List.replicate 8 0).map UInt8.ofNat)).map UInt8.toNat) :
    (Sha.Gen.expectedDigests (jobsToSha (receiptJobsAt pub r x))).Perm
      (rRecvs r x B_DIGEST++[Render.digestMsg ⟨msgId K_LEAF r,x.leaf⟩]) := by
  rw [jobs_digests]
  cases hf : x.hr with
  | false=>simp [receiptJobsAt,rRecvs,hf,Render.digestMsg,digMsg,hp,Render.shaN,Render.ofNats,Render.toNats]
  | true=>
    have hl : (x.rid++pubBytes pub PH_HEIGHT 8++List.replicate 8 0).length=48 := by
      simp [hlen,pubBytes]
    simp only [receiptJobsAt,hf,ite_true,List.map_cons,List.map_nil,
      rRecvs,List.cons_append,List.nil_append]
    simp only [Render.digestMsg,digMsg,hl,hp,hr hf,Render.shaN,Render.ofNats,Render.toNats]
    exact List.perm_middle (l₁:=[_,_]) (l₂:=[])

private theorem flatMap_perm {α β : Type} (xs : List α) (f g : α→List β)
    (h : ∀x∈xs,(f x).Perm (g x)) : (xs.flatMap f).Perm (xs.flatMap g) := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>exact (h x (by simp)).append (ih (by intro y hy;exact h y (by simp [hy])))

def jobs (pub : List Algebra.Fp) (ls : RcptV3Vs) : List Render.Msg :=
  (flatR ls).zipIdx.flatMap (fun p=>receiptJobsAt pub p.2 p.1)

def leafDigests (ls : RcptV3Vs) : List Msg :=
  (flatR ls).zipIdx.flatMap (fun p=>[Render.digestMsg ⟨msgId K_LEAF p.2,p.1.leaf⟩])

/-- Per-receipt SHA outputs split exactly into PEO/RID receipt consumers and
LEAF Merkle consumers; global receipt indices and all occurrences are retained. -/
theorem partition (pub : List Algebra.Fp) (ls : RcptV3Vs)
    (hl : ∀x∈flatR ls,x.rid.length=32)
    (hp : ∀x∈flatR ls,x.peoh=(NearSpec.sha256 (x.peo.map UInt8.ofNat)).map UInt8.toNat)
    (hr : ∀x∈flatR ls,x.hr=true→x.rfid=(NearSpec.sha256
      ((x.rid++pubBytes pub PH_HEIGHT 8++List.replicate 8 0).map UInt8.ofNat)).map UInt8.toNat) :
    (Sha.Gen.expectedDigests (jobsToSha (jobs pub ls))).Perm
      (rcptRecvs3 ls B_DIGEST++leafDigests ls) := by
  rw [jobs_digests]
  simp only [jobs,List.map_flatMap]
  have h:=flatMap_perm (flatR ls).zipIdx
    (fun p=>(receiptJobsAt pub p.2 p.1).map Render.digestMsg)
    (fun p=>rRecvs p.2 p.1 B_DIGEST++[Render.digestMsg ⟨msgId K_LEAF p.2,p.1.leaf⟩]) (by
      intro p hp'
      have hm : p.1∈flatR ls := by
        have hh : p.1∈(flatR ls).zipIdx.map Prod.fst:=List.mem_map.mpr ⟨p,hp',rfl⟩
        rw [List.zipIdx_map_fst] at hh
        exact hh
      simpa only [jobs_digests] using receipt pub p.2 p.1 (hl _ hm) (hp _ hm) (hr _ hm))
  have ho:=located_global_order ls 0 (fun r x=>rRecvs r x B_DIGEST)
  simp only [Nat.zero_add] at ho
  exact h.trans (by
    rw [show rcptRecvs3 ls B_DIGEST=_ from ho]
    exact flatMap_split_perm _ _ _)

theorem physical (pub : List Algebra.Fp) (ls : RcptV3Vs)
    (hl : ∀x∈flatR ls,x.rid.length=32)
    (hp : ∀x∈flatR ls,x.peoh=(NearSpec.sha256 (x.peo.map UInt8.ofNat)).map UInt8.toNat)
    (hr : ∀x∈flatR ls,x.hr=true→x.rfid=(NearSpec.sha256
      ((x.rid++pubBytes pub PH_HEIGHT 8++List.replicate 8 0).map UInt8.ofNat)).map UInt8.toNat)
    (tr : Air.Trace Algebra.Fp) (t : Nat)
    (ht : TableTraffic Assembly.ReceiptCandidateRouting.candidateTable.interactions tr t pub (rcptTraffic3 pub ls))
    (msg : List Algebra.Fp) :
    cnt (Sha.Gen.expectedDigests (jobsToSha (jobs pub ls))) msg=
      Air.tableBusCount Assembly.ReceiptCandidateRouting.candidateTable.interactions tr t pub B_DIGEST false msg+
        cnt (leafDigests ls) msg := by
  have hc:=((partition pub ls hl hp hr).map Msg.toFp).count_eq msg
  rw [(ht B_DIGEST msg).2]
  simpa only [cnt,rcptTraffic3,List.map_append,List.count_append] using hc

theorem extracted_rid_lengths (tr : Air.Trace Algebra.Fp) (t : Nat) (bs : List RcptV3Proof.ListBlock) :
    ∀x∈flatR (bs.map (RcptV3Proof.ListBlock.view tr t)),x.rid.length=32 := by
  intro x hx
  obtain ⟨L,hL,hx⟩:=List.mem_flatMap.mp hx
  obtain ⟨B,hB,rfl⟩:=List.mem_map.mp hL
  change x∈B.receipts.map (RcptV3Proof.rcptOf tr t) at hx
  obtain ⟨y,hy,rfl⟩:=List.mem_map.mp hx
  simp [RcptV3Proof.rcptOf,RcptV3Proof.colAt]

end ZkFormal.NearV3.Candidates.ReceiptDigestPartition
