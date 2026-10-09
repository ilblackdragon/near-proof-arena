import ZkFormal.NearV3.Rcpt.Candidates.ReceiptJobOrder

namespace ZkFormal.NearV3.Rcpt.Candidates
open ZkFormal.Near

private theorem flatMap_perm_pointwise {α β : Type} (xs : List α) (f g : α→List β)
    (h : ∀x∈xs,(f x).Perm (g x)) : (xs.flatMap f).Perm (xs.flatMap g) := by
  induction xs with
  | nil => exact .refl _
  | cons x xs ih => exact (h x (by simp)).append (ih (fun x hx => h x (by simp [hx])))

def receiptCoreJobs (pub : List Algebra.Fp) (ls : RcptV3Vs) : List Render.Msg :=
  ((rcShaPayloads pub ls).zipIdx.map (fun p => ⟨msgId K_RC p.2,p.1⟩))++
  ((flatR ls).zipIdx.flatMap (fun p => receiptJobsAt pub p.2 p.1))

/-- The refund stream is public-body traffic, not an additional SHA job. -/
def refundFragments (xs : List RcptE) : List Msg :=
  xs.zipIdx.flatMap (fun p => if p.1.hr then emitAt K_RF (bOffs xs p.2) p.1.encRefund else [])

theorem rcBatch_bytes (pub : List Algebra.Fp) (ls : RcptV3Vs) :
    (List.range ls.length).flatMap (fun j => emitAt (msgId K_RC j) 0
      (hdrBytes pub (ls.getD j default)++(ls.getD j default).rs.flatMap (fun x => x.enc)))=
    jobBytes ((rcShaPayloads pub ls).zipIdx.map (fun p => ⟨msgId K_RC p.2,p.1⟩)) := by
  have h := indexed_flatMap ls 0 (fun j L =>
    emitAt (msgId K_RC j) 0 (hdrBytes pub L++L.rs.flatMap (fun x => x.enc)))
  simpa [jobBytes,rcShaPayloads,List.zipIdx_map,List.flatMap_map] using h

theorem receipt_core_bytes (pub : List Algebra.Fp) (ls : RcptV3Vs) :
    (rcptSends3 pub ls B_BYTES).Perm
      (jobBytes (receiptCoreJobs pub ls)++refundFragments (flatR ls)) := by
  let rc := fun j => emitAt (msgId K_RC j) 0
    (hdrBytes pub (ls.getD j default)++(ls.getD j default).rs.flatMap (fun x => x.enc))
  let other := fun j => (located ls j).flatMap (fun (r,_,x) =>
    (if x.hr then emitAt K_RF (bOffs (flatR ls) r) x.encRefund else [])++jobBytes (receiptJobsAt pub r x))
  have hp := flatMap_perm_pointwise (List.range ls.length) _ (fun j => rc j++other j)
    (fun j _ => sourceList_bytes_perm pub ls j)
  have hs := flatMap_split_perm (List.range ls.length) rc other
  have h : (rcptSends3 pub ls B_BYTES).Perm
      ((List.range ls.length).flatMap rc++(List.range ls.length).flatMap other) := by
    simpa [rcptSends3,B_BYTES,B_RCL] using hp.trans hs
  have he : (List.range ls.length).flatMap other=
      (flatR ls).zipIdx.flatMap (fun p =>
        (if p.1.hr then emitAt K_RF (bOffs (flatR ls) p.2) p.1.encRefund else [])++
        jobBytes (receiptJobsAt pub p.2 p.1)) := by
    simpa [other] using located_global_order ls 0 (fun r x =>
      (if x.hr then emitAt K_RF (bOffs (flatR ls) r) x.encRefund else [])++jobBytes (receiptJobsAt pub r x))
  rw [he] at h
  have ht := flatMap_split_perm (flatR ls).zipIdx
    (fun p => if p.1.hr then emitAt K_RF (bOffs (flatR ls) p.2) p.1.encRefund else [])
    (fun p => jobBytes (receiptJobsAt pub p.2 p.1))
  have ht' := ht.trans List.perm_append_comm
  have hh := h.trans (ht'.append_left ((List.range ls.length).flatMap rc))
  dsimp only [rc] at hh
  rw [rcBatch_bytes] at hh
  simpa only [receiptCoreJobs,jobBytes,List.flatMap_append,List.flatMap_assoc,
    refundFragments,List.append_assoc] using hh

end ZkFormal.NearV3.Rcpt.Candidates
