import ZkFormal.NearV3.Rcpt.Candidates.NativeShaTraffic
import ZkFormal.Near.Extract.RcptOf

namespace ZkFormal.NearV3.Rcpt.Candidates
open ZkFormal.Near

theorem receiptJobsAt_bytes (pub : List Algebra.Fp) (xs : List RcptE)
    (j r off : Nat) (x : RcptE) :
    rSends pub xs j r off x B_BYTES=
      emitAt (msgId K_RC j) off x.enc ++
      (if x.hr then emitAt K_RF (bOffs xs r) x.encRefund else []) ++
      jobBytes (receiptJobsAt pub r x) := by
  cases h : x.hr <;> simp [rSends,receiptJobsAt,jobBytes,h,List.append_assoc]

theorem accountJobs_bytes (as : List AcctV) :
    jobBytes (accountShaJobs as)=acctV3Sends as B_BYTES := by
  simp [jobBytes,accountShaJobs,acctV3Sends,B_BYTES,B_VBYTES,List.flatMap_map,Function.comp_def]

/-- Sequential receipt segments reassemble without requiring a receipt validity
assumption or dropping empty encodings. -/
theorem receiptChunks_bytes (id off : Nat) (xs : List RcptE) :
    emitAt id off (xs.flatMap (fun x => x.enc))=
      (List.range xs.length).flatMap (fun i =>
        emitAt id (off+((xs.take i).map (fun x => x.enc.length)).sum)
          (xs.getD i default).enc) := by
  induction xs generalizing off with
  | nil => simp [emitAt]
  | cons x xs ih =>
    rw [List.flatMap_cons,RcptProof.emitAt_append,ih]
    simp only [List.length_cons,List.range_succ_eq_map,List.flatMap_cons,List.flatMap_map,
      Function.comp_def,List.getD_cons_zero,List.getD_cons_succ,List.take_zero,List.map_nil,
      List.sum_nil,Nat.add_zero,List.take_succ_cons,List.map_cons,List.sum_cons]
    simp only [Nat.add_assoc]

theorem rcJob_bytes (pub : List Algebra.Fp) (j : Nat) (L : ListV3) :
    emitAt (msgId K_RC j) 0 (hdrBytes pub L++L.rs.flatMap (fun x => x.enc))=
      emitAt (msgId K_RC j) 0 (hdrBytes pub L) ++
      (List.range L.rs.length).flatMap (fun i =>
        emitAt (msgId K_RC j) (lOffs L.rs i) (L.rs.getD i default).enc) := by
  rw [RcptProof.emitAt_append,receiptChunks_bytes]
  have hh : (hdrBytes pub L).length=12 := by simp [hdrBytes,pubBytes]
  simp only [hh,Nat.zero_add,lOffs]

theorem flatMap_split_perm {α β : Type} (xs : List α) (f g : α→List β) :
    (xs.flatMap (fun x => f x++g x)).Perm (xs.flatMap f++xs.flatMap g) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    have h := ih.append_left (f x++g x)
    have hs := (List.perm_append_comm_assoc (g x) (xs.flatMap f) (xs.flatMap g)).append_left (f x)
    exact (by simpa only [List.append_assoc] using h.trans (by simpa only [List.append_assoc] using hs))

/-- Per-list byte traffic separates into its one complete RC job and the exact
remaining receipt jobs/refund fragments; no ID-disjointness assumption is used. -/
theorem sourceList_bytes_perm (pub : List Algebra.Fp) (ls : RcptV3Vs) (j : Nat) :
    (emitAt (msgId K_RC j) 0 (hdrBytes pub (ls.getD j default)) ++
      (located ls j).flatMap (fun (r,o,x) => rSends pub (flatR ls) j r o x B_BYTES)).Perm
    (emitAt (msgId K_RC j) 0 (hdrBytes pub (ls.getD j default)++
       (ls.getD j default).rs.flatMap (fun x => x.enc)) ++
      (located ls j).flatMap (fun (r,_,x) =>
        (if x.hr then emitAt K_RF (bOffs (flatR ls) r) x.encRefund else [])++
        jobBytes (receiptJobsAt pub r x))) := by
  have hsplit := flatMap_split_perm (located ls j)
    (fun p => emitAt (msgId K_RC j) p.2.1 p.2.2.enc)
    (fun p => (if p.2.2.hr then emitAt K_RF (bOffs (flatR ls) p.1) p.2.2.encRefund else [])++
      jobBytes (receiptJobsAt pub p.1 p.2.2))
  have hr : (located ls j).flatMap (fun p => emitAt (msgId K_RC j) p.2.1 p.2.2.enc)=
      (List.range (ls.getD j default).rs.length).flatMap (fun i =>
        emitAt (msgId K_RC j) (lOffs (ls.getD j default).rs i)
          ((ls.getD j default).rs.getD i default).enc) := by
    simp only [located,List.flatMap_map]
  have h := hsplit.append_left (emitAt (msgId K_RC j) 0 (hdrBytes pub (ls.getD j default)))
  rw [hr] at h
  rw [rcJob_bytes]
  simpa only [receiptJobsAt_bytes,List.append_assoc] using h

end ZkFormal.NearV3.Rcpt.Candidates
