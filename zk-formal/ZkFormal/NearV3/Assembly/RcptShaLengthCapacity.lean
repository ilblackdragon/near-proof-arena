import ZkFormal.NearV3.Assembly.RcptNativeShaLengths

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Near Rcpt.Candidates

private theorem batch_bound (pub : List Algebra.Fp) (xs : List RcptE)
    (h : ∀x∈xs,x.peo.length≤133 ∧ x.leaf.length=68 ∧ x.rid.length=32) :
    hashRows ((xs.flatMap (receiptShaPayloads pub)).map List.length)≤105*xs.length := by
  induction xs with
  | nil => simp [hashRows]
  | cons x xs ih =>
    obtain ⟨hp,hl,hr⟩ := h x (by simp)
    have hb := receipt_sha_rows_of_lengths pub x hp hl hr
    have hi := ih (fun x hx=>h x (by simp [hx]))
    simp only [List.flatMap_cons,List.map_append,hashRows,List.sum_append,
      List.length_cons,Nat.mul_add,Nat.mul_one] at *
    omega

/-- The existing receipt-family capacity follows from the concrete serialization
lengths; account Wf remains the ordinary account-family input. -/
theorem receipt_jobs_capacity_lengths (pub : List Algebra.Fp) (ls : RcptV3Vs) (as : List AcctV)
    (hr : ∀x∈flatR ls,x.enc.length≤347 ∧ x.peo.length≤133 ∧ x.leaf.length=68 ∧ x.rid.length=32)
    (ha : as=[] ∨ AcctWf as) (hac : as.length≤8192)
    (hn : (flatR ls).length≤4481) (hl : ls.length≤1984) :
    ((receiptShaJobs pub ls as).map (fun m=>Render.rowsOf m.bytes.length)).sum≤1373299 := by
  have he : ∀L∈ls,∀x∈L.rs,x.enc.length≤347 := by
    intro L hL x hx
    exact (hr x (List.mem_flatMap.mpr ⟨L,hL,hx⟩)).1
  have hrc := rc_batch_sha_bound pub ls he
  have hp := batch_bound pub (flatR ls) (fun x hx=>(hr x hx).2)
  have hm := merkleShaJobs_rows ((flatR ls).map (fun x=>x.leaf))
  have hacct : hashRows ((accountShaJobs as).map (fun m=>m.bytes.length))=35*as.length := by
    rcases ha with rfl|ha
    · simp [accountShaJobs,hashRows]
    · exact accountShaJobs_rows as ha
  rw [receiptShaJobs_weights,receiptShaWeights_sum,hacct,hm,List.length_map]
  omega

end ZkFormal.NearV3.Assembly.RcptSkeleton
