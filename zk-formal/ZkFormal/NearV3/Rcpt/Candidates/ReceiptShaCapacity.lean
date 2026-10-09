import ZkFormal.NearV3.Rcpt.Candidates.AccountShaJobs

namespace ZkFormal.NearV3.Rcpt.Candidates
open ZkFormal.Near

/-- Weights of the four actual receipt-side payload families, in batch order. -/
def receiptShaWeights (pub : List Algebra.Fp) (ls : RcptV3Vs) (as : List AcctV) : List Nat :=
  (rcShaPayloads pub ls).map (fun b => Render.rowsOf b.length) ++
  ((flatR ls).flatMap (receiptShaPayloads pub)).map (fun b => Render.rowsOf b.length) ++
  (accountShaJobs as).map (fun m => Render.rowsOf m.bytes.length) ++
  (merkleShaJobs ((flatR ls).map (fun x => x.leaf))).map (fun m => Render.rowsOf m.bytes.length)

theorem receiptShaWeights_sum (pub : List Algebra.Fp) (ls : RcptV3Vs) (as : List AcctV) :
    (receiptShaWeights pub ls as).sum=
      hashRows ((rcShaPayloads pub ls).map List.length)+
      hashRows (((flatR ls).flatMap (receiptShaPayloads pub)).map List.length)+
      hashRows ((accountShaJobs as).map (fun m => m.bytes.length))+
      hashRows ((merkleShaJobs ((flatR ls).map (fun x => x.leaf))).map (fun m => m.bytes.length)) := by
  simp only [receiptShaWeights,List.sum_append,hashRows,List.map_map,Function.comp_def]

theorem receiptShaWeights_capacity (pub : List Algebra.Fp) (ls : RcptV3Vs) (as : List AcctV)
    (hr : ∀x∈flatR ls,∃r bg tok tok',x.Wf r bg tok tok')
    (ha : as=[] ∨ AcctWf as) (hac : as.length≤8192)
    (hn : (flatR ls).length≤4481) (hl : ls.length≤1984) :
    (receiptShaWeights pub ls as).sum≤1373299 := by
  have he : ∀L∈ls,∀x∈L.rs,x.enc.length≤347 := by
    intro L hL x hx
    have hm : x∈flatR ls := List.mem_flatMap.mpr ⟨L,hL,hx⟩
    obtain ⟨r,bg,tok,tok',hw⟩ := hr x hm
    exact (receipt_sha_lengths pub x hw).1
  have hrc := rc_batch_sha_bound pub ls he
  have hp := receipt_batch_sha_bound pub (flatR ls) hr
  have hm := merkleShaJobs_rows ((flatR ls).map (fun x => x.leaf))
  have hacct : hashRows ((accountShaJobs as).map (fun m => m.bytes.length))=35*as.length := by
    rcases ha with rfl|ha
    · simp [accountShaJobs,hashRows]
    · exact accountShaJobs_rows as ha
  rw [receiptShaWeights_sum,hacct,hm,List.length_map]
  omega

end ZkFormal.NearV3.Rcpt.Candidates
