import ZkFormal.NearV3.Rcpt.Candidates.ReceiptShaCapacity
import ZkFormal.NearV3.Rcpt.Candidates.FourShaJobAllocator

namespace ZkFormal.NearV3.Rcpt.Candidates
open ZkFormal.Near

/-- Complete messages, with the same global receipt indices as `rSends`. -/
def receiptJobsAt (pub : List Algebra.Fp) (r : Nat) (x : RcptE) : List Render.Msg :=
  [⟨msgId K_PEO r,x.peo⟩,⟨msgId K_LEAF r,x.leaf⟩] ++
  if x.hr then [⟨msgId K_RID r,x.rid++pubBytes pub PH_HEIGHT 8++List.replicate 8 0⟩] else []

theorem receiptJobsAt_payloads (pub : List Algebra.Fp) (r : Nat) (x : RcptE) :
    (receiptJobsAt pub r x).map Render.Msg.bytes=receiptShaPayloads pub x := by
  cases h : x.hr <;> simp [receiptJobsAt,receiptShaPayloads,h]

/-- RC includes its complete header even for an empty source occurrence. -/
def receiptShaJobs (pub : List Algebra.Fp) (ls : RcptV3Vs) (as : List AcctV) : List Render.Msg :=
  ((rcShaPayloads pub ls).zipIdx.map (fun p => ⟨msgId K_RC p.2,p.1⟩)) ++
  ((flatR ls).zipIdx.flatMap (fun p => receiptJobsAt pub p.2 p.1)) ++
  accountShaJobs as ++ merkleShaJobs ((flatR ls).map (fun x => x.leaf))

private theorem zipIdx_map_ignore {α β : Type} (xs : List α) (f : α→β) (n : Nat) :
    (xs.zipIdx n).map (fun p => f p.1)=xs.map f := by
  induction xs generalizing n with
  | nil => simp
  | cons x xs ih => simp [List.zipIdx_cons,ih]

private theorem zipIdx_flatMap_ignore {α β : Type} (xs : List α) (f : α→List β) (n : Nat) :
    (xs.zipIdx n).flatMap (fun p => f p.1)=xs.flatMap f := by
  induction xs generalizing n with
  | nil => simp
  | cons x xs ih => simp [List.zipIdx_cons,ih]

theorem receiptShaJobs_weights (pub : List Algebra.Fp) (ls : RcptV3Vs) (as : List AcctV) :
    (receiptShaJobs pub ls as).map (fun m => Render.rowsOf m.bytes.length)=
      receiptShaWeights pub ls as := by
  simp only [receiptShaJobs,receiptShaWeights,List.map_append,List.map_map,
    Function.comp_def,List.map_flatMap]
  have hj : ∀r x,(receiptJobsAt pub r x).map (fun m => Render.rowsOf m.bytes.length)=
      (receiptShaPayloads pub x).map (fun b => Render.rowsOf b.length) := by
    intro r x
    rw [←receiptJobsAt_payloads pub r x,List.map_map]
    rfl
  simp only [hj]
  rw [zipIdx_map_ignore (rcShaPayloads pub ls) (fun b => Render.rowsOf b.length) 0,
    zipIdx_flatMap_ignore (flatR ls) (fun x => (receiptShaPayloads pub x).map (fun b => Render.rowsOf b.length)) 0]

theorem receiptShaJobs_capacity (pub : List Algebra.Fp) (ls : RcptV3Vs) (as : List AcctV)
    (hr : ∀x∈flatR ls,∃r bg tok tok',x.Wf r bg tok tok')
    (ha : as=[] ∨ AcctWf as) (hac : as.length≤8192)
    (hn : (flatR ls).length≤4481) (hl : ls.length≤1984) :
    ((receiptShaJobs pub ls as).map (fun m => Render.rowsOf m.bytes.length)).sum≤1373299 := by
  rw [receiptShaJobs_weights]
  exact receiptShaWeights_capacity pub ls as hr ha hac hn hl

/-- Full-object four-bin allocation with the receipt batch constructed here.
The other three families retain their explicit, independently proved bounds. -/
theorem allocate_receipt_batch (pub : List Algebra.Fp) (ls : RcptV3Vs) (as : List AcctV)
    (scheduler native source : List Render.Msg)
    (hr : ∀x∈flatR ls,∃r bg tok tok',x.Wf r bg tok tok')
    (ha : as=[] ∨ AcctWf as) (hac : as.length≤8192)
    (hn : (flatR ls).length≤4481) (hl : ls.length≤1984)
    (hs : (scheduler.map (fun m => Render.rowsOf m.bytes.length)).sum≤1663260)
    (hv : (native.map (fun m => Render.rowsOf m.bytes.length)).sum≤2925275)
    (hp : (source.map (fun m => Render.rowsOf m.bytes.length)).sum≤8932712)
    (hm : ∀m∈source,Render.rowsOf m.bytes.length≤35) :
    let bins := fourShaJobBins (fun m : Render.Msg => Render.rowsOf m.bytes.length)
      scheduler native (receiptShaJobs pub ls as) source
    bins.length=4 ∧
      (∀bin∈bins,(bin.map (fun m => Render.rowsOf m.bytes.length)).sum≤2^22) ∧
      bins.flatten.Perm (scheduler++native++receiptShaJobs pub ls as++source) := by
  exact ⟨(fourShaJobBins_fit _ _ _ _ _ hs hv
    (receiptShaJobs_capacity pub ls as hr ha hac hn hl) hp hm).1,
    (fourShaJobBins_fit _ _ _ _ _ hs hv
    (receiptShaJobs_capacity pub ls as hr ha hac hn hl) hp hm).2,
    fourShaJobBins_preserve _ _ _ _ _⟩

end ZkFormal.NearV3.Rcpt.Candidates
