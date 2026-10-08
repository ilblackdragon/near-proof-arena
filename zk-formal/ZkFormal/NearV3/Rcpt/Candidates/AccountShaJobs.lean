import ZkFormal.NearV3.Rcpt.Candidates.MerkleShaJobs
import ZkFormal.NearV3.Rcpt.Extract.AcctProof

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec ZkFormal.Near ZkFormal.Near.Render

/-- V3 account table emits only VPOST SHA preimages. VPRE is already supplied by
Val and must not be counted again through the old v1 acctMsgs constructor. -/
def accountShaJobs (as : List AcctV) : List ZkFormal.Near.Render.Msg :=
  as.map (fun a => ⟨msgId K_VPOST a.k,a.post++a.pre.drop 16⟩)

theorem accountShaJobs_count (as : List AcctV) : (accountShaJobs as).length=as.length := by
  simp [accountShaJobs]

theorem accountShaJobs_length (as : List AcctV) (h : AcctWf as) :
    ∀m∈accountShaJobs as,m.bytes.length=72 := by
  intro m hm
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
  obtain ⟨hp,ho,_⟩ := h.len a ha
  simp [List.length_drop,hp,ho]

theorem accountShaJobs_rows (as : List AcctV) (h : AcctWf as) :
    hashRows ((accountShaJobs as).map (fun m => m.bytes.length))=35*as.length := by
  have hl := accountShaJobs_length as h
  have hs : ∀xs : List ZkFormal.Near.Render.Msg, (∀m∈xs,m.bytes.length=72) →
      hashRows (xs.map (fun m => m.bytes.length))=35*xs.length := by
    intro xs hx
    induction xs with
    | nil => simp [hashRows]
    | cons x xs ih =>
      have hh := hx x (by simp)
      have hi := ih (fun x hx' => hx x (by simp [hx']))
      have h72 : ZkFormal.Near.Render.rowsOf 72=35 := by decide
      simp only [List.map_cons,hashRows,List.sum_cons,List.length_cons,hh,h72] at *
      omega
  rw [hs _ hl,accountShaJobs_count]

/-- The complete concrete receipt/account/outcome-Merkle subset retains actual
account count A, rather than silently assuming A≤receipt count. -/
theorem receipt_account_merkle_budget (pub : List Algebra.Fp) (ls : RcptV3Vs)
    (as : List AcctV) (ha : AcctWf as)
    (hr : ∀x∈flatR ls,∃r bg tok tok',x.Wf r bg tok tok') :
    64*(hashRows ((rcShaPayloads pub ls).map List.length)+
      hashRows (((flatR ls).flatMap (receiptShaPayloads pub)).map List.length)+
      hashRows ((accountShaJobs as).map (fun m => m.bytes.length))+
      hashRows ((merkleShaJobs ((flatR ls).map (fun x => x.leaf))).map (fun m => m.bytes.length)))≤
      17*receiptEncodedBytes ls+6720*(flatR ls).length+1492*ls.length+
        2240*as.length+2240*((flatR ls).length-1) := by
  have hb := receipt_payload_byte_bound pub ls hr
  rw [accountShaJobs_rows as ha,merkleShaJobs_rows,List.length_map]
  omega

end ZkFormal.NearV3.Rcpt.Candidates
