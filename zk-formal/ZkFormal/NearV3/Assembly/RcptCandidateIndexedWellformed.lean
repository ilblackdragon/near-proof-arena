import ZkFormal.NearV3.Assembly.RcptCandidateTokenBytes
-- Source IndexedWellformed.lean SHA256: 23189a362e000dd8d16eac2d49a6cf491b29ae27ac115e3969e6c8b247901788.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.TokenBytes
import ZkFormal.NearV3.Rcpt.Extract.V.GlobalListCounters

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open ZkFormal.Near.RcptProof (sumL)

/-- Global receipt counts fit inside their actual physical row count. -/
theorem receipt_counts_le_rows (bs : List ListBlock) :
    (bs.map fun B => B.receipts.length).sum≤(bs.map ListBlock.rows).sum := by
  induction bs with
  | nil => simp
  | cons B bs ih =>
    have hh := B.receipts_le_rows
    simp only [List.map_cons,List.sum_cons]
    omega

/-- A concrete indexed item is strictly below the complete flattened length. -/
theorem receipt_prefix_lt (bs : List ListBlock) (j : Nat) (hj : j<bs.length)
    (k : Nat) (hk : k<bs[j].receipts.length) :
    ((bs.take j).map fun B => B.receipts.length).sum+k<(bs.map fun B => B.receipts.length).sum := by
  induction bs generalizing j with
  | nil => simp at hj
  | cons B bs ih =>
    cases j with
    | zero => simpa only [List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add,List.map_cons,List.sum_cons] using
        Nat.lt_of_lt_of_le hk (Nat.le_add_right B.receipts.length ((bs.map fun B => B.receipts.length).sum))
    | succ j =>
      have hh := ih j (by simpa using hj) hk
      simp only [List.take_succ_cons,List.map_cons,List.sum_cons]
      omega

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- Every globally indexed extracted receipt is semantically well formed, with no
external token/routing witness premise; the previous-version provider bound remains explicit. Token endpoints are its actual GP rows. -/
theorem ListChain.indexed_wf {e : Nat} {bs : List ListBlock} (hc : ListChain tr tt 0 bs e)
    (j : Nat) (hj : j<bs.length) (k : Nat) (hk : k<bs[j].receipts.length)
    (hprovider : (rcptOf tr tt bs[j].receipts[k]).tprev≤2^22) :
    let y := bs[j].receipts[k]
    (rcptOf tr tt y).Wf (((bs.take j).map fun B => B.receipts.length).sum+k) (pubBytes pub PH_GP 16)
      (sumL (fun i => cv tr tt (gq y.s y.Lp y.Lv y.Ls y.kt 0) (tok i)) 16)
      (sumL (fun i => bvN tr tt (gq y.s y.Lp y.Lv y.Ls y.kt i) 31 8) 16) := by
  have hw := hc.blocks _ (List.getElem_mem hj)
  have hy := hw.layouts _ (List.getElem_mem hk)
  have hr := ListBlockWf.receipt_indices hL hw k hk
  rw [ListChain.zero_global_counts hL hc j hj,←natCast_add] at hr
  have hn := receipt_prefix_lt bs j hj k hk
  have hrows := receipt_counts_le_rows bs
  have he := hc.rows
  have hfin := hc.end_padding
  have hp := hP hL
  exact wf_numbered hL hy hr (by omega) hprovider

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
