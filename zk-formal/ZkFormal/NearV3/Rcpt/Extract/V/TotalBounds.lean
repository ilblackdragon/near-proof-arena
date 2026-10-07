import ZkFormal.NearV3.Rcpt.Extract.V.TableTotals

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

/-- An enabled refund is shorter than its actual receipt layout. -/
theorem Layout.refund_le_rows {y : RS} (h : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt) :
    rfLen (rcptOf tr tt y)≤y.tot := by
  have hi := (ids_of hL h).2.2.1
  have hs : y.Ls≤64 := by
    simp only [NearSpec.AccountId.valid,Bool.and_eq_true,decide_eq_true_eq] at hi
    have hh := hi.1.2
    simpa [toBytes,rcptOf,colAt_len] using hh
  rw [rcptOf_refund_size]
  unfold RS.tot total Vt
  split <;> omega

/-- All refunds in a list fit inside that list's physical row budget. -/
theorem ListBlockWf.refund_le_rows {B : ListBlock} (h : ListBlockWf tr tt B) :
    B.refundBytes tr tt≤B.rows := by
  have hb : ∀ y∈B.receipts,rfLen (rcptOf tr tt y)≤y.tot := fun y hy => (h.layouts y hy).refund_le_rows hL
  unfold ListBlock.refundBytes ListBlock.rows
  suffices (B.receipts.map fun y => rfLen (rcptOf tr tt y)).sum≤(B.receipts.map RS.tot).sum by omega
  generalize B.receipts=xs at hb ⊢
  induction xs with
  | nil => simp
  | cons y ys ih =>
    have hy := hb y (by simp)
    have hh := ih (by intro z hz; exact hb z (by simp [hz]))
    simp only [List.map_cons,List.sum_cons]
    omega

/-- Both extracted natural totals are below the field characteristic, derived
from the unchanged physical height cap and actual receipt grammar. -/
theorem ListChain.total_bounds {s e : Nat} {bs : List ListBlock} (h : ListChain tr tt s bs e) :
    (bs.map fun B => B.receipts.length).sum<P ∧
    8+(bs.map fun B => B.refundBytes tr tt).sum<P := by
  have hn := receipt_counts_le_rows bs
  have hr := h.rows
  have he := (h.last_row hL).2.1
  have hH := height_le hL
  have hb : (bs.map fun B => B.refundBytes tr tt).sum≤(bs.map ListBlock.rows).sum := by
    have hw : ∀ B∈bs,B.refundBytes tr tt≤B.rows := fun B hB => (h.blocks B hB).refund_le_rows hL
    clear hn hr he h hH
    induction bs with
    | nil => simp
    | cons B bs ih =>
      have hB := hw B (by simp)
      have ht := ih (by intro C hC; exact hw C (by simp [hC]))
      simp only [List.map_cons,List.sum_cons]
      omega
  unfold P
  omega

end ZkFormal.NearV3.RcptV3Proof
