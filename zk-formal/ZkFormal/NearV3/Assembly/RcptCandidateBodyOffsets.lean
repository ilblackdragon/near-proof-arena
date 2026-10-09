import ZkFormal.NearV3.Assembly.RcptCandidateGlobalListCounters
-- Source BodyOffsets.lean SHA256: 8ed6599ab9718a1c5cdbf43dc122d51d17a2735ac8db1076454fe020ee71aa47.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.GlobalListCounters

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/-- Exact refund encoding length, whether or not the refund is enabled. -/
theorem rcptOf_refund_length (tr : Trace Fp) (tt : Nat) (y : RS) :
    (rcptOf tr tt y).encRefund.length=129+2*y.Ls+32*y.kt := by
  cases he : y.h <;>
    simp only [RcptV.encRefund,RcptV.borshN,rcptOf,he,Bool.false_eq_true,ite_false,ite_true,
      List.length_append,List.length_cons,List.length_nil,List.length_replicate,colAt_len,
      u32r,systemN,tailN] <;> omega

theorem rcptOf_refund_size (tr : Trace Fp) (tt : Nat) (y : RS) :
    rfLen (rcptOf tr tt y)=if y.h then 129+2*y.Ls+32*y.kt else 0 := by
  unfold rfLen
  change (if y.h then (rcptOf tr tt y).encRefund.length else 0)=_
  rw [rcptOf_refund_length]

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- Actual body end offset adds the enabled extracted refund encoding length. -/
theorem Layout.body_end {y : RS} (h : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt) :
    tr.cell tt y.s o2End=tr.cell tt y.s o2+((rfLen (rcptOf tr tt y) : Nat) : Fp) := by
  have hf := Layout.start_flags hL h
  have hfin := h.fin
  have hh := (sizes hL (r := y.s) (by omega) hf.1 hf.2.1).2
  rw [h.cLs,h.ckt,h.hr] at hh
  rw [rcptOf_refund_size]
  cases he : y.h <;> simp only [he,Bool.false_eq_true,ite_false,ite_true,natCast_add,natCast_mul] at hh ⊢ <;>
    rw [hh] <;> grind

theorem Layout.last_body_end {y : RS} (h : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt) :
    tr.cell tt (y.s+y.tot-1) o2End=tr.cell tt y.s o2+((rfLen (rcptOf tr tt y) : Nat) : Fp) := by
  exact ((lay_last hL h).2 o2End o2EndC).trans (Layout.body_end hL h)

/-- Adjacent receipts chain the actual body byte offsets. -/
theorem Layout.next_body_offset {y z : RS}
    (hy : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    (hz : Layout tr tt z.s z.h z.Lp z.Lv z.Ls z.kt)
    (hs : z.s=y.s+y.tot) :
    tr.cell tt z.s o2=tr.cell tt y.s o2+((rfLen (rcptOf tr tt y) : Nat) : Fp) := by
  have hp := total_pos y.h y.Lp y.Lv y.Ls y.kt
  have hfin := hy.fin
  have he : y.s+y.tot-1+1=z.s := by unfold RS.tot at *; omega
  have hh := (brkStep hL (r := y.s+y.tot-1) (by unfold RS.tot; omega)
    (by unfold RS.tot; rw [hy.endRl,lay_last_ncl hL hy]; grind)
    (by simpa only [he] using (Layout.start_flags hL hz).1)).2.2
  rw [he] at hh
  exact hh.trans (Layout.last_body_end hL hy)

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
