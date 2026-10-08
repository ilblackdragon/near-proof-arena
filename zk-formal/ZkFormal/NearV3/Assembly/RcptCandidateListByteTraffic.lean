import ZkFormal.NearV3.Assembly.RcptCandidateBlockBytes
-- Source ListByteTraffic.lean SHA256: 3574a1460d7a0e18a01ca828cf03c4fe1e9b968b0cf410fa5795132a52dece8e.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.BlockBytes

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

private theorem flatMap_perm {α β : Type} (xs : List α) (f g : α → List β)
    (h : ∀ x∈xs, (f x).Perm (g x)) : (xs.flatMap f).Perm (xs.flatMap g) := by
  induction xs with
  | nil => exact .refl _
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    exact (h x (by simp)).append (ih (by intro y hy; exact h y (by simp [hy])))

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- The whole physical interval of a list emits its header and positioned receipt byte views. -/
theorem ListBlockWf.bytes_traffic {B : ListBlock} (h : ListBlockWf tr tt B)
    (jN rN bodyN : Nat) (hjP : jN<P) (hj : tr.cell tt B.start j=(jN : Fp))
    (hr : tr.cell tt B.start RcptV3.r=(rN : Fp)) (hb : tr.cell tt B.start o2=(bodyN : Fp)) :
    ((List.range' B.start B.rows).flatMap
      (fun q => rowTraffic RcptV3.interactions tr tt q pub B_BYTES true)).Perm
      ((blockByteMsgs tr tt pub B jN rN bodyN).map Msg.toFp) := by
  have hhead := ListBlockWf.header_bytes_traffic hL h
  have hjn : (tr.cell tt B.start j).toNat=jN := by rw [hj,toNat_natCast,Nat.mod_eq_of_lt hjP]
  rw [hjn] at hhead
  have hs := range'_segs (segsOf B.receipts) (B.start+12) h.consecutive
  rw [receipt_end_sum B.receipts (B.start+12) h.consecutive,Nat.add_sub_cancel_left] at hs
  unfold ListBlock.rows blockByteMsgs
  rw [←List.range'_append_1,List.flatMap_append,List.map_append]
  apply List.Perm.append
  · rw [List.range'_eq_map_range,List.flatMap_map]
    exact List.Perm.of_eq hhead
  · rw [hs]
    simp only [segsOf,List.flatMap_map,List.flatMap_assoc]
    rw [flatMap_eq_range B.receipts, List.map_flatMap]
    apply flatMap_perm
    intro k hk
    have hk := List.mem_range.mp hk
    rw [getD_eq_getElem' B.receipts default hk]
    exact ListBlockWf.receipt_bytes hL h jN rN bodyN k hk hj hr hb

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
