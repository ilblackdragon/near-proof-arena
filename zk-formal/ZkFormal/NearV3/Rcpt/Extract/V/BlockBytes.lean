import ZkFormal.NearV3.Rcpt.Extract.V.PrefixOffsets
import ZkFormal.NearV3.Rcpt.Extract.V.HeaderTraffic

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- Existing per-receipt byte view, positioned by exact natural prefix lengths. -/
def receiptByteMsgs (tr : Trace Fp) (tt : Nat) (pub : List Fp) (B : ListBlock)
    (jN rN bodyN k : Nat) : List Msg :=
  rcptBytesV pub (rcptOf tr tt (B.receipts.getD k default)) jN
    (12+((B.receipts.take k).map fun y => (rcptOf tr tt y).enc.length).sum)
    (bodyN+((B.receipts.take k).map fun y => rfLen (rcptOf tr tt y)).sum) (rN+k)

def blockByteMsgs (tr : Trace Fp) (tt : Nat) (pub : List Fp) (B : ListBlock)
    (jN rN bodyN : Nat) : List Msg :=
  emitAt (msgId K_RC jN) 0 (hdrBytes pub (B.view tr tt)) ++
    (List.range B.receipts.length).flatMap (receiptByteMsgs tr tt pub B jN rN bodyN)

variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

theorem ListBlockWf.receipt_bounds {B : ListBlock} (h : ListBlockWf tr tt B)
    {y : RS} (hy : y∈B.receipts) : B.start+12≤y.s ∧ y.s+y.tot≤B.stop := by
  exact seg_le_end (segsOf B.receipts) (B.start+12) h.consecutive (y.s,y.tot)
    (List.mem_map.mpr ⟨y,hy,rfl⟩)

/-- Every extracted receipt emits the existing exact V3 byte view at reconstructed offsets. -/
theorem ListBlockWf.receipt_bytes {B : ListBlock} (h : ListBlockWf tr tt B)
    (jN rN bodyN k : Nat) (hk : k<B.receipts.length)
    (hj : tr.cell tt B.start j=(jN : Fp))
    (hr : tr.cell tt B.start RcptV3.r=(rN : Fp)) (hb : tr.cell tt B.start o2=(bodyN : Fp)) :
    ((List.range' B.receipts[k].s B.receipts[k].tot).flatMap
      (fun q => rowTraffic RcptV3.interactions tr tt q pub B_BYTES true)).Perm
      ((receiptByteMsgs tr tt pub B jN rN bodyN k).map Msg.toFp) := by
  have hy := h.layouts B.receipts[k] (List.getElem_mem hk)
  have ho := h.receipt_offsets hL k hk
  have ho2 := h.receipt_body_offsets hL k hk
  have hrc := h.receipt_indices hL k hk
  rw [hb,←natCast_add] at ho2
  rw [hr,←natCast_add] at hrc
  unfold receiptByteMsgs
  rw [getD_eq_getElem' B.receipts default hk]
  apply rcpt_bytes hL hy ho ho2 hrc
  intro q hlo hhi
  have hbounds := h.receipt_bounds hL (List.getElem_mem hk)
  unfold RS.tot at hbounds
  have hc := h.constants hL (q-B.start) (by omega) j (by simp [lconsts])
  rw [show B.start+(q-B.start)=q by omega,hj] at hc
  exact hc

end ZkFormal.NearV3.RcptV3Proof
