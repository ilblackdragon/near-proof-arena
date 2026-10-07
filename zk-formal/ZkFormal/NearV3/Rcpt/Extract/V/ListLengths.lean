import ZkFormal.NearV3.Rcpt.Extract.V.ListChain
import ZkFormal.NearV3.Rcpt.Extract.V.Of

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/-- The encoding read from a receipt has its actual byte length, independently of byte values. -/
theorem rcptOf_enc_length (tr : Trace Fp) (tt : Nat) (y : RS) :
    (rcptOf tr tt y).enc.length=123+Vt y.Lp y.Lv y.Ls y.kt := by
  simp only [RcptV.enc, RcptV.borshN, List.length_append, rcptOf, colAt_len,
    u32r, List.length_cons, List.length_nil, tailN, Vt]
  omega

theorem rcptOf_enc_pos (tr : Trace Fp) (tt : Nat) (y : RS) :
    0<(rcptOf tr tt y).enc.length := by rw [rcptOf_enc_length]; omega

/-- Auxiliary receipt rows only increase the physical size, including refund receipts. -/
theorem rcptOf_enc_le_rows (tr : Trace Fp) (tt : Nat) (y : RS) :
    (rcptOf tr tt y).enc.length≤y.tot := by
  rw [rcptOf_enc_length]
  unfold RS.tot total
  split <;> omega

def ListBlock.viewReceipts (tr : Trace Fp) (tt : Nat) (B : ListBlock) : List RcptE :=
  B.receipts.map (rcptOf tr tt)

theorem ListBlock.encoded_le_rows (tr : Trace Fp) (tt : Nat) (B : ListBlock) :
    lOffs (B.viewReceipts tr tt) (B.viewReceipts tr tt).length≤B.rows := by
  simp only [lOffs, List.take_length, ListBlock.viewReceipts, ListBlock.rows, List.map_map, Function.comp_def]
  suffices ((B.receipts.map fun x => (rcptOf tr tt x).enc.length).sum≤(B.receipts.map RS.tot).sum) by omega
  induction B.receipts with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,List.sum_cons]; have := rcptOf_enc_le_rows tr tt x; omega

/-- Encoded lengths cannot wrap in the base field: this follows from actual rows, not view assumptions. -/
theorem ListBlockWf.encoded_lt_height {tr : Trace Fp} {tt : Nat} {B : ListBlock}
    (h : ListBlockWf tr tt B) :
    lOffs (B.viewReceipts tr tt) (B.viewReceipts tr tt).length<tr.height tt := by
  have := B.encoded_le_rows tr tt
  have := h.stop_eq
  have := h.bound.2
  omega

theorem ListBlockWf.encoded_lt_P {tr : Trace Fp} {pub : List Fp} {tt : Nat} {B : ListBlock}
    (hL : TableLocal RcptV3.table tr tt pub) (h : ListBlockWf tr tt B) :
    lOffs (B.viewReceipts tr tt) (B.viewReceipts tr tt).length<P := by
  have := h.encoded_lt_height
  have := hP hL
  omega

/-- A twelve-byte list encoding contains no receipt; no modular equality is used here. -/
theorem ListBlock.encoded_eq_twelve (tr : Trace Fp) (tt : Nat) (B : ListBlock) :
    lOffs (B.viewReceipts tr tt) (B.viewReceipts tr tt).length=12 ↔ B.receipts=[] := by
  simp only [lOffs,List.take_length,ListBlock.viewReceipts,List.map_map, Function.comp_def]
  cases he : B.receipts with
  | nil => simp
  | cons x xs =>
    simp only [List.map_cons,List.sum_cons]
    have := rcptOf_enc_pos tr tt x
    constructor
    · intro h; omega
    · intro h; cases h

/-- Every list extracted from a locally valid physical trace has a nonwrapping encoded length. -/
theorem ListChain.encoded_bounds {tr : Trace Fp} {pub : List Fp} {tt s e : Nat} {bs : List ListBlock}
    (hL : TableLocal RcptV3.table tr tt pub) (h : ListChain tr tt s bs e) :
    ∀ B∈bs, lOffs (B.viewReceipts tr tt) (B.viewReceipts tr tt).length<P := by
  intro B hb
  exact (h.blocks B hb).encoded_lt_P hL

end ZkFormal.NearV3.RcptV3Proof
