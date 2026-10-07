import ZkFormal.NearV3.Rcpt.Extract.V.ListCounts

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/-- The actual header registers and actual receipt layouts define the list view. -/
def ListBlock.view (tr : Trace Fp) (tt : Nat) (B : ListBlock) : ListV3 :=
  ⟨(tr.cell tt B.start (reg 8)).toNat,(tr.cell tt B.start (reg 9)).toNat,B.viewReceipts tr tt⟩

theorem ListBlock.view_length (tr : Trace Fp) (tt : Nat) (B : ListBlock) :
    (B.view tr tt).rs.length=B.receipts.length := by simp [ListBlock.view,ListBlock.viewReceipts]

theorem ListBlock.receipts_le_rows (B : ListBlock) : B.receipts.length≤B.rows := by
  suffices B.receipts.length≤(B.receipts.map RS.tot).sum by unfold ListBlock.rows; omega
  induction B.receipts with
  | nil => simp
  | cons x xs ih =>
    have hp := total_pos x.h x.Lp x.Lv x.Ls x.kt
    change 176≤x.tot at hp
    simp only [List.length_cons,List.map_cons,List.sum_cons]
    omega

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

theorem ListBlockWf.receipts_lt_P {B : ListBlock} (h : ListBlockWf tr tt B) : B.receipts.length<P := by
  have := B.receipts_le_rows
  have := h.stop_eq
  have := h.bound.2
  have := hP hL
  omega

/-- The two count registers encode the exact extracted count in the field. -/
theorem ListBlockWf.count_registers {B : ListBlock} (h : ListBlockWf tr tt B) :
    (B.receipts.length : Fp)=tr.cell tt B.start (reg 8)+256*tr.cell tt B.start (reg 9) ∧
    tr.cell tt B.start (reg 10)=0 ∧ tr.cell tt B.start (reg 11)=0 := by
  have hf := h.header
  have hfin := h.header_fin
  have hc : tr.cell tt B.start sCL=1 := by simpa using hf.st 0 (by decide)
  have hs : tr.cell tt B.start fs=1 := by simpa using hf.fs 0 (by decide)
  have hh := (hdrRow hL (r := B.start) (by omega) hc).2.2.2 hs
  rw [h.header_count hL] at hh
  exact hh

/-- Once the emitted count bytes are range checked, the header's natural count
is exactly the actual receipt count. Byte range checking remains an explicit bus obligation. -/
theorem ListBlockWf.view_count {B : ListBlock} (h : ListBlockWf tr tt B)
    (h0 : (B.view tr tt).n0<256) (h1 : (B.view tr tt).n1<256) :
    (B.view tr tt).rs.length=(B.view tr tt).n0+256*(B.view tr tt).n1 := by
  rw [B.view_length]
  apply ofNat_inj (h.receipts_lt_P hL) (by unfold P; omega)
  have hh := h.count_registers hL
  rw [natCast_add,natCast_mul]
  have hn0 : (((B.view tr tt).n0 : Nat) : Fp)=tr.cell tt B.start (reg 8) := Fp.ofNat_toNat _
  have hn1 : (((B.view tr tt).n1 : Nat) : Fp)=tr.cell tt B.start (reg 9) := Fp.ofNat_toNat _
  rw [hn0,hn1]
  exact hh.1

end ZkFormal.NearV3.RcptV3Proof
