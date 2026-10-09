import ZkFormal.NearV3.Rcpt.Extract.V.ReceiptOffsets

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

/-- A list header finishes with offset twelve and no receipt increment. -/
theorem ListBlockWf.header_end {B : ListBlock} (h : ListBlockWf tr tt B) :
    tr.cell tt (B.start+11) oEnd=12 ∧ tr.cell tt (B.start+11) cj=0 ∧
    tr.cell tt (B.start+11) rl=0 ∧
    tr.cell tt (B.start+11) rl+tr.cell tt (B.start+11) sCL*tr.cell tt (B.start+11) fe=1 := by
  have hf := h.header
  have hn := h.header_fin
  have hc := hf.st 11 (by omega)
  have he : tr.cell tt (B.start+11) fe=1 := by simpa using hf.fe 11 (by omega)
  have hr := fld_rl0 hL (by omega) hf (by simp [states]) (by decide) (by decide) 11 (by omega)
  have hh := hdrRow hL (r := B.start+11) (by omega) hc
  refine ⟨hh.2.1,hh.1,hr,?_⟩
  rw [hr,hc,he]
  grind

/-- The first receipt following a header starts at the canonical list offset twelve. -/
theorem ListBlockWf.first_offset {B : ListBlock} (h : ListBlockWf tr tt B)
    {y : RS} (hy : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    (hs : y.s=B.start+12) :
    tr.cell tt y.s o=12 ∧ tr.cell tt y.s cj=1 := by
  have hh := h.header_end hL
  have hn := h.header_fin
  have hf := hy.start_flags hL
  have he : B.start+11+1=y.s := by omega
  have ht := brkStep hL (r := B.start+11) (by omega) hh.2.2.2 (by simpa only [he] using hf.1)
  have hc := ht.2.1 (by simpa only [he] using hf.2.2)
  rw [he,hh.1,hh.2.1] at hc
  exact ⟨hc.2,by have := hc.1; grind⟩

/-- Empty extracted lists end on their header's offset twelve. -/
theorem ListBlockWf.empty_end {B : ListBlock} (h : ListBlockWf tr tt B) (he : B.receipts=[]) :
    tr.cell tt (B.stop-1) oEnd=12 := by
  have hs : B.stop-1=B.start+11 := by simp [ListBlock.stop,he,segsOf,segEnd]
  rw [hs]
  exact (h.header_end hL).1

end ZkFormal.NearV3.RcptV3Proof
