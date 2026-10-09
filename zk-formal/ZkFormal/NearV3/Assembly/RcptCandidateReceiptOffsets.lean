import ZkFormal.NearV3.Assembly.RcptCandidateListLengths
-- Source ReceiptOffsets.lean SHA256: ffe830dcc28970213ba0d18701d9fd1d5e462d23cad891a574dbe7a3c18bff30.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.ListLengths

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)

/-- The first physical field of an extracted receipt is its predecessor-length field. -/
theorem Layout.start_field {y : RS} (h : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt) :
    Fld tr tt y.s 4 sPL := by
  have hf := (h.flds (sPL,0,4) (by simp [plan])).fld
  simpa using hf

include hL

theorem Layout.start_flags {y : RS} (h : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt) :
    tr.cell tt y.s act=1 ∧ tr.cell tt y.s sCL=0 ∧ tr.cell tt y.s rf=1 := by
  have hf := h.start_field
  have hs : tr.cell tt y.s sPL=1 := by simpa using hf.st 0 (by decide)
  have hfs : tr.cell tt y.s fs=1 := by simpa using hf.fs 0 (by decide)
  have hfin := h.fin
  have ho := oneHot hL (r := y.s) (by omega) (by simp [states]) hs
  have hb := bounds hL (r := y.s) (by omega)
  refine ⟨ho.1,ho.2 sCL (by simp [states]) (by decide),?_⟩
  exact hb.2.2.1 hs hfs

/-- The emitted end offset is the previous offset plus the exact extracted encoding length. -/
theorem Layout.encoded_end {y : RS} (h : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt) :
    tr.cell tt y.s oEnd=tr.cell tt y.s o+((rcptOf tr tt y).enc.length : Fp) := by
  have hf := Layout.start_flags hL h
  have hfin := h.fin
  have hh := (sizes hL (r := y.s) (by omega) hf.1 hf.2.1).1
  rw [h.cLp,h.cLv,h.cLs,h.ckt] at hh
  rw [rcptOf_enc_length]
  simp only [Vt,natCast_add,natCast_mul]
  rw [hh]
  grind

theorem Layout.last_encoded_end {y : RS} (h : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt) :
    tr.cell tt (y.s+y.tot-1) oEnd=tr.cell tt y.s o+((rcptOf tr tt y).enc.length : Fp) := by
  have hh := (lay_last hL h).2 oEnd oEndC
  exact hh.trans (Layout.encoded_end hL h)

/-- Adjacent receipt layouts chain the encoded offsets across their physical boundary. -/
theorem Layout.next_offset {y z : RS}
    (hy : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    (hz : Layout tr tt z.s z.h z.Lp z.Lv z.Ls z.kt)
    (hnext : z.s=y.s+y.tot) :
    tr.cell tt z.s o=tr.cell tt y.s o+((rcptOf tr tt y).enc.length : Fp) := by
  have hp := total_pos y.h y.Lp y.Lv y.Ls y.kt
  have hf := Layout.start_flags hL hz
  have hfin := hy.fin
  have hrl := hy.endRl
  have hnc := lay_last_ncl hL hy
  have hstep := brkStep hL (r := y.s+y.tot-1) (by unfold RS.tot; omega)
    (by unfold RS.tot; rw [hrl,hnc]; grind)
    (by simpa only [show y.s+y.tot-1+1=z.s by unfold RS.tot at *; omega] using hf.1)
  have ho := (hstep.2.1 (by simpa only [show y.s+y.tot-1+1=z.s by unfold RS.tot at *; omega] using hf.2.2)).2
  rw [show y.s+y.tot-1+1=z.s by unfold RS.tot at *; omega] at ho
  exact ho.trans (Layout.last_encoded_end hL hy)

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
