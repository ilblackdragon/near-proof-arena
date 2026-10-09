import ZkFormal.NearV3.Assembly.RcptCandidateLayout
import ZkFormal.NearV3.Rcpt.Extract.V.ListInterior
namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open RcptV3Proof RcptSkeleton
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL
theorem layout_row_flags {y : RS} (h : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    (k : Nat) (hk : k<y.tot) :
    tr.cell tt (y.s+k) act=1 ∧ tr.cell tt (y.s+k) sCL=0 := by
  obtain ⟨f,hf,hlo,hhi⟩ := plan_cover y.h y.Lp y.Lv y.Ls y.kt k hk
  have hs := (h.flds f hf).fld.st (k-f.2.1) (by omega)
  rw [show y.s+f.2.1+(k-f.2.1)=y.s+k by omega] at hs
  have hfin := h.fin
  have hp := plan_states y.h y.Lp y.Lv y.Ls y.kt f hf
  have hh := oneHot hL (r := y.s+k) (by unfold RS.tot at hk; omega) hp.1 hs
  exact ⟨hh.1,hh.2 sCL (by simp [states]) hp.2.symm⟩

theorem layout_start_flags {y : RS} (h : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt) :
    tr.cell tt y.s act=1 ∧ tr.cell tt y.s sCL=0 ∧ tr.cell tt y.s rf=1 := by
  have hf := h.start_field
  have hs : tr.cell tt y.s sPL=1 := by simpa using hf.st 0 (by decide)
  have hfs : tr.cell tt y.s fs=1 := by simpa using hf.fs 0 (by decide)
  have hfin := h.fin
  have ho := oneHot hL (r := y.s) (by omega) (by simp [states]) hs
  have hb := bounds hL (r := y.s) (by omega)
  refine ⟨ho.1,ho.2 sCL (by simp [states]) (by decide),?_⟩
  exact hb.2.2.1 hs hfs

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
