import ZkFormal.NearV3.Assembly.RcptCandidateRouteRows
import ZkFormal.NearV3.Assembly.RcptCandidateBoundaryTrafficRows
-- Source BoundaryTrafficIndex.lean SHA256: f4400758e8e1c9ff5c2cbf5965e4c6ed4478165b06bfd362dd4063ebdb7e0901.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.BoundaryTrafficRows

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- Actual boundary lookup address is the receipt's boundary pair and its exact
receiver/end-marker byte position. -/
theorem Layout.boundary_index {y : RS} (h : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    (k : Nat) (hk : k≤y.Lv) :
    tr.cell tt (lkRow y k) RcptV3.q=tr.cell tt y.s RcptV3.q ∧
    tr.cell tt (lkRow y k) iB=(k:Fp) := by
  have hq := route_height hL h k hk
  by_cases he : k=y.Lv
  · subst k
    have F := route_end hL h
    have hs : tr.cell tt (lkRow y y.Lv) sRID=1 := by simpa using F.fld.st 0 (by decide)
    have hf : tr.cell tt (lkRow y y.Lv) fs=1 := by simpa using F.fld.fs 0 (by decide)
    have hl : tr.cell tt (lkRow y y.Lv) RcptV3.Lv=(y.Lv:Fp) := by
      have hh := F.consts 0 (by decide) RcptV3.Lv LvC
      simpa only [Nat.add_zero,h.cLv] using hh
    have hc := con hL hq (e:=mul3 (c sRID) (c fs) (sub (c iB) (c RcptV3.Lv))) (mem_ro (by simp [cRoute]))
    simp only [eval_mul3,eval_sub,eval_c,hs,hf,hl] at hc
    refine ⟨?_,by grind⟩
    simpa only [Nat.add_zero] using F.consts 0 (by decide) RcptV3.q (by simp [rconsts])
  · have F := route_receiver hL h
    have hs : tr.cell tt (lkRow y k) sV=1 := by simpa [lkRow] using F.fld.st k (by omega)
    have hi : tr.cell tt (lkRow y k) idx=(k:Fp) := by simpa [lkRow] using F.fld.idx k (by omega)
    have hc := con hL hq (e:=.mul (c sV) (sub (c iB) (c idx))) (mem_ro (by simp [cRoute]))
    simp only [eval_mul,eval_sub,eval_c,hs,hi] at hc
    refine ⟨?_,by grind⟩
    simpa [lkRow] using F.consts k (by omega) RcptV3.q (by simp [rconsts])

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
