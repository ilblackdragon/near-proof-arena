import ZkFormal.NearV3.Assembly.RcptCandidateNamed
-- Source ReceiptNamed.lean SHA256: ab1b17d56b59147a978d76dd89a59a9d2ec145f2eae15f2d3fcd74fcc668fc75.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.Named

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 NearSpec
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- The concrete V3 receipt receiver satisfies the native named-account rule. -/
theorem named_of (hL : TableLocal receiptArithmeticCandidate tr tt pub) {y : RS}
    (lay : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt) :
    AccountId.isNamed (toBytes (rcptOf tr tt y).v) = true := by
  have mV : (sV,8+y.Lp,y.Lv)∈plan y.h y.Lp y.Lv y.Ls y.kt := by simp [plan]
  have hl := plan_le y.h y.Lp y.Lv y.Ls y.kt _ mV
  have hf := lay.fin
  simp only at hl
  have F : RFld tr tt y.s (y.s+(8+y.Lp)) y.Lv sV := lay.flds _ mV
  have hc : ∀ k, k<y.Lv → tr.cell tt (y.s+(8+y.Lp)+k) RcptV3.Lv = ((y.Lv : Nat) : Fp) := by
    intro k hk
    rw [F.consts k hk _ LvC,lay.cLv]
  have hn := str_len hL F (by omega) hc (mem_ch (by simp [cChars])) (mem_ch (by simp [cChars]))
  exact named_ok hL F (by omega) hc hn

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
