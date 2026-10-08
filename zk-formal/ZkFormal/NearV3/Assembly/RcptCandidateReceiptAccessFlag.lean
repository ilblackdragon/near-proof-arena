import ZkFormal.NearV3.Assembly.RcptCandidateReceiptUnequal
-- Source ReceiptAccessFlag.lean SHA256: cafb97962b4d2500b7aed1c03f669035880d5929460e73a5ba3a60f4475de9e1.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.ReceiptUnequal

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/-- The access-key flag at the reconstructed T0 row is a canonical boolean. -/
theorem akf_of {tr : Trace Fp} {pub : List Fp} {tt : Nat}
    (hL : TableLocal receiptArithmeticCandidate tr tt pub) {y : RS}
    (lay : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt) : (rcptOf tr tt y).akf≤1 := by
  have hm : (sT0,40+y.Lp+y.Lv,1)∈plan y.h y.Lp y.Lv y.Ls y.kt := by simp [plan]
  have hl := plan_le y.h y.Lp y.Lv y.Ls y.kt _ hm
  have hf := lay.fin
  simp only at hl
  exact cv_bool (isBool hL (by omega) (by simp [boolCols]))

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
