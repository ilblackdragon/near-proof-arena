import ZkFormal.NearV3.Rcpt.Extract.V.ReceiptUnequal

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/-- The access-key flag at the reconstructed T0 row is a canonical boolean. -/
theorem akf_of {tr : Trace Fp} {pub : List Fp} {tt : Nat}
    (hL : TableLocal RcptV3.table tr tt pub) {y : RS}
    (lay : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt) : (rcptOf tr tt y).akf≤1 := by
  have hm : (sT0,40+y.Lp+y.Lv,1)∈plan y.h y.Lp y.Lv y.Ls y.kt := by simp [plan]
  have hl := plan_le y.h y.Lp y.Lv y.Ls y.kt _ hm
  have hf := lay.fin
  simp only at hl
  exact cv_bool (isBool hL (by omega) (by simp [boolCols]))

end ZkFormal.NearV3.RcptV3Proof
