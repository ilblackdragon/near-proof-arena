import ZkFormal.NearV3.Rcpt.Extract.V.ReceiptArithmetic
import ZkFormal.NearV3.Rcpt.Extract.V.ReceiptAccessFlag
import ZkFormal.NearV3.Rcpt.Extract.V.ReceiptIds
import ZkFormal.NearV3.Rcpt.Extract.V.ReceiptNamed
import ZkFormal.NearV3.Rcpt.Extract.V.ReceiptShape

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open ZkFormal.Near.RcptProof (sumL)
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- Assemble all extracted receipt Wf fields. Routing, global receipt numbering,
and the entering token byte invariant remain explicit caller obligations. -/
theorem wf_of_route (hL : TableLocal RcptV3.table tr tt pub) {y : RS}
    (lay : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt) {rN : Nat}
    (hrN : tr.cell tt y.s RcptV3.r=(rN:Fp)) (hrP : rN<P)
    (hold : ∀ j,j<16 → cv tr tt (gq y.s y.Lp y.Lv y.Ls y.kt 0) (tok j)<256)
    (hroute : RouteOk (rcptOf tr tt y)) :
    (rcptOf tr tt y).Wf rN (pubBytes pub PH_GP 16)
      (sumL (fun j => cv tr tt (gq y.s y.Lp y.Lv y.Ls y.kt 0) (tok j)) 16)
      (sumL (fun k => bvN tr tt (gq y.s y.Lp y.Lv y.Ls y.kt k) 31 8) 16) := by
  exact {
    lens := lens_of tr tt y lay.kt1
    ids := ids_of hL lay
    sysIff := system_of hL lay
    named := named_of hL lay
    aft8 := aft8_of hL lay
    small := small_of tr tt y
    tprev_le := tprev_le_of hL lay hrN hrP
    arith := arith_of hL lay hold
    ee := ee_of hL lay
    neq := neq_of hL lay
    akf := akf_of hL lay
    route := hroute }

end ZkFormal.NearV3.RcptV3Proof
