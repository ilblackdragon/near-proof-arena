import ZkFormal.NearV3.Assembly.RcptCandidateReceiptArithmetic
import ZkFormal.NearV3.Assembly.RcptCandidateReceiptIds
import ZkFormal.NearV3.Assembly.RcptCandidateReceiptNamed
import ZkFormal.NearV3.Assembly.RcptCandidateReceiptShape
import ZkFormal.NearV3.Assembly.RcptCandidatePrevious
import ZkFormal.NearV3.Assembly.RcptCandidateReceiptAccessFlag
-- Source ReceiptWf.lean SHA256: 685532c5a631f5bfd6603057926098ca11d689d5540c1bd589aba7662eaceaf7.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.ReceiptArithmetic
import ZkFormal.NearV3.Rcpt.Extract.V.ReceiptAccessFlag
import ZkFormal.NearV3.Rcpt.Extract.V.ReceiptIds
import ZkFormal.NearV3.Rcpt.Extract.V.ReceiptNamed
import ZkFormal.NearV3.Rcpt.Extract.V.ReceiptShape

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open ZkFormal.Near.RcptProof (sumL)
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- Assemble all extracted receipt Wf fields. Routing, global receipt numbering,
and the entering token byte invariant remain explicit caller obligations. -/
theorem wf_of_route (hL : TableLocal receiptArithmeticCandidate tr tt pub) {y : RS}
    (lay : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt) {rN : Nat}
    (hrN : tr.cell tt y.s RcptV3.r=(rN:Fp)) (hrP : rN<P)
    (hold : ∀ j,j<16 → cv tr tt (gq y.s y.Lp y.Lv y.Ls y.kt 0) (tok j)<256)
    (hroute : RouteOk (rcptOf tr tt y))
    (hprovider : (rcptOf tr tt y).tprev≤2^22) :
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
    tprev_le := fun _=>previous_of_provider_bound hL lay hrN hrP hprovider
    arith := arith_of hL lay hold
    ee := ee_of hL lay
    neq := neq_of hL lay
    akf := akf_of hL lay
    route := hroute }

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
