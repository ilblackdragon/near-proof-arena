import ZkFormal.NearV3.Rcpt.Extract.V.ReceiptWf
import ZkFormal.NearV3.Rcpt.Extract.V.RouteSemantic

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open ZkFormal.Near.RcptProof (sumL)

/-- All per-receipt semantic fields follow from the active V3 table and layout.
Only global receipt numbering and the entering token-byte invariant remain to
be supplied by whole-table reconstruction. -/
theorem wf_of {tr : Trace Fp} {pub : List Fp} {tt : Nat}
    (hL : TableLocal RcptV3.table tr tt pub) {y : RS}
    (lay : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt) {rN : Nat}
    (hrN : tr.cell tt y.s RcptV3.r=(rN:Fp)) (hrP : rN<P)
    (hold : ∀ j,j<16 → cv tr tt (gq y.s y.Lp y.Lv y.Ls y.kt 0) (tok j)<256) :
    (rcptOf tr tt y).Wf rN (pubBytes pub PH_GP 16)
      (sumL (fun j => cv tr tt (gq y.s y.Lp y.Lv y.Ls y.kt 0) (tok j)) 16)
      (sumL (fun k => bvN tr tt (gq y.s y.Lp y.Lv y.Ls y.kt k) 31 8) 16) :=
  wf_of_route hL lay hrN hrP hold (route_of hL lay)

end ZkFormal.NearV3.RcptV3Proof
