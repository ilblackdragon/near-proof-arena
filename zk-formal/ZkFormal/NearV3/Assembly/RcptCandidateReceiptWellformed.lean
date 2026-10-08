import ZkFormal.NearV3.Assembly.RcptCandidateReceiptWf
import ZkFormal.NearV3.Assembly.RcptCandidateRouteSemantic
-- Source ReceiptWellformed.lean SHA256: c40b14e8806ce887d60b282e1c7a0bb521fa63c22fa93ce258064509d210a4ac.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.ReceiptWf
import ZkFormal.NearV3.Rcpt.Extract.V.RouteSemantic

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open ZkFormal.Near.RcptProof (sumL)

/-- All per-receipt semantic fields follow from the active V3 table and layout.
Global receipt numbering, the previous-version provider bound, and the entering token-byte invariant remain to
be supplied by whole-table reconstruction. -/
theorem wf_of {tr : Trace Fp} {pub : List Fp} {tt : Nat}
    (hL : TableLocal receiptArithmeticCandidate tr tt pub) {y : RS}
    (lay : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt) {rN : Nat}
    (hrN : tr.cell tt y.s RcptV3.r=(rN:Fp)) (hrP : rN<P)
    (hold : ∀ j,j<16 → cv tr tt (gq y.s y.Lp y.Lv y.Ls y.kt 0) (tok j)<256)
    (hprovider : (rcptOf tr tt y).tprev≤2^22) :
    (rcptOf tr tt y).Wf rN (pubBytes pub PH_GP 16)
      (sumL (fun j => cv tr tt (gq y.s y.Lp y.Lv y.Ls y.kt 0) (tok j)) 16)
      (sumL (fun k => bvN tr tt (gq y.s y.Lp y.Lv y.Ls y.kt k) 31 8) 16) :=
  wf_of_route hL lay hrN hrP hold (route_of hL lay) hprovider

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
