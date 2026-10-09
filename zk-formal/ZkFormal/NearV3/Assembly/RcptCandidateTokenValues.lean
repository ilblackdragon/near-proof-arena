import ZkFormal.NearV3.Assembly.RcptCandidateHeaderTokens
-- Source TokenValues.lean SHA256: 01a2c7189365363693dccfa334f76de8e1cb740aca3b28df3c0a61bd001204f4.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.HeaderTokens

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open ZkFormal.Near.RcptProof (sumL sumL_congr)

def tokenAt (tr : Trace Fp) (tt q : Nat) : Nat := sumL (fun j => cv tr tt q (tok j)) 16
def tokenIn (tr : Trace Fp) (tt : Nat) (y : RS) : Nat := tokenAt tr tt (gq y.s y.Lp y.Lv y.Ls y.kt 0)
def tokenOut (tr : Trace Fp) (tt : Nat) (y : RS) : Nat := sumL (fun j => bvN tr tt (gq y.s y.Lp y.Lv y.Ls y.kt j) 31 8) 16

/-- Token values agree whenever all sixteen register bytes agree. -/
theorem tokenAt_eq {tr : Trace Fp} {tt a b : Nat}
    (h : ∀ j,j<16 → tr.cell tt a (tok j)=tr.cell tt b (tok j)) : tokenAt tr tt a=tokenAt tr tt b := by
  apply sumL_congr
  intro j hj
  simp [cv,h j hj]

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

theorem tokenAt_zero (h0 : 0<tr.height tt) : tokenAt tr tt 0=0 := by
  apply (sumL_zero_iff _ 16).mpr
  intro j hj
  simp [cv,token_zero hL h0 j hj,Fp.toNat_zero]

/-- A row containing the generated GP bytes has exactly the receipt's output token value. -/
theorem tokenAt_output {y : RS} (lay : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt) (q : Nat)
    (he : ∀ j,j<16 → tr.cell tt q (tok j)=((bvN tr tt (gq y.s y.Lp y.Lv y.Ls y.kt j) 31 8:Nat):Fp)) :
    tokenAt tr tt q=tokenOut tr tt y := by
  apply sumL_congr
  intro j hj
  have hb := (bitsX_eval hL (gp_row hL lay j hj).1 31 8 (by omega)).2
  change bvN tr tt (gq y.s y.Lp y.Lv y.Ls y.kt j) 31 8<256 at hb
  rw [cv,he j hj,toNat_natCast,Nat.mod_eq_of_lt (by unfold P; omega)]

theorem tokenIn_start {y : RS} (lay : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt) :
    tokenIn tr tt y=tokenAt tr tt y.s := tokenAt_eq (token_receipt_start hL lay)

theorem tokenOut_last {y : RS} (lay : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt) :
    tokenOut tr tt y=tokenAt tr tt (y.s+y.tot-1) :=
  (tokenAt_output hL lay _ (token_receipt_last hL lay)).symm

theorem tokenIn_next {y z : RS}
    (hy : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    (hz : Layout tr tt z.s z.h z.Lp z.Lv z.Ls z.kt) (hs : z.s=y.s+y.tot) :
    tokenIn tr tt z=tokenOut tr tt y := tokenAt_output hL hy _ (token_next_receipt hL hy hz hs)

/-- Field-level token carry across a block's physical terminal row. -/
theorem ListBlockWf.next_tokens {B : ListBlock} (h : ListBlockWf tr tt B)
    (ha : tr.cell tt B.stop act=1) : tokenAt tr tt B.stop=tokenAt tr tt (B.stop-1) := by
  have hb := h.bound
  have hs : 0<B.stop := by omega
  have hn : B.stop-1+1=B.stop := by omega
  have hact : tr.cell tt (B.stop-1) act=1 := ListBlockWf.active hL h (by omega) (by omega)
  have hgp : tr.cell tt (B.stop-1) sGP=0 := by
    cases he : B.receipts with
    | nil =>
      have hstop : B.stop=B.start+12 := by simp [ListBlock.stop,he,segsOf,segEnd]
      have hq : B.stop-1=B.start+11 := by omega
      have hh := h.header.st 11 (by omega)
      rw [←hq] at hh
      exact (oneHot hL (by omega) (by simp [states]) hh).2 sGP (by simp [states]) (by decide)
    | cons y ys =>
      have hne : B.receipts≠[] := by simp [he]
      obtain ⟨z,hz,hend⟩ := receipt_sequence_last B.receipts (B.start+12) hne
      have hy := h.layouts z hz
      have hs' : B.stop=z.s+z.tot := hend
      have hp : 94+Vt z.Lp z.Lv z.Ls z.kt<z.tot := by unfold RS.tot total; split <;> omega
      have hm : (sGP,78+Vt z.Lp z.Lv z.Ls z.kt,16)∈plan z.h z.Lp z.Lv z.Ls z.kt := by simp [plan]
      have hh := cell_state hL hy hm (z.tot-1) (by unfold RS.tot at *; omega)
      rw [if_neg (by omega)] at hh
      simpa only [hs',show z.s+z.tot-1=z.s+(z.tot-1) by omega] using hh
  apply tokenAt_eq
  intro j hj
  have hh := token_keep_active hL (q:=B.stop-1) (by omega) hact (by rwa [hn]) hgp j hj
  rwa [hn] at hh

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
