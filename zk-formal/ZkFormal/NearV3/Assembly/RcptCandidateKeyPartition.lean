import ZkFormal.NearV3.Assembly.RcptCandidateKeyCanonical
-- Source KeyPartition.lean SHA256: 9b6a7ddb30911cd92a3e402dca4c68b6a3becfcded347db23bdb01eecf0f1356.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.KeyCanonical

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def keyFieldTraffic (tr : Trace Fp) (tt : Nat) (pub : List Fp) (s off len : Nat) : List (List Fp) :=
  (List.range' (s+off) len).flatMap (fun q => rowTraffic RcptV3.interactions tr tt q pub B_KEYNIB true)

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- Non-key fields contribute no symbols anywhere in their complete physical span. -/
theorem Layout.key_other_field {y : RS} (lay : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    {X off len : Nat} (hm : (X,off,len)∈plan y.h y.Lp y.Lv y.Ls y.kt) (hx : X∉keyStates) :
    keyFieldTraffic tr tt pub y.s off len=[] := by
  have F : RFld tr tt y.s (y.s+off) len X := lay.flds _ hm
  have hfin := lay.fin
  have hle := plan_le y.h y.Lp y.Lv y.Ls y.kt _ hm
  simp only at hle
  apply List.flatMap_eq_nil_iff.mpr
  intro q hq
  obtain ⟨k,hk,hq⟩ := List.mem_range'.mp hq
  simp only [Nat.one_mul] at hq
  subst q
  exact key_state_silent hL (by omega) (plan_states _ _ _ _ _ _ hm).1 (F.fld.st k hk) hx

/-- Exact physical KEYNIB partition: every receipt row occurs once; only nine
key fields survive, in serialization order. -/
theorem Layout.key_partition {y : RS} (lay : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt) :
    (List.range' y.s y.tot).flatMap (fun q => rowTraffic RcptV3.interactions tr tt q pub B_KEYNIB true)=
      keyFieldTraffic tr tt pub y.s (4+y.Lp) 4++
      keyFieldTraffic tr tt pub y.s (8+y.Lp) y.Lv++
      keyFieldTraffic tr tt pub y.s (8+y.Lp+y.Lv) 32++
      keyFieldTraffic tr tt pub y.s (40+y.Lp+y.Lv) 1++
      keyFieldTraffic tr tt pub y.s (41+y.Lp+y.Lv) 4++
      keyFieldTraffic tr tt pub y.s (45+y.Lp+y.Lv) y.Ls++
      keyFieldTraffic tr tt pub y.s (45+y.Lp+y.Lv+y.Ls) 1++
      keyFieldTraffic tr tt pub y.s (46+y.Lp+y.Lv+y.Ls) (32+32*y.kt)++
      keyFieldTraffic tr tt pub y.s (78+Vt y.Lp y.Lv y.Ls y.kt) 16 := by
  rw [plan_traffic]
  change (plan y.h y.Lp y.Lv y.Ls y.kt).flatMap (fun fld => keyFieldTraffic tr tt pub y.s fld.2.1 fld.2.2)=_
  have hf : (plan y.h y.Lp y.Lv y.Ls y.kt).flatMap (fun fld => keyFieldTraffic tr tt pub y.s fld.2.1 fld.2.2)=
      (plan y.h y.Lp y.Lv y.Ls y.kt).flatMap (fun fld =>
        if fld.1∈keyStates then keyFieldTraffic tr tt pub y.s fld.2.1 fld.2.2 else []) := by
    apply flatMap_congr'
    intro fld hm
    by_cases hx : fld.1∈keyStates
    · rw [if_pos hx]
    · rw [if_neg hx]
      exact Layout.key_other_field hL lay hm hx
  rw [hf]
  cases hy : y.h <;>
    simp [plan,hy,keyStates,sPL,sP,sVL,sV,sRID,sT0,sSL,sS,sKT,sPK,sGP,sTL,sDEP,sXP0,
      sXRI,sXG,sXST,sXL0,sXLH,sXRH,sXRF,sXRZ,List.append_assoc]

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
