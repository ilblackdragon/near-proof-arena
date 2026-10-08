import ZkFormal.NearV3.Assembly.RcptCandidateSignerTraffic
-- Source BoundaryTrafficRows.lean SHA256: e213f2b75a3f4e07fadce1368658816b7f865cbf2aa72c8027faa1912a5f6cf7.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.SignerTraffic

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem rowT_bnd (q : Nat) (sd : Bool) :
    rowTraffic RcptV3.interactions tr tt q pub B_BND sd=
      gt (tr.cell tt q gBd) [(BND_STRIDE:Nat)*tr.cell tt q RcptV3.q+tr.cell tt q iB,
        tr.cell tt q loB,tr.cell tt q hiB,tr.cell tt q hnB,tr.cell tt q uB+(if sd then 1 else 0)] := by
  rw [rowT]
  cases sd <;> simp [B_BYTES,B_DIGEST,B_KEYNIB,B_FINAL,B_MEM,B_RIDS,B_MPOS,B_RCL,B_SREC,B_AKC,B_BND,C] <;>
    congr 6 <;> grind

variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- Disabled routing rows cannot inject boundary-counter messages. -/
theorem bnd_silent {q : Nat} (hq : q<tr.height tt) (hr : rwE.eval tr tt q pub=0) (sd : Bool) :
    rowTraffic RcptV3.interactions tr tt q pub B_BND sd=[] := by
  have hh := con hL hq (e:=sub (c gBd) (.mul rwE (orE (c eqL) (c eqH)))) (mem_ro (by simp [cRoute]))
  simp only [eval_sub,eval_c,eval_mul,hr] at hh
  have hz : tr.cell tt q gBd=0 := by grind
  rw [rowT_bnd]
  exact gt_zero hz _

theorem ListBlockWf.header_bnd {B : ListBlock} (h : ListBlockWf tr tt B) (sd : Bool) :
    (List.range' B.start 12).flatMap
      (fun q => rowTraffic RcptV3.interactions tr tt q pub B_BND sd)=[] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro q hq
  obtain ⟨k,hk,hq⟩ := List.mem_range'.mp hq
  simp only [Nat.one_mul] at hq
  subst q
  have hs := h.header.st k hk
  have hfin := h.header_fin
  have ho := (oneHot hL (r:=B.start+k) (by omega) (by simp [states]) hs).2
  apply bnd_silent hL (by omega) _ sd
  simp only [rwE,eval_add,eval_mul,eval_c,ho sV (by simp [states]) (by decide),
    ho sRID (by simp [states]) (by decide)]
  grind

/-- Routing enable is zero outside receiver bytes plus their end marker. -/
theorem Layout.route_disabled {y : RS} (h : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    (j : Nat) (hj : j<y.tot) (hout : j<8+y.Lp ∨ 8+y.Lp+(y.Lv+1)≤j) :
    rwE.eval tr tt (y.s+j) pub=0 := by
  have mv : (sV,8+y.Lp,y.Lv)∈plan y.h y.Lp y.Lv y.Ls y.kt := by simp [plan]
  have mr : (sRID,8+y.Lp+y.Lv,32)∈plan y.h y.Lp y.Lv y.Ls y.kt := by simp [plan]
  have hv := st_row hL h mv j hj (by omega)
  simp only [rwE,eval_add,eval_mul,eval_c,hv]
  by_cases hr : 8+y.Lp+y.Lv≤j ∧ j<8+y.Lp+y.Lv+32
  · have F := (h.flds _ mr).fld
    have hf := F.fs (j-(8+y.Lp+y.Lv)) (by change j-(8+y.Lp+y.Lv)<32; omega)
    have he : y.s+(8+y.Lp+y.Lv)+(j-(8+y.Lp+y.Lv))=y.s+j := by omega
    simp only at hf
    rw [he,if_neg (by omega)] at hf
    rw [hf]
    grind
  · have hh := st_row hL h mr j hj (by omega)
    rw [hh]
    grind

/-- Boundary traffic is confined to the receiver and its first receipt-ID row. -/
theorem Layout.bnd_window {y : RS} (h : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt) (sd : Bool) :
    (List.range' y.s y.tot).flatMap (fun q => rowTraffic RcptV3.interactions tr tt q pub B_BND sd)=
      (List.range' (y.s+(8+y.Lp)) (y.Lv+1)).flatMap
        (fun q => rowTraffic RcptV3.interactions tr tt q pub B_BND sd) := by
  have hm : (sRID,8+y.Lp+y.Lv,32)∈plan y.h y.Lp y.Lv y.Ls y.kt := by simp [plan]
  have hl := plan_le y.h y.Lp y.Lv y.Ls y.kt _ hm
  have hf := h.fin
  simp only at hl
  apply flatMap_window _ y.s y.tot (8+y.Lp) (y.Lv+1) (by unfold RS.tot; omega)
  intro j hj hout
  exact bnd_silent hL (by unfold RS.tot at hj; omega) (Layout.route_disabled hL h j hj hout) sd

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
