import ZkFormal.NearV3.Assembly.RcptCandidateKey
-- Source KeyTrafficRows.lean SHA256: c0c1dd6abeee092cf25824e2f7d75459867c224491a01c36566136744c9e6211.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.PlanTraffic
import ZkFormal.NearV3.Rcpt.Extract.V.Key

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def keyStates : List Nat := [sVL,sV,sRID,sT0,sSL,sS,sKT,sPK,sGP]

theorem keyStates_sub : ∀ x∈keyStates,x∈states := by decide

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- Exact second key-symbol gate, including all access-key byte fields. -/
theorem keyB_gate {q : Nat} (hq : q<tr.height tt) :
    tr.cell tt q gKB=tr.cell tt q sV+tr.cell tt q ee*
      (tr.cell tt q sT0+tr.cell tt q sSL*tr.cell tt q fs+tr.cell tt q sS+
        tr.cell tt q sKT+tr.cell tt q sPK) := by
  have hh := con hL hq (e:=sub (c gKB) (.add (c sV) (.mul (c ee)
    (sum [c sT0,.mul (c sSL) (c fs),c sS,c sKT,c sPK])))) (mem_ky (by simp [cKey]))
  simp only [eval_sub,eval_add,eval_mul,eval_c,eval_sum_cons,eval_sum_nil] at hh
  grind

/-- No key symbols can be emitted when all relevant actual states are absent. -/
theorem key_silent {q : Nat} (hq : q<tr.height tt)
    (hz : ∀ x∈keyStates,tr.cell tt q x=0) :
    rowTraffic RcptV3.interactions tr tt q pub B_KEYNIB true=[] := by
  have ha := (key_row hL hq).1
  have hb := keyB_gate hL hq
  have hk := kz_zero hL hq (hz sVL (by simp [keyStates]))
  simp only [hz sV (by simp [keyStates]),hz sRID (by simp [keyStates]),hz sT0 (by simp [keyStates]),
    hz sSL (by simp [keyStates]),hz sS (by simp [keyStates]),hz sKT (by simp [keyStates]),
    hz sPK (by simp [keyStates]),hz sGP (by simp [keyStates]),hk] at ha hb
  have ga : tr.cell tt q gKA=0 := by grind
  have gb : tr.cell tt q gKB=0 := by grind
  rw [rowT_key]
  simp only [C]
  rw [gt_zero ga,gt_zero gb,List.nil_append]

/-- One-hot receipt states outside key fields are silent. -/
theorem key_state_silent {q X : Nat} (hq : q<tr.height tt) (hx : X∈states)
    (hs : tr.cell tt q X=1) (hn : X∉keyStates) :
    rowTraffic RcptV3.interactions tr tt q pub B_KEYNIB true=[] := by
  apply key_silent hL hq
  intro Y hY
  exact (oneHot hL hq hx hs).2 Y (keyStates_sub Y hY) (by intro he; exact hn (he ▸ hY))

theorem ListBlockWf.header_key {B : ListBlock} (h : ListBlockWf tr tt B) :
    (List.range' B.start 12).flatMap
      (fun q => rowTraffic RcptV3.interactions tr tt q pub B_KEYNIB true)=[] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro q hq
  obtain ⟨k,hk,hq⟩ := List.mem_range'.mp hq
  simp only [Nat.one_mul] at hq
  subst q
  have hfin := h.header_fin
  exact key_state_silent hL (by omega) (by simp [states]) (h.header.st k hk) (by decide)

theorem inactive_key {q : Nat} (hq : q<tr.height tt) (ha : tr.cell tt q act=0) :
    rowTraffic RcptV3.interactions tr tt q pub B_KEYNIB true=[] :=
  key_silent hL hq (fun x hx => noState hL hq ha x (keyStates_sub x hx))

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
