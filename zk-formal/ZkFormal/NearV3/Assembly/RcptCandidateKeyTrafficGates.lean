import ZkFormal.NearV3.Assembly.RcptCandidateKeyTrafficRows
-- Source KeyTrafficGates.lean SHA256: 58e0427d97807d1f6d48fdc11fbdbda86edaa073cc6add2c64eb8f6ce544ae64.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.KeyTrafficRows

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def stateBit (X Y : Nat) : Fp := if Y=X then 1 else 0

def keyAState (X : Nat) (f z e : Fp) : Fp :=
  stateBit X sV+z+stateBit X sRID*f+e*(stateBit X sT0+stateBit X sSL*f+
    stateBit X sS+stateBit X sKT+stateBit X sPK+stateBit X sGP*f)
def keyBState (X : Nat) (f e : Fp) : Fp :=
  stateBit X sV+e*(stateBit X sT0+stateBit X sSL*f+stateBit X sS+stateBit X sKT+stateBit X sPK)
def keyWalkState (X : Nat) (r : Fp) : Fp :=
  r+(W_AK:Nat)*(stateBit X sT0+stateBit X sSL+stateBit X sS+stateBit X sKT+stateBit X sPK+stateBit X sGP)

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- One-hot states expose all key slot gates and the actual account/access walk ID. -/
theorem key_state_gates {q X : Nat} (hq : q<tr.height tt) (hx : X∈states) (hs : tr.cell tt q X=1) :
    tr.cell tt q gKA=keyAState X (tr.cell tt q fs) (tr.cell tt q kz) (tr.cell tt q ee) ∧
    tr.cell tt q gKB=keyBState X (tr.cell tt q fs) (tr.cell tt q ee) ∧
    wE.eval tr tt q pub=keyWalkState X (tr.cell tt q RcptV3.r) := by
  have ho : ∀ Y∈states,tr.cell tt q Y=stateBit X Y := by
    intro Y hY
    unfold stateBit
    by_cases he : Y=X
    · subst Y; simp only [ite_true]; exact hs
    · rw [if_neg he]; exact (oneHot hL hq hx hs).2 Y hY he
  have ha := (key_row hL hq).1
  have hb := keyB_gate hL hq
  simp only [ho sV (by simp [states]),ho sRID (by simp [states]),ho sT0 (by simp [states]),
    ho sSL (by simp [states]),ho sS (by simp [states]),ho sKT (by simp [states]),
    ho sPK (by simp [states]),ho sGP (by simp [states])] at ha hb
  refine ⟨?_,hb,?_⟩
  · unfold keyAState; grind
  · simp only [wE,akRow,eval_add,eval_smul,eval_sum_cons,eval_sum_nil,eval_c,
      ho sT0 (by simp [states]),ho sSL (by simp [states]),ho sS (by simp [states]),
      ho sKT (by simp [states]),ho sPK (by simp [states]),ho sGP (by simp [states]),keyWalkState]
    grind

omit hL in
/-- State-only gate formulas used for concrete field cases. -/
theorem account_key_gates (f z e r : Fp) :
    (keyAState sVL f z e=z ∧ keyBState sVL f e=0 ∧ keyWalkState sVL r=r) ∧
    (keyAState sV f 0 e=1 ∧ keyBState sV f e=1 ∧ keyWalkState sV r=r) ∧
    (keyAState sRID f 0 e=f ∧ keyBState sRID f e=0 ∧ keyWalkState sRID r=r) := by
  simp only [keyAState,keyBState,keyWalkState,stateBit,sVL,sV,sRID,sT0,sSL,sS,sKT,sPK,sGP]
  simp only [ite_true,ite_false]
  constructor <;> (first | constructor | skip) <;> grind

omit hL in
/-- Access-key states have the offset walk ID and exactly their actual slot gates. -/
theorem access_key_gates (f e r : Fp) :
    (∀ X∈[sT0,sS,sKT,sPK],keyAState X f 0 e=e ∧ keyBState X f e=e ∧ keyWalkState X r=r+(W_AK:Nat)) ∧
    (keyAState sSL f 0 e=e*f ∧ keyBState sSL f e=e*f ∧ keyWalkState sSL r=r+(W_AK:Nat)) ∧
    (keyAState sGP f 0 e=e*f ∧ keyBState sGP f e=0 ∧ keyWalkState sGP r=r+(W_AK:Nat)) := by
  constructor
  · intro X hX
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hX
    rcases hX with rfl|rfl|rfl|rfl <;>
      simp only [keyAState,keyBState,keyWalkState,stateBit,sVL,sV,sRID,sT0,sSL,sS,sKT,sPK,sGP,ite_true,ite_false] <;> grind
  · simp only [keyAState,keyBState,keyWalkState,stateBit,sVL,sV,sRID,sT0,sSL,sS,sKT,sPK,sGP,ite_true,ite_false]
    grind

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
