import ZkFormal.NearV3.Assembly.RcptDepositAgeCandidate

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/-- Independence from the thirteen candidate age scratch columns. -/
def ageIndependent : Expr→Bool
  | .col col _=>!(decide (xb 53≤col ∧ col<xb 66))
  | .add a b | .mul a b=>ageIndependent a && ageIndependent b
  | .neg a=>ageIndependent a
  | _=>true

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem depositAge_otherFamilies :
    (cEmit++cRegs++cChars++cKey++cSys++cRoute++cGas++cEnd).all ageIndependent=true := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem depositAge_structuralStates :
    (cStates.drop boolCols.length).all ageIndependent=true := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem depositAge_interactions :
    RcptV3.interactions.all (fun it=>it.mult.all ageIndependent && it.msg.all ageIndependent)=true := by decide

/- Besides the replaced age equation, the only overlap is the storage check
on the SECOND DEP row. That gate must be shown zero on the patched first row. -/
set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem depositAge_exact_overlap :
    cDep.filter (fun e=>!(ageIndependent e))=
    [mul3 (Dsl.not (c big)) (c r1) (sub (k 770) (sum [c (dl 0),smul 256 (c st),bitsX 47 10])),
     mul3 dp (c fs) (sub (sub (c r) (c tprev)) (bitsX 57 9))] := by decide

/-- Semantic preservation for every expression outside the scratch ownership
set, including its physical successor accesses and boundary flags. -/
theorem ageIndependent_eval (tr tr' : Trace Fp) (tt pos : Nat) (pub : List Fp)
    (hh : tr.height tt=tr'.height tt)
    (hc : ∀col,¬(xb 53≤col ∧ col<xb 66)→tr.cell tt pos col=tr'.cell tt pos col)
    (hn : ∀col,¬(xb 53≤col ∧ col<xb 66)→
      tr.cell tt ((pos+1)%tr.height tt) col=tr'.cell tt ((pos+1)%tr'.height tt) col)
    (e : Expr) (he : ageIndependent e=true) : e.eval tr tt pos pub=e.eval tr' tt pos pub := by
  induction e with
  | const | pub | isFirst => rfl
  | isLast | isTransition => simp only [Expr.eval,Expr.evalWith,rowEnv,hh]
  | col col nx =>
    have hb : ¬(xb 53≤col ∧ col<xb 66) := by simp [ageIndependent] at he; omega
    cases nx
    · exact hc col hb
    · exact hn col hb
  | add a b ia ib =>
    have hs : ageIndependent a=true ∧ ageIndependent b=true := by simpa only [ageIndependent,Bool.and_eq_true] using he
    simp only [eval_add,ia hs.1,ib hs.2]
  | mul a b ia ib =>
    have hs : ageIndependent a=true ∧ ageIndependent b=true := by simpa only [ageIndependent,Bool.and_eq_true] using he
    simp only [eval_mul,ia hs.1,ib hs.2]
  | neg a ia => simp only [eval_neg,ia he]

end ZkFormal.NearV3.Assembly.RcptSkeleton
