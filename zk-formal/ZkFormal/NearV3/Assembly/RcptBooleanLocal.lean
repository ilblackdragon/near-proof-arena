import ZkFormal.NearV3.Assembly.RcptBooleanTrace

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def booleanConstraints : List Expr := boolCols.map (fun x=>bool (c x))

set_option maxRecDepth 4096 in
theorem booleanConstraints_count : booleanConstraints.length=119 := by decide
set_option maxRecDepth 4096 in
theorem booleanConstraints_in_states : ∀e∈booleanConstraints,e∈cStates := by
  intro e he
  unfold cStates
  simp only [List.mem_append]
  simp_all [booleanConstraints]

theorem bool_eval_zero (tr : Trace Fp) (pos col : Nat) (pub : List Fp)
    (h : BooleanValue (tr.cell 0 pos col)) : (bool (c col)).eval tr 0 pos pub=0 := by
  simp only [Dsl.bool,Dsl.c,Dsl.sub,Dsl.k,Expr.eval,Expr.evalWith,rowEnv,Bool.false_eq_true,ite_false]
  rcases h with h|h <;> rw [h] <;> grind only

theorem booleanReceiptTrace_cBool (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log pos : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp) :
    ∀e∈booleanConstraints,
      e.eval (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0 pos pub=0 := by
  intro e he
  obtain ⟨col,hc,rfl⟩ := List.mem_map.mp he
  have hb := booleanReceiptTrace_cells own ctx lists hw log pos constants pub digests fallback headerFallback col hc
  exact bool_eval_zero _ pos col pub hb

/-- All200 register,189 emission and119 Boolean constraints on one physical trace.
Remaining structural state and semantic groups are not asserted here. -/
theorem booleanReceiptTrace_regs_emit_bool (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hcap : (plannedRows lists).length≤2^log)
    (hown : ∀j,j<8→pub.getD (PH_OWN+j) 0=Fp.ofNat (((u64 own).getD j 0).toNat)) :
    ∀pos,pos<2^log→∀e∈cRegs++cEmit++booleanConstraints,
      e.eval (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0 pos pub=0 := by
  intro pos hp e he
  rcases List.mem_append.mp he with he|he
  · exact emittedReceiptTrace_regs_emit own ctx lists hw log (booleanConstants constants) pub digests
      (booleanReceiptAux fallback) (booleanHeaderAux headerFallback) hcap hown pos hp e he
  · exact booleanReceiptTrace_cBool own ctx lists hw log pos constants pub digests fallback headerFallback e he

end ZkFormal.NearV3.Assembly.RcptSkeleton
