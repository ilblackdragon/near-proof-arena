import ZkFormal.NearV3.Candidates.ProcPriorMemoryTransport
namespace ZkFormal.NearV3.Candidates.ProcPriorMemoryGated
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha.Table.E ZkFormal.Near

def liftTrace (tr : Trace Fp) (tt : Nat) (pub : List Fp) : Trace Fp :=
  {log:=tr.log,cell:=fun t r x=>if t=tt ∧ x=stampGate then gateExpr.eval tr tt r pub else tr.cell t r x}

theorem lift_old (tr : Trace Fp) (tt r x : Nat) (pub : List Fp) (hx:x<11) :
    (liftTrace tr tt pub).cell tt r x=tr.cell tt r x := by
  simp [liftTrace,stampGate,show x≠11 by omega]

theorem lift_eval (tr : Trace Fp) (tt r : Nat) (pub : List Fp) (e : Expr) (hb:e.colBound≤11) :
    e.eval (liftTrace tr tt pub) tt r pub=e.eval tr tt r pub := by
  induction e with
  | col x nx =>
    have hx:x<11 := by simp only [Expr.colBound] at hb; omega
    cases nx <;> exact lift_old tr tt _ x pub hx
  | add a b ha hb' | mul a b ha hb' =>
    have hh:a.colBound≤11 ∧ b.colBound≤11 := by simpa only [Expr.colBound,Nat.max_le] using hb
    simp only [Expr.eval,Expr.evalWith,rowEnv]
    congr 1
    · exact ha hh.1
    · exact hb' hh.2
  | neg a ha => exact congrArg (fun x : Fp=>-x) (ha hb)
  | _ => rfl

theorem lift_gate (tr : Trace Fp) (tt r : Nat) (pub : List Fp) :
    (c stampGate).eval (liftTrace tr tt pub) tt r pub=gateExpr.eval tr tt r pub := by
  simp [c,Expr.eval,Expr.evalWith,rowEnv,liftTrace]

set_option maxRecDepth 8192 in
theorem old_bounds (wb rb cb : Nat) :
    ∀ e∈(ProcPriorMemoryTable.table wb rb cb).exprs,e.colBound≤11 := by
  change ∀ e∈(ProcPriorMemoryTable.table 0 1 2).exprs,e.colBound≤11
  have hh: (ProcPriorMemoryTable.table 0 1 2).exprs.all (fun e=>decide (e.colBound≤11))=true := by decide +kernel
  intro e he
  exact of_decide_eq_true (List.all_eq_true.mp hh e he)

theorem lift_gate_eq (tr : Trace Fp) (tt r : Nat) (pub : List Fp) :
    (c stampGate).eval (liftTrace tr tt pub) tt r pub=gateExpr.eval (liftTrace tr tt pub) tt r pub := by
  rw [lift_gate,lift_eval tr tt r pub gateExpr (by decide +kernel)]

end ZkFormal.NearV3.Candidates.ProcPriorMemoryGated
