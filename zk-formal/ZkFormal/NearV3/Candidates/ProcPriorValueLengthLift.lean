import ZkFormal.NearV3.Candidates.ProcPriorValueLength
namespace ZkFormal.NearV3.Candidates.ProcPriorValueLength
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Rcpt.Candidates.SizeCount

def liftTrace (tr : Trace Fp) (tt : Nat) (selected : Nat→Bool) : Trace Fp :=
  {log:=tr.log,cell:=fun t r x=>if t=tt ∧ x=gate then (if selected r then 1 else 0) else tr.cell t r x}

theorem lift_old (tr : Trace Fp) (tt r x : Nat) (selected : Nat→Bool) (hx:x<gate) :
    (liftTrace tr tt selected).cell tt r x=tr.cell tt r x := by
  simp [liftTrace,show x≠gate by omega]

theorem lift_eval (tr : Trace Fp) (tt r : Nat) (selected : Nat→Bool) (pub : List Fp)
    (e : Expr) (hb:e.colBound≤gate) :
    e.eval (liftTrace tr tt selected) tt r pub=e.eval tr tt r pub := by
  induction e with
  | col x nx =>
    have hx:x<gate := by simp only [Expr.colBound] at hb; omega
    cases nx <;> exact lift_old tr tt _ x selected hx
  | add a b ha hb' | mul a b ha hb' =>
    have hh:a.colBound≤gate ∧ b.colBound≤gate := by simpa only [Expr.colBound,Nat.max_le] using hb
    simp only [Expr.eval,Expr.evalWith,rowEnv]
    congr 1
    · exact ha hh.1
    · exact hb' hh.2
  | neg a ha => exact congrArg (fun x : Fp=>-x) (ha hb)
  | _ => rfl

theorem lift_gate (tr : Trace Fp) (tt r : Nat) (selected : Nat→Bool) (pub : List Fp) :
    (c gate).eval (liftTrace tr tt selected) tt r pub=if selected r then 1 else 0 := by
  simp [c,Expr.eval,Expr.evalWith,rowEnv,liftTrace]

theorem old_bounds : ∀ e∈valTable.exprs,e.colBound≤gate := by
  have h:valTable.exprs.all (fun e=>decide (e.colBound≤gate))=true:=by decide +kernel
  exact fun e he=>of_decide_eq_true (List.all_eq_true.mp h e he)

/-- A Boolean selection announces each selected physical header once. Global
consumer uniqueness/balance is deliberately not inferred from this local lift. -/
theorem lift_local (bus : Nat) (tr : Trace Fp) (tt : Nat) (selected : Nat→Bool) (pub : List Fp)
    (h:TableLocal valTable tr tt pub)
    (hs:∀r,r<tr.height tt→selected r=true→(c ValV3.vf).eval tr tt r pub=1) :
    TableLocal (table bus) (liftTrace tr tt selected) tt pub := by
  refine ⟨h.log_ge,h.log_le,?_,?_⟩
  · intro r hr e he
    rcases List.mem_append.mp he with he|he
    · rw [lift_eval tr tt r selected pub e (old_bounds e (List.mem_append_left _ he))]
      exact h.constr r hr e he
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with rfl|rfl
      · have hone:(k 1).eval (liftTrace tr tt selected) tt r pub=(1:Fp):=rfl
        simp only [Dsl.bool,sub,eval_mul,eval_add,eval_neg,hone,lift_gate]
        cases selected r <;> simp <;> grind
      · have hone:(k 1).eval (liftTrace tr tt selected) tt r pub=(1:Fp):=rfl
        simp only [Dsl.not,sub,eval_mul,eval_add,eval_neg,hone,lift_gate]
        rw [lift_eval tr tt r selected pub (c ValV3.vf) (by decide +kernel)]
        cases he:selected r with
        | false => simp; grind
        | true => rw [hs r hr he]; simp; grind
  · intro r hr i hi e he
    rcases List.mem_append.mp hi with hi|hi
    · rw [lift_eval tr tt r selected pub e (old_bounds e (List.mem_append_right _
        (List.mem_flatMap.mpr ⟨i,hi,List.mem_append_left _ he⟩)))]
      exact h.bits r hr i hi e he
    · simp only [List.mem_singleton] at hi
      subst i
      simp only [interaction,List.mem_singleton] at he
      subst e
      rw [lift_gate]
      cases selected r <;> simp

end ZkFormal.NearV3.Candidates.ProcPriorValueLength
