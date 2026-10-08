import ZkFormal.NearV3.Candidates.ProcPriorMemoryLift
namespace ZkFormal.NearV3.Candidates.ProcPriorMemoryGated
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha.Table.E ZkFormal.Near

theorem base_gate_bit (wb rb cb : Nat) (tr : Trace Fp) (tt : Nat) (pub : List Fp)
    (h:TableLocal (ProcPriorMemoryTable.table wb rb cb) tr tt pub) (r : Nat) (hr:r<tr.height tt) :
    gateExpr.eval tr tt r pub=0 ∨ gateExpr.eval tr tt r pub=1 := by
  exact h.bits r hr (ProcPriorMemoryTable.interactions wb rb cb)[3]!
    (by simp [ProcPriorMemoryTable.table,ProcPriorMemoryTable.interactions]) gateExpr
    (by simp [ProcPriorMemoryTable.interactions,gateExpr])

/-- Executable one-column extension gives the degree-reduced local witness. -/
theorem lift_local (wb rb cb : Nat) (tr : Trace Fp) (tt : Nat) (pub : List Fp)
    (h:TableLocal (ProcPriorMemoryTable.table wb rb cb) tr tt pub) :
    TableLocal (table wb rb cb) (liftTrace tr tt pub) tt pub := by
  refine ⟨h.log_ge,h.log_le,?_,?_⟩
  · intro r hr e he
    rcases List.mem_append.mp he with he|he
    · rw [lift_eval tr tt r pub e (old_bounds wb rb cb e (List.mem_append_left _ he))]
      exact h.constr r hr e he
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with rfl|rfl
      · have hh:=base_gate_bit wb rb cb tr tt pub h r hr
        have hone:(k 1).eval (liftTrace tr tt pub) tt r pub=(1:Fp) := rfl
        simp only [ZkFormal.Chacha.Table.boolC,sub,eval_mul,eval_add,eval_neg,hone,lift_gate]
        rcases hh with hh|hh <;> rw [hh] <;> grind
      · simp only [gateEq,sub,eval_add,eval_neg,lift_gate_eq]
        grind
  · intro r hr i hi e he
    simp only [table,interactions,ProcPriorMemoryTable.interactions,List.take,List.cons_append,List.nil_append,
      List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl
    all_goals simp only [List.mem_singleton] at he; subst e
    · rw [lift_eval tr tt r pub _ (by decide +kernel)]
      exact h.bits r hr (ProcPriorMemoryTable.interactions wb rb cb)[0]!
        (by simp [ProcPriorMemoryTable.table,ProcPriorMemoryTable.interactions]) _
        (by simp [ProcPriorMemoryTable.interactions])
    · rw [lift_eval tr tt r pub _ (by decide +kernel)]
      exact h.bits r hr (ProcPriorMemoryTable.interactions wb rb cb)[1]!
        (by simp [ProcPriorMemoryTable.table,ProcPriorMemoryTable.interactions]) _
        (by simp [ProcPriorMemoryTable.interactions])
    · rw [lift_eval tr tt r pub _ (by decide +kernel)]
      exact h.bits r hr (ProcPriorMemoryTable.interactions wb rb cb)[2]!
        (by simp [ProcPriorMemoryTable.table,ProcPriorMemoryTable.interactions]) _
        (by simp [ProcPriorMemoryTable.interactions])
    · rw [lift_gate]
      exact base_gate_bit wb rb cb tr tt pub h r hr

end ZkFormal.NearV3.Candidates.ProcPriorMemoryGated
