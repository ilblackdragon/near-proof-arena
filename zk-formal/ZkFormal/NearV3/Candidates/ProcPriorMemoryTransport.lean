import ZkFormal.NearV3.Candidates.ProcPriorMemoryGated
namespace ZkFormal.NearV3.Candidates.ProcPriorMemoryGated
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha.Table.E ZkFormal.Near

/-- The extra gate column preserves all baseline local constraints and bits. -/
theorem to_base (wb rb cb : Nat) (tr : Trace Fp) (tt : Nat) (pub : List Fp)
    (h:TableLocal (table wb rb cb) tr tt pub) :
    TableLocal (ProcPriorMemoryTable.table wb rb cb) tr tt pub := by
  refine ⟨h.log_ge,h.log_le,?_,?_⟩
  · intro r hr e he
    exact h.constr r hr e (List.mem_append_left _ he)
  · intro r hr i hi b hb
    simp only [ProcPriorMemoryTable.table,ProcPriorMemoryTable.interactions,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl
    all_goals simp only [List.mem_singleton] at hb; subst b
    · exact h.bits r hr (ProcPriorMemoryTable.interactions wb rb cb)[0]! (by simp [table,interactions,ProcPriorMemoryTable.interactions]) _ (by simp [ProcPriorMemoryTable.interactions])
    · exact h.bits r hr (ProcPriorMemoryTable.interactions wb rb cb)[1]! (by simp [table,interactions,ProcPriorMemoryTable.interactions]) _ (by simp [ProcPriorMemoryTable.interactions])
    · exact h.bits r hr (ProcPriorMemoryTable.interactions wb rb cb)[2]! (by simp [table,interactions,ProcPriorMemoryTable.interactions]) _ (by simp [ProcPriorMemoryTable.interactions])
    · have hh:=h.bits r hr
        ⟨cb,[c stampGate],[n ProcPriorMemoryTable.stamp,.add (c ProcPriorMemoryTable.stamp) (k 1),k 1],true⟩
        (by simp [table,interactions,ProcPriorMemoryTable.interactions]) (c stampGate) (by simp)
      rw [gate_value wb rb cb tr tt pub h r hr] at hh
      exact hh

end ZkFormal.NearV3.Candidates.ProcPriorMemoryGated
