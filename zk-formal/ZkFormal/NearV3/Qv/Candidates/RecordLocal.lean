import ZkFormal.NearV3.Qv.Candidates.RecordConcat
import ZkFormal.Near.Extract.Common

namespace ZkFormal.NearV3.Qv.Candidates.ValueGen
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra

/-- The executable concatenation satisfies the shared field-level local table
interface. Capacity is still an explicit input, separately from data validity. -/
theorem records_table_local (vs : List Record) (hv : ∀ v ∈ vs, v.Valid)
    (log : Nat) (hlog : 1≤log ∧ log≤ValueTable.table.maxLog)
    (hb : recordsSize vs≤2^log) :
    TableLocal ValueTable.table (recordsTrace vs log) 0 [] := by
  refine ⟨hlog.1,hlog.2,?_,?_⟩
  · intro r hr e he
    exact recordsTrace_local vs hv log hb hr e (List.mem_append_left _ he)
  · intro r hr i hi b hbit
    have hm : Expr.mul b (.add b (.neg (.const 1))) ∈ ValueTable.table.allConstraints := by
      apply List.mem_append_right
      apply List.mem_flatMap.mpr
      exact ⟨i,hi,List.mem_map.mpr ⟨b,hbit,rfl⟩⟩
    have he := recordsTrace_local (F:=Fp) vs hv log hb hr _ hm
    simp only [Expr.eval,Expr.evalWith,Lean.Grind.Semiring.natCast_one] at he
    rcases Lean.Grind.Field.of_mul_eq_zero he with hz | ho
    · exact Or.inl hz
    · right
      change b.evalWith (rowEnv (recordsTrace vs log) 0 r [])=1
      change b.evalWith (rowEnv (recordsTrace vs log) 0 r []) + -(1 : Fp)=0 at ho
      grind only

end ZkFormal.NearV3.Qv.Candidates.ValueGen
