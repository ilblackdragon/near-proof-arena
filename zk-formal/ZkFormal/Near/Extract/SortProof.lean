import ZkFormal.Near.Extract.SmallViews
import ZkFormal.Near.Extract.Segments
import ZkFormal.Near.Extract.BusCount

/-!
# ZkFormal.Near.Extract.SortProof — `SortViewStmt`

Pilot of the table-view extractions: constraint facts per row, segment
decomposition, view, traffic, and the ordering fact.
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace SortProof

variable {tr : Trace Fp} {pub : List Fp}

/-- Constraint `e` of the sort table holds on row `r`. -/
theorem con (hL : TableLocal Sort.table tr T_SORT pub) {r : Nat} (hr : r < tr.height T_SORT)
    {e : Expr} (he : e ∈ Sort.constraints) : e.eval tr T_SORT r pub = 0 :=
  hL.constr r hr e he

end SortProof

end ZkFormal.Near

namespace ZkFormal.Near.SortProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Sort

example : Dsl.bool (c act) ∈ Sort.constraints := by simp [Sort.constraints]
example : Expr.mul (c act) (sub (n (d 0)) (c bb)) ∈ Sort.constraints := by simp [Sort.constraints]
example : Expr.mul (c act) (sub (n (d 5)) (c (d 4))) ∈ Sort.constraints := by
  simp only [Sort.constraints, List.mem_append, List.mem_map, List.mem_range]; right; exact ⟨4, by omega, rfl⟩

end ZkFormal.Near.SortProof
