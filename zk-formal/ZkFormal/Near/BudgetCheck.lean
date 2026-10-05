import ZkFormal.Near.Budget

/-!
# ZkFormal.Near.BudgetCheck — kernel-checked width budget and well-formedness

Leaf module (kernel evaluation of the whole AIR value; nothing imports it
except the root).  `W_eq` at the deployed `auxGroup = 1` is `1766`
(NEAR-AIR.md §5).
-/

namespace ZkFormal.Near.Budget

open ZkFormal.Air

/-- **The width budget** (DESIGN.md §5.2: `W_eq ≤ 3000`). -/
theorem weq_le : weq nearAir 1 ≤ 3000 := by decide +kernel

/-- L4's static well-formedness (columns, buses, degree ≤ 16, multiplicity
and fingerprint budgets) holds for `nearAir`. -/
theorem nearAir_wf : Air.wf nearAir 16 = true := by decide +kernel

end ZkFormal.Near.Budget
