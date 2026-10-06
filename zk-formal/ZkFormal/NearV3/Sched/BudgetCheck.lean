import ZkFormal.NearV3.Sched.Budget

/-!
# ZkFormal.NearV3.Sched.BudgetCheck — kernel-checked budget of the scheduler tables

`(width, interactions, aux, degree, W_eq, maxLog)` per table, order `schV3, ssdV3, sprV3, smmV3,
scpV3`, at `auxGroup = 1` (`ssdV3` = scan + distribute, width cut B: 168 + 201 → 223).
-/

namespace ZkFormal.NearV3.Sched.Budget

theorem report_g1 : report 1 =
    [(114, 14, 14, 4, 250, 22), (119, 10, 10, 4, 223, 22), (64, 11, 11, 4, 176, 22),
     (18, 4, 4, 4, 74, 22), (33, 1, 1, 4, 65, 22)] := by decide +kernel

theorem weqSched_g1 : weqSched 1 = 788 := by decide +kernel

end ZkFormal.NearV3.Sched.Budget
