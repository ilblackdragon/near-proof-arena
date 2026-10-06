import ZkFormal.NearV3.Sched.Budget

/-!
# ZkFormal.NearV3.Sched.BudgetCheck — kernel-checked budget of the scheduler tables

`(width, interactions, aux, degree, W_eq, maxLog)` per table, order `schV3, sscV3, sprV3, smmV3,
scpV3, sdsV3`, at `auxGroup = 1`.
-/

namespace ZkFormal.NearV3.Sched.Budget

theorem report_g1 : report 1 =
    [(106, 14, 14, 4, 242, 22), (50, 6, 6, 4, 122, 22), (64, 11, 11, 4, 176, 22),
     (18, 4, 4, 4, 74, 22), (33, 1, 1, 4, 65, 22), (55, 8, 8, 4, 143, 22)] := by decide +kernel

theorem weqSched_g1 : weqSched 1 = 822 := by decide +kernel

end ZkFormal.NearV3.Sched.Budget
