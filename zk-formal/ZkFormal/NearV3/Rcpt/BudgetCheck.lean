import ZkFormal.NearV3.Rcpt.Budget

/-!
# ZkFormal.NearV3.Rcpt.BudgetCheck — kernel-checked budget of the receipt-side tables

`(width, interactions, aux, degree, W_eq, maxLog)` per table, in the order
`rcptV3, acctV3, akeyV3, bndV3, srcpV3, sizeV3`, at `auxGroup = 1` and `3`.
-/

namespace ZkFormal.NearV3.Rcpt.Budget

theorem report_g1 : report 1 =
    [(263, 18, 18, 4, 431, 22), (16, 13, 13, 4, 144, 17), (7, 3, 3, 4, 55, 16),
     (6, 3, 3, 4, 54, 13), (56, 5, 5, 4, 120, 20), (31, 1, 1, 4, 63, 2)] := by decide +kernel

theorem report_g3 : report 3 =
    [(263, 18, 6, 8, 367, 22), (16, 13, 5, 8, 112, 17), (7, 3, 2, 6, 63, 16),
     (6, 3, 2, 6, 62, 13), (56, 5, 2, 8, 128, 20), (31, 1, 1, 4, 63, 2)] := by decide +kernel

theorem weqRcpt_g1 : weqRcpt 1 = 867 := by decide +kernel
theorem weqRcpt_g3 : weqRcpt 3 = 795 := by decide +kernel

end ZkFormal.NearV3.Rcpt.Budget
