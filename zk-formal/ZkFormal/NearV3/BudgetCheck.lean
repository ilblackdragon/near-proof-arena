import ZkFormal.NearV3.Budget

/-!
# ZkFormal.NearV3.BudgetCheck — kernel-checked budget of the v3 trie tables

`(width, interactions, aux, degree, W_eq, maxLog)` per table, in the order
`nodeV3, headV3, valV3, walkV3, uniqV3`, at `auxGroup = 1` and `3`.  `nodeV3` includes the
`UPB` delta (M7c: column `mU`, two interactions; totals 838 / 782 → 855 / 783) and the
`VSLOT (vid)` receive on written value windows (gate `valStart·tw`, degree 2, no column; degree
4 → 5 at `g = 1`; totals 855 / 783 → 871 / 791).
-/

namespace ZkFormal.NearV3.Budget

theorem report_g1 : report 1 =
    [(186, 21, 21, 5, 386, 22), (73, 8, 8, 4, 161, 11), (15, 7, 7, 4, 95, 22),
     (56, 6, 6, 4, 128, 21), (53, 2, 2, 5, 101, 22)] := by decide +kernel

theorem report_g3 : report 3 =
    [(186, 21, 8, 8, 306, 22), (73, 8, 4, 8, 161, 11), (15, 7, 3, 8, 95, 22),
     (56, 6, 2, 8, 128, 21), (53, 2, 2, 5, 101, 22)] := by decide +kernel

theorem weqTrie_g1 : weqTrie 1 = 871 := by decide +kernel
theorem weqTrie_g3 : weqTrie 3 = 791 := by decide +kernel

end ZkFormal.NearV3.Budget
