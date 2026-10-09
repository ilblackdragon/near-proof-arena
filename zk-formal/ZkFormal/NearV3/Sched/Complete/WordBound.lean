import ZkFormal.NearV3.Sched.Complete.Steps
import ZkFormal.Chacha.Table

/-!
# ZkFormal.NearV3.Sched.Complete.WordBound — the ChaCha word bound `W0` (RelD0a A9)

RelD0a's conjunct A9 (`e.chacha_words`, `NearSpecV3.a9`, user decision 2026-10-09):
`chachaWords cb w ≤ W0 = 770,000`, the ChaCha20 words drawn by all scheduler runs.

* `a9_iff`: A9 is exactly the decidable comparison of the spec's count with `W`.
* `lane_W0`: at `W0` the three lane tables fit (`shufV3 < 2^22`, `genV3 < 2^20`,
  `chachaV3 ≤ 86·(W0 + 15·33)/16 = 4,141,410 < 2^22`).
* `chacha_cap_short`: the deployed ChaCha table cap `Chacha.Table.maxLog = 21` is **below** the
  `W0` lane (`2^21 < 4,141,411`). Raising it to `22` is the planned completion step; it is held
  back because four measured candidate families (`ProcPriorProcessRepaired`, `SortEmpty`,
  `ProcPriorCodec`, `ProcPriorComparatorRouted`) would then exceed the fingerprint budget
  `busBudget = 2^36` (STATUS-V3-AIR §5). The bus budget is not changed here.
-/

namespace ZkFormal.NearV3.Sched.Complete

open NearSpecV3

theorem a9_iff (W : Nat) (cb w : NearSpec.Bytes) : a9 W cb w = true ↔ chachaWords cb w ≤ W := by
  unfold a9; simp only [decide_eq_true_eq]

theorem W0_eq : W0 = 770000 := rfl

/-- The lane tables at the challenge word bound. -/
theorem lane_W0 (Ps : List IStat) (h7 : A7 2000000 Ps) (h8 : A8 Ps) (hb : Steps 43 Ps)
    (hT : Ps.length ≤ 33) (hW : total IStat.genRows Ps ≤ W0) :
    total IStat.shufRows Ps + 1 ≤ 2 ^ 22 ∧ total IStat.genRows Ps + 1 ≤ 2 ^ 20 ∧
    total IStat.chachaRows Ps + 1 ≤ 2 ^ 22 :=
  lane_770k_22 Ps h7 h8 hb hT hW

/-- The deployed ChaCha table cap does not yet hold the `W0` lane. -/
theorem chacha_cap_short : 2 ^ ZkFormal.Chacha.Table.maxLog < chachaMax W0 33 + 1 ∧
    chachaMax W0 33 + 1 ≤ 2 ^ 22 := by decide

end ZkFormal.NearV3.Sched.Complete
