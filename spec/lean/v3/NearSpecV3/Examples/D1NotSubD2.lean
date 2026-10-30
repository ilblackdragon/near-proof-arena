import NearSpecV3.Examples.D1NotSubD2K0
import NearSpecV3.Examples.D1NotSubD2K1
import NearSpecV3.Examples.D1NotSubD2K2
import NearSpecV3.Examples.D1NotSubD2K3
import NearSpecV3.Examples.D1NotSubD2K4

/-!
# D1 ⊄ D2 (and D0 ⊄ D3): a kernel-checked counterexample

`claimGF`/`witnessGF` are d1run `ood/03-h10003-s0` (an honest chunk; nearcore `ok`) with the claim's
`epoch_start_after` flags set to 0. The segment ends at the genesis block, whose honest flag is 1.

* `checkD0` and `checkD1` accept: they require every flag to be 0 (`c.single_epoch`) and never
  compare the flags with the headers; the witness is the honest one.
* `checkD2` and `checkD3` reject with `invalid: epoch_start_after inconsistent with the headers`:
  they require `!b.isGenesis || flag = 1` for every block of the segment.

So the rung inclusions `D1 ⊂ D2` and `D0 ⊂ D3` are false as stated, and `WitnessLift`
(`RelD1a → ∃ w2, RelD3 cb w2`) cannot be proved unconditionally: the D2/D3 rejection reads only
the claim. No checker accepts a witness nearcore rejects here — the witness is nearcore-valid; the
difference is claim discipline (a false trusted fact, claim-v3 §2.2). All five verdicts (with
`RelD1a B0`, module `K4`) are
`decide +kernel`, no `native_decide`. On demand, not in CI.
-/

namespace NearSpecV3.Examples

open NearSpec NearSpecV3

theorem gf_relD0 : RelD0 claimGF witnessGF := gf_acceptsD0
theorem gf_relD1 : RelD1 claimGF witnessGF := gf_acceptsD1
theorem gf_not_relD2 : ¬ RelD2 claimGF witnessGF := by
  unfold RelD2; rw [gf_acceptsD2]; decide
theorem gf_not_relD3 : ¬ D3.RelD3 claimGF witnessGF := by
  rw [D3.relD3_iff_acceptsD3, gf_acceptsD3]; decide

/-- **D1 ⊂ D2 is false.** -/
theorem not_d1_sub_d2 : ¬ ∀ cb w, RelD1 cb w → RelD2 cb w :=
  fun h => gf_not_relD2 (h _ _ gf_relD1)

/-- **D1 ⊂ D3 is false.** -/
theorem not_d1_sub_d3 : ¬ ∀ cb w, RelD1 cb w → D3.RelD3 cb w :=
  fun h => gf_not_relD3 (h _ _ gf_relD1)

/-- **`RelD1a ⊂ RelD3` is false** (on the same bytes): the pair satisfies every D1a amendment at the
challenge instance `B0` (`gf_relD1a`, kernel). So `relD1a_relD3_of_d1_d2`'s hypothesis is false,
and `WitnessLift` with the identity witness fails on this pair. -/
theorem not_d1a_sub_d3 : ¬ ∀ cb w, RelD1a B0 cb w → D3.RelD3 cb w :=
  fun h => gf_not_relD3 (h _ _ gf_relD1a)

/-- **D0 ⊂ D3 is false.** -/
theorem not_d0_sub_d3 : ¬ ∀ cb w, RelD0 cb w → D3.RelD3 cb w :=
  fun h => gf_not_relD3 (h _ _ gf_relD0)

end NearSpecV3.Examples

#print axioms NearSpecV3.Examples.not_d1_sub_d2
#print axioms NearSpecV3.Examples.not_d0_sub_d3
#print axioms NearSpecV3.Examples.not_d1a_sub_d3
