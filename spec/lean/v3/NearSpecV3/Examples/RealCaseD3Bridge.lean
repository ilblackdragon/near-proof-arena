import NearSpecV3.D3.FunctionCall
import NearSpecV3.Successor.Config

/-!
# Bool ↔ Prop bridges for the D3 kernel non-vacuity theorems (`RealCaseD3.lean`)

`RelD3` is `Except`-primary (`checkD3 c w = .ok ()`), and its `Decidable` instance is
`decidable_of_iff` over the theorem `relD3_iff_acceptsD3`. A theorem is opaque to kernel reduction,
so `decide +kernel` on `RelD3 c w` itself fails with an application type mismatch
(`docs/HANDOVER.md`). The non-vacuity theorems therefore decide the **Bool mirror** in the kernel
(`acceptsD3 c w = true`, `acceptsSuccessor cfg c w = true`, a closed `Bool` equation that reduces
by evaluation) and transport the result to the `Prop` with the proved bridges below.

None of this changes a definition. `RelD3`, `checkD3`, `acceptsD3`, `RelSuccessor` and `Tier.rel` are
the signed and successor terms as they stand. The bridges are ordinary theorems over all inputs.
-/

namespace NearSpecV3.Examples

open NearSpecV3.D3 NearSpecV3.Successor

/-- The Bool-primary characterization of the signed relation, in the direction the negative
theorems use: a `false` verdict refutes `RelD3`. -/
theorem not_relD3_of_accepts_false (c w : NearSpec.Bytes) (h : acceptsD3 c w = false) :
    ¬ RelD3 c w := by
  intro hr
  rw [(relD3_iff_acceptsD3 c w).1 hr] at h
  exact Bool.noConfusion h

/-- The successor relation is Bool-characterized by its own mirror. -/
theorem relSuccessor_iff_accepts (cfg : ProtocolCfg) (c w : NearSpec.Bytes) :
    RelSuccessor cfg c w ↔ acceptsSuccessor cfg c w = true := by
  unfold RelSuccessor acceptsSuccessor
  cases h : checkSuccessor cfg c w with
  | ok u => cases u; simp
  | error e => simp

/-- A tier accepts an input when its Bool mirror does. -/
theorem tierRel_of_accepts (t : NearSpecV3.Successor.Tier) (c w : NearSpec.Bytes)
    (h : acceptsSuccessor t.cfg c w = true) : NearSpecV3.Successor.Tier.rel t c w :=
  (relSuccessor_iff_accepts t.cfg c w).2 h

/-- A tier rejects an input when its Bool mirror does. -/
theorem not_tierRel_of_accepts_false (t : NearSpecV3.Successor.Tier) (c w : NearSpec.Bytes)
    (h : acceptsSuccessor t.cfg c w = false) : ¬ NearSpecV3.Successor.Tier.rel t c w := by
  intro hr
  rw [(relSuccessor_iff_accepts t.cfg c w).1 hr] at h
  exact Bool.noConfusion h

end NearSpecV3.Examples
