import ZkFormal.Prover.SizeBound
import ZkFormal.NearAssembly.Final
import ZkFormal.Toy.Air

/-!
# ZkFormal.Prover.SizeBoundNear — `NearSizeStmt` (lane L7-size)

The generic header-free bound `SizeBound.sizeBound_le` instantiated at the deployed
parameters with per-layer arity cost `κ = 86` (`32·2^a ≤ 86·a` for `a ∈ {1,2,3}`):
`sizeMax nearAir Params.default 86 = 7 426 175 ≤ 8 388 608`, closing
`NearAssembly.NearSizeStmt` for every admissible NEAR header.  The toy AIR is checked
the same way as a sanity instance.
-/

namespace ZkFormal.Prover.SizeBound

open ZkFormal ZkFormal.Stark ZkFormal.Air ZkFormal.Near

/-- Per-layer arity cost of the deployed parameters (`maxArityLog = 3`). -/
theorem kappa_default :
    ∀ a, 1 ≤ a → a ≤ max Params.default.maxArityLog 1 → 32 * 2 ^ a ≤ a * 86 := by
  intro a h1 h2
  have h3 : a ≤ 3 := h2
  obtain rfl | rfl | rfl : a = 1 ∨ a = 2 ∨ a = 3 := by omega
  all_goals decide

theorem near_sizeMax : sizeMax nearAir Params.default 86 = 7426175 := by decide +kernel

/-- **`NearSizeStmt`**: every admissible NEAR header has `sizeBound ≤ 8 MiB`. -/
theorem near_size : NearAssembly.NearSizeStmt := fun hdr h =>
  Nat.le_trans (sizeBound_le nearAir Params.default hdr 86 kappa_default (verifier_headerOk h).1)
    (by rw [near_sizeMax]; decide)

theorem toy_sizeMax : sizeMax Toy.toyAir Params.default 86 ≤ 8388608 := by decide +kernel

/-- Sanity instance: the toy AIR's size bound via the generic route. -/
theorem toy_size' : ∀ hdr, (Vd Toy.toyAir).headerOk hdr = true →
    sizeBound (Vd Toy.toyAir) hdr ≤ 8388608 := fun hdr h =>
  Nat.le_trans (sizeBound_le Toy.toyAir Params.default hdr 86 kappa_default (verifier_headerOk h).1)
    toy_sizeMax

end ZkFormal.Prover.SizeBound
