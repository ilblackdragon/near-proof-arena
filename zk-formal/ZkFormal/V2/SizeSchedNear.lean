import ZkFormal.V2.SizeSched
import ZkFormal.Prover.SizeBoundNear
import ZkFormal.Toy.Air
import ZkFormal.Prover.Compose

/-!
# ZkFormal.V2.SizeSchedNear — the schedule-exact size bound at the deployed AIRs

Kernel evaluations of `SizeSched.sizeMaxSched` at `Params.default` (`B = 5`, `M = 3`,
`d ≤ 21`, `nq = 216`) and the resulting header-free size theorems.  `nearAir` has 7
tables with `maxLog = [22, 22, 16, 18, 12, 15, 13]`, so up to 6 roll-in commitments
(capped per remaining distance by `capE`); the toy AIR has one table (no roll-ins).

| AIR | `friSchedMax` (B/query) | FRI openings `nq·…` | `sizeMaxSched` | `sizeMax … 86` | saved |
|---|---|---|---|---|---|
| `nearAir` | 12 928 (vs `pot` 21 966) | 2 792 448 | **5 473 967** | 7 426 175 | 1 952 208 |
| `toyAir`  |  8 064 | 1 741 824 | **2 832 681** | 5 835 513 | 3 002 832 |

Without roll-ins the NEAR value would be 4 423 343 (the V3-D0 §5.3 ≈4.4 MB estimate).
The up to six roll-in commitments, each an extra Merkle path near the top of the FRI
tree, account for the remaining 1 050 624 B.  The DP is the exact worst case of
the cost model, where roll-in positions are bounded only by `capE`.
-/

namespace ZkFormal.V2.SizeSched

open ZkFormal ZkFormal.Stark ZkFormal.Air ZkFormal.Near ZkFormal.Prover

theorem near_friSchedMax : friSchedMax nearAir Params.default = 12928 := by decide +kernel

theorem near_sizeMaxSched : sizeMaxSched nearAir Params.default = 5473967 := by decide +kernel

theorem toy_friSchedMax : friSchedMax Toy.toyAir Params.default = 8064 := by decide +kernel

theorem toy_sizeMaxSched : sizeMaxSched Toy.toyAir Params.default = 2832681 := by decide +kernel

/-- Every admissible NEAR header has `sizeBound ≤ 5 473 967` bytes (vs `7 426 175` from
`SizeBound.near_sizeMax`). -/
theorem near_size_sched : ∀ hdr, (Vd nearAir).headerOk hdr = true →
    sizeBound (Vd nearAir) hdr ≤ 5473967 := fun hdr h =>
  Nat.le_trans (sizeBound_le_sched nearAir Params.default hdr (verifier_headerOk h).1)
    (Nat.le_of_eq near_sizeMaxSched)

/-- Every admissible toy header has `sizeBound ≤ 2 832 681` bytes. -/
theorem toy_size_sched : ∀ hdr, (Vd Toy.toyAir).headerOk hdr = true →
    sizeBound (Vd Toy.toyAir) hdr ≤ 2832681 := fun hdr h =>
  Nat.le_trans (sizeBound_le_sched Toy.toyAir Params.default hdr (verifier_headerOk h).1)
    (Nat.le_of_eq toy_sizeMaxSched)

/-- The refinement at the deployed parameters (`κ = 86`), generic in the AIR. -/
theorem sizeMaxSched_le_default (A : Air) :
    sizeMaxSched A Params.default ≤ SizeBound.sizeMax A Params.default 86 :=
  sizeMaxSched_le A Params.default 86 SizeBound.kappa_default

end ZkFormal.V2.SizeSched
