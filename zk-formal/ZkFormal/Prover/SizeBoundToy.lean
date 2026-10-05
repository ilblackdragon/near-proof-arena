import ZkFormal.Prover.SizeBoundNear
import ZkFormal.Toy.Air
import ZkFormal.Prover.Compose

/-! Sanity instance of the generic size bound on the M2 toy AIR (kept out of the NEAR
certificate's import closure). -/

namespace ZkFormal.Prover.SizeBound

open ZkFormal ZkFormal.Stark ZkFormal.Air ZkFormal.Prover

theorem toy_sizeMax : sizeMax Toy.toyAir Params.default 86 ≤ 8388608 := by decide +kernel

/-- Sanity instance: the toy AIR's size bound via the generic route. -/
theorem toy_size' : ∀ hdr, (Vd Toy.toyAir).headerOk hdr = true →
    sizeBound (Vd Toy.toyAir) hdr ≤ 8388608 := fun hdr h =>
  Nat.le_trans (sizeBound_le Toy.toyAir Params.default hdr 86 kappa_default (verifier_headerOk h).1)
    toy_sizeMax

end ZkFormal.Prover.SizeBound
