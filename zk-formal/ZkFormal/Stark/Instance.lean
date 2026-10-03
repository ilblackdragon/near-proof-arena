import ZkFormal.Stark.Field
import ZkFormal.Algebra.Fp8
import ZkFormal.Algebra.Decode

/-!
# ZkFormal.Stark.Instance — `StarkField` for L1's BabyBear and `Fp8`

The deployed instantiation: `F = ZkFormal.Algebra.Fp`, `K = ZkFormal.Algebra.Fp8`.
-/

namespace ZkFormal.Stark

open ZkFormal.Algebra

instance : StarkField Fp Fp8 where
  toNat := Fp.toNat
  embed := Fp8.ofBase
  limbs := fun a => [a.c0, a.c1, a.c2, a.c3, a.c4, a.c5, a.c6, a.c7]
  ofLimbs := fun l => Fp8.ofCoeffs fun i => l.getD i 0
  twoAdicGen := Fp.twoAdicGen
  shift := 31

/-- The deployed verifier's field pair. -/
abbrev BB := Fp
abbrev BB8 := Fp8

end ZkFormal.Stark
