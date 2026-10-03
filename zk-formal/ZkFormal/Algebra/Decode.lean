import ZkFormal.Algebra.Fp8
import ArenaCore

/-!
# ZkFormal.Algebra.Decode — challenges from oracle answers (definitions)

DESIGN.md §4: `decodeChal(y)` reads 8 big-endian `u32` limbs from the
32-byte answer `y`, limb `i` (bytes `4i … 4i+3`) is the coefficient of
`x^i`, each reduced mod `p`.  Each residue has at most 3 preimages in
`[0, 2^32)` (`2^32 < 3p`), so at most `3^8` answers map to a given element of
`K` (`decodeChal_count`, in `Algebra.Statements`).

`decodeOod` is the out-of-domain sample: if all non-constant coefficients
vanish (the decoded element lies in `F_p`), coefficient 1 is set to `1`, so
the result is never in the base field (`decodeOod_not_base`).
-/

namespace ZkFormal.Algebra

open ArenaCore

/-- Big-endian `u32` limb `i` of `y` (bytes `4i … 4i+3`). -/
def be32 (y : Bytes) (i : Nat) : Nat := Bytes.beToNat ((y.drop (4 * i)).take 4)

/-- A commit-phase challenge in `K` from one oracle answer. -/
def decodeChal (y : Bytes) : Fp8 := Fp8.ofCoeffs fun i => Fp.ofNat (be32 y i)

/-- The out-of-domain point: `decodeChal`, pushed out of `F_p` if needed. -/
def decodeOod (y : Bytes) : Fp8 :=
  if (decodeChal y).IsBase then { decodeChal y with c1 := 1 } else decodeChal y

theorem decodeOod_not_base (y : Bytes) : ¬ (decodeOod y).IsBase := by
  unfold decodeOod
  split
  · intro h; exact absurd h.1 (by show (1 : Fp) ≠ 0; decide +kernel)
  · next h => exact h

theorem decodeOod_ne_ofBase (y : Bytes) (a : Fp) : decodeOod y ≠ Fp8.ofBase a := by
  intro h
  exact decodeOod_not_base y ((Fp8.isBase_iff _).mpr ⟨a, h⟩)

end ZkFormal.Algebra
