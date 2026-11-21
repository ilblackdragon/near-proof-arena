import FinalM5d.Final

/-!
# FinalM5d.RsCoeff — the `RS` rows' GF(2) bit matrices are the spec's GF(2^8) products

The `RS` table computes parity bit `k` of part `d + i` as the parity of
`Σ_{j,m} mulBit (M[d+i][j]) k m · x_j[m]` (`Rs.paritySum`), with `M = buildMatrix d t` and
`mulBit c k m` = bit `k` of `gfMul c (2^m)`. `coeff_linear` checks, in the kernel, for every
coefficient `c` of the class matrix's parity rows, every byte `x` and every bit `k`, that bit `k`
of the spec's `gfMul c x` is that parity over the bits of `x`.
-/

namespace FinalM5d.RsCoeff

open NearSpecV3 FinalM5d

/-- Bit `k` of `gfMul c x` as the GF(2) sum over the bits of `x`. -/
def linAt (c x k : Nat) : Bool :=
  ((List.range 8).foldl (fun acc m => acc + (x / 2 ^ m % 2) * Rs.mulBit c k m) 0) % 2 ==
    gfMul c x / 2 ^ k % 2

/-- The class matrix's parity coefficients. -/
def coeffs : List Nat := (Rs.matrix.drop RSD).flatten

theorem coeffs_length : coeffs.length = NPAR * RSD := by decide +kernel

theorem coeff_linear :
    coeffs.all (fun c => (List.range 256).all fun x => (List.range 8).all fun k => linAt c x k) = true := by
  decide +kernel

end FinalM5d.RsCoeff
