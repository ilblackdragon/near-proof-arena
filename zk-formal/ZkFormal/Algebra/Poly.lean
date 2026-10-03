import ZkFormal.Algebra.Transport

/-!
# ZkFormal.Algebra.Poly — univariate polynomials (definitions)

Coefficient lists, lowest degree first; trailing zeros are allowed, so the
degree notion is the semantic bound `DegLt f D` ("all coefficients from `D`
on vanish") together with the computable `size` (length after trimming).
Generic over any `Lean.Grind.CommRing` (field facts need `Lean.Grind.Field`).

Theorems: `ZkFormal.Algebra.PolyLemmas` (eval homomorphism, degree bounds,
root bound `card_roots_le`, Lagrange interpolation).
-/

namespace ZkFormal.Algebra

open Lean.Grind

/-- A polynomial `Σ coeffs[i] · X^i`. -/
structure Poly (K : Type) where
  coeffs : List K

namespace Poly

section Ring
variable {K : Type} [CommRing K]

/-- Coefficient of `X^i`. -/
def coeff (f : Poly K) (i : Nat) : K := f.coeffs.getD i 0

/-- Horner evaluation. -/
def evalL (x : K) : List K → K
  | [] => 0
  | c :: cs => c + x * evalL x cs

def eval (f : Poly K) (x : K) : K := evalL x f.coeffs

/-- Coefficientwise sum (padding the shorter list). -/
def addL : List K → List K → List K
  | [], g => g
  | f, [] => f
  | a :: f, b :: g => (a + b) :: addL f g

def scaleL (c : K) (f : List K) : List K := f.map (c * ·)

/-- Schoolbook product. -/
def mulL : List K → List K → List K
  | [], _ => []
  | a :: f, g => addL (scaleL a g) (0 :: mulL f g)

instance : Add (Poly K) := ⟨fun f g => ⟨addL f.coeffs g.coeffs⟩⟩
instance : Mul (Poly K) := ⟨fun f g => ⟨mulL f.coeffs g.coeffs⟩⟩
instance : Neg (Poly K) := ⟨fun f => ⟨scaleL (-1) f.coeffs⟩⟩
instance : Sub (Poly K) := ⟨fun f g => f + -g⟩

/-- The zero polynomial. -/
def zero : Poly K := ⟨[]⟩
/-- Constant. -/
def C (c : K) : Poly K := ⟨[c]⟩
/-- The variable. -/
def X : Poly K := ⟨[0, 1]⟩
/-- Scalar multiple. -/
def smul (c : K) (f : Poly K) : Poly K := ⟨scaleL c f.coeffs⟩

/-- `f` has degree `< D` (all coefficients from index `D` on are zero). -/
def DegLt (f : Poly K) (D : Nat) : Prop := ∀ i, D ≤ i → f.coeff i = 0

/-- `f` is the zero polynomial (all coefficients zero). -/
def IsZero (f : Poly K) : Prop := ∀ i, f.coeff i = 0

/-- Drop trailing zeros. -/
def trimL [DecidableEq K] (f : List K) : List K :=
  (f.reverse.dropWhile (· = 0)).reverse

/-- Number of coefficients after trimming: `degree + 1`, and `0` for the zero
polynomial.  `DegLt f D ↔ size f ≤ D` (`PolyLemmas.degLt_iff_size_le`). -/
def size [DecidableEq K] (f : Poly K) : Nat := (trimL f.coeffs).length

/-- Synthetic division by `X − r` (quotient): for `f = c :: g`,
`quot f r = g + r · quot g r`, so `f(x) − f(r) = (x − r) · quot f r (x)`. -/
def quotL (r : K) : List K → List K
  | [] => []
  | _ :: g => addL g (scaleL r (quotL r g))

def quot (f : Poly K) (r : K) : Poly K := ⟨quotL r f.coeffs⟩

/-- Product of a list of ring elements. -/
def prodL : List K → K
  | [] => 1
  | a :: l => a * prodL l

/-- `∏_{a ∈ xs} (X − a)`. -/
def linProd : List K → Poly K
  | [] => ⟨[1]⟩
  | a :: xs => ⟨mulL [-a, 1] (linProd xs).coeffs⟩

/-- Sum of a list of polynomials. -/
def sum (fs : List (Poly K)) : Poly K := fs.foldr (· + ·) zero

end Ring

section Field
variable {K : Type} [Field K]

/-- Lagrange interpolation through `(x, v x)` for `x ∈ xs` (distinct points):
`Σ_{x ∈ xs} v x · ∏_{y ≠ x} (X − y) / ∏_{y ≠ x} (x − y)`. -/
def lagrange [DecidableEq K] (xs : List K) (v : K → K) : Poly K :=
  sum (xs.map fun x => smul (v x * (prodL ((xs.erase x).map (x - ·)))⁻¹) (linProd (xs.erase x)))

end Field

end Poly
end ZkFormal.Algebra
