import ZkFormal.Algebra.Poly
import ZkFormal.Algebra.RS
import ZkFormal.Algebra.Decode
import ZkFormal.LineLemma

/-!
# ZkFormal.Algebra.Statements — lane L1 open obligations, as `Prop`s

Frozen interface (DESIGN.md §9 L1).  Each `…Stmt` is proved as
`theorem … : …Stmt` in its own module (see docs/zk-formal/STATUS-L1.md);
`Algebra.Compose` builds the downstream objects from these hypotheses.

Already proved outright (not listed here): `p_prime`, `Fp.pow_card_sub_one`,
`Fp.eleven_nonsquare`, `instance : Field Fp`, `instance : Field Fp8`,
`Fp8.mem_all`, `Fp8.nodup_all`, `Fp8.length_all`, two-adic generators,
`decodeOod_not_base`.
-/

namespace ZkFormal.Algebra

open Lean.Grind ArenaCore ArenaCore.Security

/-! ## Polynomials -/

/-- `eval` is a ring homomorphism `Poly K → K` (for each point). -/
def PolyEvalStmt : Prop :=
  ∀ (K : Type) [CommRing K] (f g : Poly K) (x c : K),
    (f + g).eval x = f.eval x + g.eval x ∧
    (f * g).eval x = f.eval x * g.eval x ∧
    (-f).eval x = -f.eval x ∧
    (f - g).eval x = f.eval x - g.eval x ∧
    (Poly.smul c f).eval x = c * f.eval x ∧
    (Poly.C c).eval x = c ∧
    (Poly.X : Poly K).eval x = x ∧
    (Poly.zero : Poly K).eval x = 0

/-- Coefficients of sums/scalings/products, and degree bounds. -/
def PolyDegStmt : Prop :=
  ∀ (K : Type) [CommRing K] (f g : Poly K) (c : K) (a b : Nat),
    (∀ i, (f + g).coeff i = f.coeff i + g.coeff i) ∧
    (∀ i, (Poly.smul c f).coeff i = c * f.coeff i) ∧
    f.DegLt f.coeffs.length ∧
    (f.DegLt a → a ≤ b → f.DegLt b) ∧
    (f.DegLt a → g.DegLt a → (f + g).DegLt a) ∧
    (f.DegLt a → (Poly.smul c f).DegLt a) ∧
    (f.DegLt a → (-f).DegLt a) ∧
    (f.DegLt (a + 1) → g.DegLt (b + 1) → (f * g).DegLt (a + b + 1))

/-- `DegLt` agrees with the computable `size`. -/
def PolySizeStmt : Prop :=
  ∀ (K : Type) [CommRing K] [DecidableEq K] (f : Poly K) (D : Nat),
    f.DegLt D ↔ f.size ≤ D

/-- **Root bound**: a nonzero polynomial of degree `< D` has at most `D − 1`
roots among any distinct points. -/
def CardRootsLeStmt : Prop :=
  ∀ (K : Type) [Field K] (f : Poly K) (D : Nat) (xs : List K),
    ¬ f.IsZero → f.DegLt D → xs.Nodup → count xs (fun x => f.eval x = 0) + 1 ≤ D

/-- Vanishing on `D` distinct points forces a degree-`< D` polynomial to be zero. -/
def EqZeroOfRootsStmt : Prop :=
  ∀ (K : Type) [Field K] (f : Poly K) (D : Nat) (xs : List K),
    f.DegLt D → xs.Nodup → D ≤ xs.length → (∀ x ∈ xs, f.eval x = 0) → f.IsZero

/-- A zero polynomial evaluates to zero. -/
def IsZeroEvalStmt : Prop :=
  ∀ (K : Type) [CommRing K] (f : Poly K) (x : K), f.IsZero → f.eval x = 0

/-- **Lagrange interpolation** through distinct points. -/
def LagrangeStmt : Prop :=
  ∀ (K : Type) [Field K] [DecidableEq K] (xs : List K) (v : K → K),
    (Poly.lagrange xs v).DegLt xs.length ∧
    (xs.Nodup → ∀ x ∈ xs, (Poly.lagrange xs v).eval x = v x)

/-- Factor theorem for `quot`: `f(x) − f(r) = (x − r)·(quot f r)(x)`, degree drops. -/
def QuotStmt : Prop :=
  ∀ (K : Type) [CommRing K] (f : Poly K) (r x : K) (D : Nat),
    f.eval x - f.eval r = (x - r) * (f.quot r).eval x ∧
    (f.DegLt (D + 1) → (f.quot r).DegLt D)

/-! ## Reed–Solomon codes -/

/-- RS codes are linear. -/
def RSLinStmt : Prop :=
  ∀ (K : Type) [Field K] (n D : Nat) (pts : Nat → K) (u v : Nat → K) (a b : K),
    RS.Mem n D pts u → RS.Mem n D pts v → RS.Mem n D pts fun i => a * u i + b * v i

/-- **`RS.sep`**: distinct codewords differ in at least `n − D + 1` positions. -/
def RSSepStmt : Prop :=
  ∀ (K : Type) [Field K] [DecidableEq K] (n D : Nat) (pts : Nat → K), RS.PtsInj n pts →
    ∀ u v, RS.Mem n D pts u → RS.Mem n D pts v →
      LineLemma.dist n u v < n - D + 1 → ∀ i, i < n → u i = v i

/-! ## Challenge decoding -/

/-- **`decodeChal_count`**: a set of `≤ b` field elements is hit by at most
`b · 3^8` of the `2^256` oracle answers. -/
def DecodeChalCountStmt : Prop :=
  ∀ (B : Fp8 → Prop) (b : Nat), count Fp8.all B ≤ b →
    count (List.range roRange) (fun t => B (decodeChal (LazyRO.answer t))) ≤ b * 3 ^ 8

/-- The out-of-domain decoder has fibers of size `≤ 2·3^8`. -/
def DecodeOodCountStmt : Prop :=
  ∀ (B : Fp8 → Prop) (b : Nat), count Fp8.all B ≤ b →
    count (List.range roRange) (fun t => B (decodeOod (LazyRO.answer t))) ≤ b * (2 * 3 ^ 8)

end ZkFormal.Algebra
