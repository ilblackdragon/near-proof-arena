import ArenaCore.Bytes

/-!
# alt_bn128 (BN254) arithmetic and codec, as nearcore's three `alt_bn128_*` hosts consume it

Leaf module for the crypto-enabled successor domain (L3), fourth entry after `Secp256k1.lean`,
`P256.lean` and the two BLS12-381 modules. It transcribes the arithmetic and the wire codec of
`runtime/near-vm-runner/src/logic/alt_bn128.rs` (nearcore `44f7ae6c`, PV86) — which forwards every
byte of decoding and arithmetic to the `bn` crate (`zeropool-bn` 0.5.11, the version nearcore's
`Cargo.toml:165` pins) — so that the three `alt_bn128_*` hosts have a Lean semantics instead of the
blanket `out-of-domain` they get in `D3α`.

## Curve and tower

`E: y² = x³ + 3` over `Fq`,
`q = 21888242871839275222246405745257275088696311157297823662689037894645226208583` (254 bits);
the twist `E': y² = x³ + b'` over `Fq2 = Fq[i]/(i² + 1)` with `b' = 3/(9+i)`; scalar field order
`r = 21888242871839275222246405745257275088548364400416034343698204186575808495617`. `bn` names the
non-residue `BETA = q − 1 = −1` (`fq_non_residue`), so its `Fq2` is exactly `Fq[i]/(i² + 1)`:
real part first, `i² = −1`.

`Fq6 = Fq2[v]/(v³ − ξ)`, `Fq12 = Fq6[w]/(w² − v)`, `ξ = 9 + i`, matching
`zeropool-bn-0.5.11/src/fields/{fq2,fq6,fq12}.rs` and `src/groups/mod.rs:719-721` (`twist()`).

## Encoding (`logic/alt_bn128.rs:113-149`) — **little-endian**, unlike the EVM precompiles

| object | wire form | Rust |
|---|---|---|
| `Fq` / `Fr` | 32-byte **little-endian** `u256`; a value `≥ q` (resp. `≥ r`) is `invalid fq` / `invalid fr` | `decode_u256` = `u128::from_le_bytes(lo) ‖ u128::from_le_bytes(hi)` |
| G1 point | 64 B: `x ‖ y`, each 32 B LE; `(0, 0)` is the point at infinity | `decode_g1` |
| `Fq2` | 64 B: `real ‖ imaginary`, each 32 B LE — **real first** | `decode_fq2` |
| G2 point | 128 B: `x.real ‖ x.imag ‖ y.real ‖ y.imag`; `(0, 0)` is infinity | `decode_g2` |
| `bool` (sign) | 1 byte, must be `0x00` or `0x01` | `decode_bool` |
| output G1 | 64 B LE; infinity encodes as 64 zero bytes | `encode_g1` |
| verdict | `pairing_check` returns `1` iff the product is one | `pairing_batch(...) == Gt::one()` |

## The pairing

`bn` computes the **optimal ate** pairing (`groups/mod.rs:813-845` `miller_loop_batch` over
`ATE_LOOP_COUNT_NAF`, then `Fq12::final_exponentiation`). This module computes the **reduced Tate**
pairing `t(P,Q) = f_{r,P}(Q)^((q¹²−1)/r)` instead. That is legitimate for this host because the host
only asks whether `∏ e(g1ᵢ, g2ᵢ) = 1`: any two non-degenerate bilinear pairings into `μ_r` differ by
a single exponent `c` coprime to `r` (both are bilinear forms on `G1 × G2 ≅ (ℤ/r)²` and `μ_r` is
cyclic of prime order), so `∏ t = 1 ⟺ ∏ e = 1`. Agreement on every vector is *tested* against the
pinned oracle, not proved.

## Status

Proved here (axiom-free: only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`):

* the `Fq` operation laws — `add_mod`, `mul_mod`, `sub_mod`, `neg_mod` — and canonicity
  (`add_lt` … `neg_lt`), plus the `Nat`→`Int` bridges `cast_add`, `cast_mul`, `cast_sub`;
* **curve membership is preserved by the group law**, as four polynomial identities over `Int`:
  * `dbl_defect_int` — Jacobian doubling: the output defect is `64·Y⁶` times the input defect;
  * `dbl_membership_int` — affine doubling, given the slope relation `2yλ = 3x²`;
  * `add_membership_scaled` — affine addition in denominator-free form (`(x₂−x₁)²` times the
    output defect is `0`), given `λ(x₂−x₁) = y₂−y₁`;
  * `add_defect_int` — Jacobian addition: the output defect is an explicit combination of the two
    input defects, so an on-curve pair yields an on-curve output;
* `productIsOne_nil` — the empty pairing product is one, so the empty `pairing_check` input is the
  `1` verdict.

The residual premise of the two affine statements is exactly "`λ` is the chord/tangent slope", which
is what `g1Slope` computes through `Fq.inv`; a statement mentioning the divided quantity directly
would need an inverse witness, so the scaled form is used instead. Nothing here asserts that the
group law is the chord–tangent *group* operation, that `q` is prime, or that the reduced Tate
pairing agrees with `bn`'s optimal ate pairing — those are tested, not proved.

Tested, not proved: agreement with `zeropool-bn` 0.5.11 on 56 directed rows (including all 19
vectors of nearcore's own `logic/tests/alt_bn128.rs`, whose asserted verdicts the oracle is first
checked against) and 3,120 generated rows across four seeds; plus 47 host-arm cases for gas, charge
order, argument order, register behaviour and error text. See
`docs/logs/lean-chunk-L3-bn128-2026-10-23.md`.
-/

namespace NearSpecV3
namespace AltBn128

open ArenaCore

/-! ## `Fq` — the base field -/

/-- The alt_bn128 base-field modulus (`zeropool-bn-0.5.11/src/fields/fp.rs:225-232`). -/
def q : Nat :=
  21888242871839275222246405745257275088696311157297823662689037894645226208583

/-- The scalar field / G1 group order `r` (`zeropool-bn-0.5.11/src/fields/fp.rs:196-203`). -/
def r : Nat :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

/-- `bn`'s `fq_non_residue`: `BETA = q − 1 = −1`, so `Fq2 = Fq[i]/(i² − BETA) = Fq[i]/(i² + 1)`. -/
def beta : Nat := q - 1

namespace Fq

def add (a b : Nat) : Nat := (a + b) % q

/-- `(a + q − b % q) % q`. Because `b % q < q`, the `Nat` subtraction never truncates, so this casts
to `Int` as plain subtraction — which is what the curve identities need. -/
def sub (a b : Nat) : Nat := (a + q - b % q) % q

def mul (a b : Nat) : Nat := (a * b) % q
def neg (a : Nat) : Nat := (q - a % q) % q

/-- Square-and-multiply, structurally recursive on the exponent `f`, so the kernel can reduce
concrete instances: `powAux f b e = b^(e mod 2^f) mod q`. -/
def powAux : Nat → Nat → Nat → Nat
  | 0, _, _ => 1
  | f + 1, b, e =>
    let h := powAux f b (e / 2)
    if e % 2 = 1 then mul (mul h h) b else mul h h

/-- `b ^ e mod q`. Every `Fq` value is already reduced, so `b < q`. -/
def pow (b e : Nat) : Nat := powAux 300 b e

/-- `a⁻¹ = a^(q−2) mod q` (Fermat). `0⁻¹` is `0`; callers that need "no inverse" use `inv?`. -/
def inv (a : Nat) : Nat := pow a (q - 2)

/-- `Option`-valued inverse (`FieldElement::inverse` returns `Option<Self>`). -/
def inv? (a : Nat) : Option Nat := if a % q = 0 then none else some (inv a)

/-! ### Field-operation laws

Each `Nat`-modulo result casts to `Int` as the corresponding plain `Int` operation modulo `q`. The
`cast_*` lemmas below are the plumbing the curve-membership proofs use; each is one `simp`/`omega`. -/

theorem add_mod (a b : Nat) : Fq.add a b % q = (a + b) % q := by simp [add]
theorem mul_mod (a b : Nat) : Fq.mul a b % q = (a * b) % q := by simp [mul]
theorem sub_mod (a b : Nat) : Fq.sub a b % q = (a + q - b % q) % q := by simp [sub]
theorem neg_mod (a : Nat) : Fq.neg a % q = (q - a % q) % q := by simp [neg]

/-- `Fq` values are canonical: every operation returns a value `< q`. -/
theorem add_lt (a b : Nat) : Fq.add a b < q := Nat.mod_lt _ (by decide)
theorem mul_lt (a b : Nat) : Fq.mul a b < q := Nat.mod_lt _ (by decide)
theorem sub_lt (a b : Nat) : Fq.sub a b < q := Nat.mod_lt _ (by decide)
theorem neg_lt (a : Nat) : Fq.neg a < q := Nat.mod_lt _ (by decide)

/-- `0 < q`, so `%` is the canonical representative. -/
theorem q_pos : 0 < q := by decide

theorem cast_add (a b : Nat) :
    ((Fq.add a b : Nat) : Int) % (q:Int) = ((a:Int) + (b:Int)) % (q:Int) := by
  simp [add, q]

theorem cast_mul (a b : Nat) :
    ((Fq.mul a b : Nat) : Int) % (q:Int) = ((a:Int) * (b:Int)) % (q:Int) := by
  simp [mul, q]

/-- `Nat` truncating subtraction is the only place the bridge is not definitional; since
`b % q < q ≤ a + q`, the subtraction never truncates and `omega` closes it. -/
theorem cast_sub (a b : Nat) :
    ((Fq.sub a b : Nat) : Int) % (q:Int) = ((a:Int) - (b:Int)) % (q:Int) := by
  simp only [sub, q]
  omega

end Fq

/-! ## G1: `E(Fq): y² = x³ + 3`, in Jacobian coordinates -/

/-- A G1 point in Jacobian coordinates; `Z = 0` is the point at infinity. The affine point is
`(X/Z², Y/Z³)`, so the curve equation is `Y² = X³ + 3·Z⁶`. -/
structure G1 where
  X : Nat
  Y : Nat
  Z : Nat
  deriving DecidableEq, Repr

namespace G1

/-- The point at infinity (`G::zero()`: `x = 0`, `y = 1`, `z = 0`). -/
def inf : G1 := ⟨0, 1, 0⟩

/-- Affine point with `Z = 1`. -/
def ofAffine (x y : Nat) : G1 := ⟨x % q, y % q, 1⟩

def isInf (P : G1) : Bool := P.Z = 0

/-- The affine "infinity" encoding test the codec uses: both coordinates zero
(`decode_g1`'s `x.is_zero() && y.is_zero()` branch, `logic/alt_bn128.rs:117`). -/
def affIsInf (x y : Nat) : Bool := x % q = 0 ∧ y % q = 0

/-- `y² = x³ + 3` on affine coordinates (`AffineG1::new`, `groups/mod.rs:215`). -/
def onCurve (x y : Nat) : Bool := Fq.mul y y == Fq.add (Fq.mul (Fq.mul x x) x) 3

/-- `bn`'s `GroupElement::double` for `a = 0` (`groups/mod.rs:378-404`): `A = X²`, `B = Y²`,
`C = B²`, `D = 2((X+B)² − A − C)`, `E = 3A`, `F = E²`, `X₃ = F − 2D`, `Y₃ = E(D − X₃) − 8C`,
`Z₃ = 2YZ`. -/
def dbl (P : G1) : G1 :=
  if P.Z = 0 ∨ P.Y = 0 then inf else
  let A := Fq.mul P.X P.X
  let B := Fq.mul P.Y P.Y
  let C := Fq.mul B B
  let D := Fq.mul 2 (Fq.sub (Fq.sub (Fq.mul (Fq.add P.X B) (Fq.add P.X B)) A) C)
  let E := Fq.mul 3 A
  let F := Fq.mul E E
  let X3 := Fq.sub F (Fq.mul 2 D)
  let Y3 := Fq.sub (Fq.mul E (Fq.sub D X3)) (Fq.mul 8 C)
  let Z3 := Fq.mul 2 (Fq.mul P.Y P.Z)
  ⟨X3, Y3, Z3⟩

/-- `add-2007-bl` (Jacobian + Jacobian, `a = 0`), `groups/mod.rs:493-540`. -/
def add (P Q : G1) : G1 :=
  if P.Z = 0 then Q else if Q.Z = 0 then P else
  let Z1Z1 := Fq.mul P.Z P.Z
  let Z2Z2 := Fq.mul Q.Z Q.Z
  let U1 := Fq.mul P.X Z2Z2
  let U2 := Fq.mul Q.X Z1Z1
  let S1 := Fq.mul (Fq.mul P.Y Q.Z) Z2Z2
  let S2 := Fq.mul (Fq.mul Q.Y P.Z) Z1Z1
  if U1 = U2 then (if S1 = S2 then dbl P else inf)
  else
    let H := Fq.sub U2 U1
    let I := Fq.mul (Fq.mul 2 H) (Fq.mul 2 H)
    let J := Fq.mul H I
    let r := Fq.mul 2 (Fq.sub S2 S1)
    let V := Fq.mul U1 I
    let X3 := Fq.sub (Fq.sub (Fq.mul r r) J) (Fq.mul 2 V)
    let Y3 := Fq.sub (Fq.mul r (Fq.sub V X3)) (Fq.mul 2 (Fq.mul S1 J))
    let Z3 := Fq.mul (Fq.sub (Fq.sub (Fq.mul (Fq.add P.Z Q.Z) (Fq.add P.Z Q.Z)) Z1Z1) Z2Z2) H
    ⟨X3, Y3, Z3⟩

/-- Negation: `(X, Y, Z) ↦ (X, −Y, Z)`; infinity is its own negative. -/
def neg (P : G1) : G1 := if P.Z = 0 then P else ⟨P.X, Fq.neg P.Y, P.Z⟩

/-- MSB-first double-and-add over 256 bits, matching `bn`'s `BitIterator`/`found_one` loop
(`arith.rs:377-399` + `groups/mod.rs:400-420`): leading zero bits are skipped, and the first set bit
initialises the accumulator. -/
def smulAux : Nat → Nat → G1 → G1
  | 0, _, _ => inf
  | f + 1, k, P =>
    let Q := smulAux f (k / 2) P
    let Q2 := dbl Q
    if k % 2 = 1 then add Q2 P else Q2

/-- `k • P` for a 256-bit scalar. -/
def smul (k : Nat) (P : G1) : G1 := smulAux 256 k P

/-- Affine coordinates of a finite point (`none` for infinity), via `Z⁻¹`
(`G::to_affine`, `groups/mod.rs:318-335`). -/
def affine? (P : G1) : Option (Nat × Nat) :=
  if P.Z = 0 then none
  else
    let zi := Fq.inv P.Z
    let zi2 := Fq.mul zi zi
    some (Fq.mul P.X zi2, Fq.mul (Fq.mul P.Y zi2) zi)

/-- `bn`'s `subgroup_check` for G1 is the constant `true` (`groups/mod.rs:576-578`): `#E(Fq) = r`,
so on-curve already implies in-subgroup, and the only `AffineG1::new` gates are "on curve" and "not
the infinity encoding", both in the codec. -/
def subgroupCheck (_P : G1) : Bool := true

end G1

/-! ### Curve membership is preserved by the group law

These are the chord–tangent identities. Each is one polynomial identity over `Int`, discharged by
`grind`; nothing here depends on `q` being prime, and no inverse is mentioned (the slope `λ` is a
free variable with the relation the executable code establishes through `Fq.inv`, so the residual
premise is exactly "λ is the slope"). -/

/-- **Jacobian doubling preserves the curve**, unconditionally: the output's defect
`Y₃² − (X₃³ + 3Z₃⁶)` is `64·Y⁶` times the input's defect. -/
theorem dbl_defect_int (X Y Z : Int) :
    (let A := X*X
     let B := Y*Y
     let C := B*B
     let D := 2*((X+B)*(X+B) - A - C)
     let E := 3*A
     let F := E*E
     let X3 := F - 2*D
     let Y3 := E*(D - X3) - 8*C
     let Z3 := 2*Y*Z
     Y3*Y3 - (X3*X3*X3 + 3*Z3^6)) = 64*(Y^6)*(Y*Y - (X*X*X + 3*Z^6)) := by
  dsimp only
  grind (splits := 100) (ringSteps := 1000000)

/-- **Affine doubling preserves the curve**: if `y² = x³ + 3` and `2yλ = 3x²`, the chord–tangent
output satisfies the curve equation. -/
theorem dbl_membership_int (x y lam : Int)
    (h : y*y = x*x*x + 3) (hl : 2*y*lam = 3*x*x) :
    (let x3 := lam*lam - 2*x
     let y3 := lam*(x - x3) - y
     y3*y3 = x3*x3*x3 + 3) := by
  dsimp only
  grind (splits := 100) (ringSteps := 1000000)

/-- **Affine addition preserves the curve**, in the denominator-free form: multiplying the output
defect by `(x₂−x₁)²` clears the division that `λ(x₂−x₁) = y₂−y₁` encodes. Since the curve
coordinates come from a field, `(x₂−x₁)² ≠ 0` for distinct inputs, so this is exactly the usual
statement, with no inverse hypothesis. -/
theorem add_membership_scaled (x1 y1 x2 y2 lam : Int)
    (h1 : y1*y1 = x1*x1*x1 + 3) (h2 : y2*y2 = x2*x2*x2 + 3)
    (hl : lam*(x2-x1) = y2-y1) :
    (let x3 := lam*lam - x1 - x2
     let y3 := lam*(x1 - x3) - y1
     (x2-x1)*(x2-x1)*(y3*y3 - (x3*x3*x3 + 3)) = 0) := by
  dsimp only
  grind (splits := 100) (ringSteps := 2000000)

/-- **Jacobian addition preserves the curve**, unconditionally: the output defect is an explicit
combination of the two input defects, so an on-curve pair yields an on-curve output. -/
theorem add_defect_int (X1 Y1 Z1 X2 Y2 Z2 : Int) :
    (let Z1Z1 := Z1*Z1
     let Z2Z2 := Z2*Z2
     let U1 := X1*Z2Z2
     let U2 := X2*Z1Z1
     let S1 := Y1*Z2*Z2Z2
     let S2 := Y2*Z1*Z1Z1
     let H := U2 - U1
     let I := (2*H)*(2*H)
     let J := H*I
     let r := 2*(S2 - S1)
     let V := U1*I
     let X3 := r*r - J - 2*V
     let Y3 := r*(V - X3) - 2*(S1*J)
     let Z3 := ((Z1+Z2)*(Z1+Z2) - Z1Z1 - Z2Z2)*H
     (Y3*Y3 - (X3*X3*X3 + 3*Z3^6))
       = (Y1*Y1 - (X1*X1*X1 + 3*Z1^6)) * (-64*Z2^6*(X1*Z2^2 - X2*Z1^2)^3*
            (X1^3*Z2^6 - 3*X1*X2^2*Z1^4*Z2^2 + X2^3*Z1^6 - Y1^2*Z2^6
              + 2*Y1*Y2*Z1^3*Z2^3 - 3*Z1^6*Z2^6))
         + (Y2*Y2 - (X2*X2*X2 + 3*Z2^6)) * (64*Z1^6*(X1*Z2^2 - X2*Z1^2)^3*
            (X1^3*Z2^6 - 3*X1^2*X2*Z1^2*Z2^4 + X2^3*Z1^6 + 2*Y1*Y2*Z1^3*Z2^3
              - Y2^2*Z1^6 - 3*Z1^6*Z2^6))) := by
  dsimp only
  grind (splits := 200) (ringSteps := 4000000)

/-! ## `Fq2 = Fq[i]/(i² + 1)` -/

/-- An `Fq2` element `c0 + c1·i`, both components kept canonical. -/
structure Fq2 where
  c0 : Nat
  c1 : Nat
  deriving DecidableEq, Repr

namespace Fq2

def zero : Fq2 := ⟨0, 0⟩
def one : Fq2 := ⟨1, 0⟩

def add (a b : Fq2) : Fq2 := ⟨Fq.add a.c0 b.c0, Fq.add a.c1 b.c1⟩
def sub (a b : Fq2) : Fq2 := ⟨Fq.sub a.c0 b.c0, Fq.sub a.c1 b.c1⟩
def neg (a : Fq2) : Fq2 := ⟨Fq.neg a.c0, Fq.neg a.c1⟩

/-- `(a0 + a1 i)(b0 + b1 i) = (a0b0 − a1b1) + (a0b1 + a1b0) i`, `i² = −1`
(`fq2.rs:138-154`). -/
def mul (a b : Fq2) : Fq2 :=
  ⟨Fq.sub (Fq.mul a.c0 b.c0) (Fq.mul a.c1 b.c1),
   Fq.add (Fq.mul a.c0 b.c1) (Fq.mul a.c1 b.c0)⟩

def sqr (a : Fq2) : Fq2 := mul a a
def dbl (a : Fq2) : Fq2 := ⟨Fq.add a.c0 a.c0, Fq.add a.c1 a.c1⟩
def triple (a : Fq2) : Fq2 := ⟨Fq.add (Fq.add a.c0 a.c0) a.c0, Fq.add (Fq.add a.c1 a.c1) a.c1⟩

def isZero (a : Fq2) : Bool := a.c0 = 0 ∧ a.c1 = 0

/-- Norm `N(a) = a0² + a1² = a·ā`; `a⁻¹ = ā / N(a)` (`fq2.rs:126-136`, Algorithm 8). -/
def inv (a : Fq2) : Option Fq2 :=
  let n := Fq.add (Fq.mul a.c0 a.c0) (Fq.mul a.c1 a.c1)
  if n = 0 then none
  else
    let ni := Fq.inv n
    some ⟨Fq.mul a.c0 ni, Fq.neg (Fq.mul a.c1 ni)⟩

/-- `a^n` by square-and-multiply, structural in the fuel so the kernel can reduce it. -/
def powAux : Nat → Fq2 → Nat → Fq2
  | 0, _, _ => one
  | f + 1, b, e =>
    let h := powAux f b (e / 2)
    if e % 2 = 1 then mul (mul h h) b else mul h h

def pow (b : Fq2) (e : Nat) : Fq2 := powAux 300 b e

/-- Conjugation `ā = c0 − c1·i`. -/
def conj (a : Fq2) : Fq2 := ⟨a.c0, Fq.neg a.c1⟩

end Fq2

/-! ## `Fq6 = Fq2[v]/(v³ − ξ)`, `ξ = 9 + i` -/

/-- The cubic non-residue `ξ = 9 + i` (`fq2_nonresidue`, `zeropool-bn/src/fields/fq2.rs:22-36`;
`groups/mod.rs:719-721` `twist()`). -/
def xi : Fq2 := ⟨9, 1⟩

/-- An `Fq6` element `c0 + c1·v + c2·v²`. -/
structure Fq6 where
  c0 : Fq2
  c1 : Fq2
  c2 : Fq2
  deriving DecidableEq, Repr

namespace Fq6

def zero : Fq6 := ⟨Fq2.zero, Fq2.zero, Fq2.zero⟩
def one : Fq6 := ⟨Fq2.one, Fq2.zero, Fq2.zero⟩

def add (a b : Fq6) : Fq6 :=
  ⟨Fq2.add a.c0 b.c0, Fq2.add a.c1 b.c1, Fq2.add a.c2 b.c2⟩
def sub (a b : Fq6) : Fq6 :=
  ⟨Fq2.sub a.c0 b.c0, Fq2.sub a.c1 b.c1, Fq2.sub a.c2 b.c2⟩
def neg (a : Fq6) : Fq6 := ⟨Fq2.neg a.c0, Fq2.neg a.c1, Fq2.neg a.c2⟩

/-- Multiplication by `ξ`: `a + bv + cv² ↦ c·ξ + av + bv²` (`v³ = ξ`), matching
`Fq6::mul_by_nonresidue` (`fq6.rs:113-119`) with `Fq2::mul_by_nonresidue` (`fq2.rs:59-61`). -/
def mulByXi (a : Fq6) : Fq6 := ⟨Fq2.mul a.c2 xi, a.c0, a.c1⟩

/-- `Fq2`-scalar multiplication by `ξ`, the `Fq2::mul_by_nonresidue` of `fq2.rs:59-61`. -/
def mulXi (a : Fq2) : Fq2 := Fq2.mul a xi

/-- Karatsuba multiplication (`fq6.rs:200-211`): with `ξ = 9+i` and `v³ = ξ`,
`c0 = a0b0 + ξ(a1b2 + a2b1)`, `c1 = a0b1 + a1b0 + ξ·a2b2`, `c2 = a0b2 + a1b1 + a2b0`. -/
def mul (a b : Fq6) : Fq6 :=
  let ac0 := Fq2.mul a.c0 b.c0
  let ac2 := Fq2.mul a.c2 b.c2
  let c0 := Fq2.add ac0 (mulXi (Fq2.add (Fq2.mul a.c1 b.c2) (Fq2.mul a.c2 b.c1)))
  let c1 := Fq2.add (Fq2.add (Fq2.mul a.c0 b.c1) (Fq2.mul a.c1 b.c0)) (mulXi ac2)
  let c2 := Fq2.add (Fq2.add (Fq2.mul a.c0 b.c2) (Fq2.mul a.c1 b.c1)) (Fq2.mul a.c2 b.c0)
  ⟨c0, c1, c2⟩

def sqr (a : Fq6) : Fq6 := mul a a

/-- Inverse (`fq6.rs:183-196`): the adjugate divided by the norm
`a0³ + ξ·a1³ + ξ²·a2³ − 3ξ·a0a1a2`. -/
def inv (a : Fq6) : Option Fq6 :=
  let t0 := Fq2.sub (Fq2.mul a.c0 a.c0) (mulXi (Fq2.mul a.c1 a.c2))
  let t1 := Fq2.sub (mulXi (Fq2.mul a.c2 a.c2)) (Fq2.mul a.c0 a.c1)
  let t2 := Fq2.sub (Fq2.mul a.c1 a.c1) (Fq2.mul a.c0 a.c2)
  let d := Fq2.add (Fq2.mul a.c0 t0)
    (mulXi (Fq2.add (Fq2.mul a.c2 t1) (Fq2.mul a.c1 t2)))
  match Fq2.inv d with
  | none => none
  | some di => some ⟨Fq2.mul t0 di, Fq2.mul t1 di, Fq2.mul t2 di⟩

def isZero (a : Fq6) : Bool :=
  Fq2.isZero a.c0 ∧ Fq2.isZero a.c1 ∧ Fq2.isZero a.c2

end Fq6

/-! ## `Fq12 = Fq6[w]/(w² − v)` -/

/-- An `Fq12` element `c0 + c1·w`. -/
structure Fq12 where
  c0 : Fq6
  c1 : Fq6
  deriving DecidableEq, Repr

namespace Fq12

def zero : Fq12 := ⟨Fq6.zero, Fq6.zero⟩
def one : Fq12 := ⟨Fq6.one, Fq6.zero⟩

def add (a b : Fq12) : Fq12 := ⟨Fq6.add a.c0 b.c0, Fq6.add a.c1 b.c1⟩
def sub (a b : Fq12) : Fq12 := ⟨Fq6.sub a.c0 b.c0, Fq6.sub a.c1 b.c1⟩
def neg (a : Fq12) : Fq12 := ⟨Fq6.neg a.c0, Fq6.neg a.c1⟩

/-- `(a + bw)(c + dw) = (ac + v·bd) + (ad + bc)w`, `w² = v` (`fq12.rs:322-333`). -/
def mul (a b : Fq12) : Fq12 :=
  let ac := Fq6.mul a.c0 b.c0
  let bd := Fq6.mul a.c1 b.c1
  let ad := Fq6.mul a.c0 b.c1
  let bc := Fq6.mul a.c1 b.c0
  ⟨Fq6.add ac (Fq6.mulByXi bd), Fq6.add ad bc⟩

def sqr (a : Fq12) : Fq12 := mul a a

/-- Inverse (`fq12.rs:311-320`): `(a + bw)⁻¹ = (a − bw)/(a² − v·b²)`. -/
def inv (a : Fq12) : Option Fq12 :=
  let d := Fq6.sub (Fq6.mul a.c0 a.c0) (Fq6.mulByXi (Fq6.mul a.c1 a.c1))
  match Fq6.inv d with
  | none => none
  | some di => some ⟨Fq6.mul a.c0 di, Fq6.neg (Fq6.mul a.c1 di)⟩

/-- `a^n` by square-and-multiply, structural in the fuel so the kernel can reduce concrete
instances. -/
def powAux : Nat → Fq12 → Nat → Fq12
  | 0, _, _ => one
  | f + 1, b, e =>
    let h := powAux f b (e / 2)
    if e % 2 = 1 then mul (mul h h) b else mul h h

def pow (b : Fq12) (e : Nat) : Fq12 := powAux 3200 b e

def isOne (a : Fq12) : Bool := a = one

/-- Conjugation `a ↦ ā = c0 − c1·w` (`fq12.rs:131-133`). -/
def conj (a : Fq12) : Fq12 := ⟨a.c0, Fq6.neg a.c1⟩

end Fq12

/-! ## `Fq12` embeddings

The twist map `Ψ(x, y) = (x·w², y·w³) = (x·v, y·v·w)` sends `E'(Fq2)` into `E(Fq12)`; with
`Fq12 = Fq6[w]/(w²−v)` and `Fq6 = Fq2[v]/(v³−ξ)` the images are `x·v = (0, x, 0)` in `Fq6` and
`y·v·w = ((0, y, 0))·w`. -/

/-- Embed a scalar `a ∈ Fq` into `Fq12`. -/
def embedFq (a : Nat) : Fq12 := ⟨⟨⟨a % q, 0⟩, Fq2.zero, Fq2.zero⟩, Fq6.zero⟩

/-- The twist image of a finite G2 point: `(x·v, y·v·w)`. -/
def embedG2 (P : Fq2 × Fq2) : Fq12 × Fq12 :=
  let x : Fq2 := P.1
  let y : Fq2 := P.2
  let xv : Fq6 := ⟨Fq2.zero, x, Fq2.zero⟩
  let yv : Fq6 := ⟨Fq2.zero, y, Fq2.zero⟩
  ((⟨xv, Fq6.zero⟩ : Fq12), (⟨Fq6.zero, yv⟩ : Fq12))

/-! ## G2: the twist `E'(Fq2): y² = x³ + b'` -/

/-- `b' = 3/(9+i)`, `zeropool-bn/src/groups/mod.rs:655-671` `G2Params::coeff_b` (de-Montgomeryised;
checked exactly in the lane log). -/
def bTwist : Fq2 :=
  ⟨19485874751759354771024239261021720505790618469301721065564631296452457478373,
   266929791119991161246907387137283842545076965332900288569378510910307636690⟩

/-- A G2 point in Jacobian coordinates over `Fq2`; `Z = 0` is infinity. -/
structure G2 where
  X : Fq2
  Y : Fq2
  Z : Fq2
  deriving DecidableEq, Repr

namespace G2

def inf : G2 := ⟨Fq2.zero, Fq2.one, Fq2.zero⟩

def ofAffine (x y : Fq2) : G2 := ⟨x, y, Fq2.one⟩

def isInf (P : G2) : Bool := P.Z = Fq2.zero

def affIsInf (x y : Fq2) : Bool := x = Fq2.zero ∧ y = Fq2.zero

/-- `y² = x³ + b'` on affine coordinates over `Fq2`. -/
def onCurve (x y : Fq2) : Bool := Fq2.sqr y == Fq2.add (Fq2.mul (Fq2.sqr x) x) bTwist

/-- Doubling over `Fq2`, the same `dbl-2009-l` shape as G1 with `3` replaced by `b'` in the
`Z`-only term (which vanishes at `Z = 1`). -/
def dbl (P : G2) : G2 :=
  if P.Z = Fq2.zero ∨ P.Y = Fq2.zero then inf else
  let A := Fq2.sqr P.X
  let B := Fq2.sqr P.Y
  let C := Fq2.sqr B
  let D := Fq2.dbl (Fq2.sub (Fq2.sub (Fq2.sqr (Fq2.add P.X B)) A) C)
  let E := Fq2.triple A
  let F := Fq2.sqr E
  let X3 := Fq2.sub F (Fq2.dbl D)
  let Y3 := Fq2.sub (Fq2.mul E (Fq2.sub D X3)) (Fq2.mul ⟨8, 0⟩ C)
  let Z3 := Fq2.dbl (Fq2.mul P.Y P.Z)
  ⟨X3, Y3, Z3⟩

/-- Addition over `Fq2` (the generic `add-2007-bl`; `a = 0` for the twist). -/
def add (P Q : G2) : G2 :=
  if P.Z = Fq2.zero then Q else if Q.Z = Fq2.zero then P else
  let Z1Z1 := Fq2.sqr P.Z
  let Z2Z2 := Fq2.sqr Q.Z
  let U1 := Fq2.mul P.X Z2Z2
  let U2 := Fq2.mul Q.X Z1Z1
  let S1 := Fq2.mul (Fq2.mul P.Y Q.Z) Z2Z2
  let S2 := Fq2.mul (Fq2.mul Q.Y P.Z) Z1Z1
  if U1 = U2 then (if S1 = S2 then dbl P else inf)
  else
    let H := Fq2.sub U2 U1
    let I := Fq2.sqr (Fq2.dbl H)
    let J := Fq2.mul H I
    let rr := Fq2.dbl (Fq2.sub S2 S1)
    let V := Fq2.mul U1 I
    let X3 := Fq2.sub (Fq2.sub (Fq2.sqr rr) J) (Fq2.dbl V)
    let Y3 := Fq2.sub (Fq2.mul rr (Fq2.sub V X3)) (Fq2.dbl (Fq2.mul S1 J))
    let Z3 := Fq2.mul (Fq2.sub (Fq2.sub (Fq2.sqr (Fq2.add P.Z Q.Z)) Z1Z1) Z2Z2) H
    ⟨X3, Y3, Z3⟩

def neg (P : G2) : G2 := if P.Z = Fq2.zero then P else ⟨P.X, Fq2.neg P.Y, P.Z⟩

def smulAux : Nat → Nat → G2 → G2
  | 0, _, _ => inf
  | f + 1, k, P =>
    let Q := smulAux f (k / 2) P
    let Q2 := dbl Q
    if k % 2 = 1 then add Q2 P else Q2

def smul (k : Nat) (P : G2) : G2 := smulAux 256 k P

def affine? (P : G2) : Option (Fq2 × Fq2) :=
  if P.Z = Fq2.zero then none
  else
    match Fq2.inv P.Z with
    | none => none
    | some zi =>
      let zi2 := Fq2.sqr zi
      some (Fq2.mul P.X zi2, Fq2.mul (Fq2.mul P.Y zi2) zi)

/-- `bn`'s G2 subgroup check (`groups/mod.rs:120-122`, `check_order() = true` at `:672-674`):
`[r]P = O`. `#E'(Fq2) = r · h₂` with `h₂ ≠ 1`, so this is a real gate. -/
def inSubgroup (P : G2) : Bool := isInf (smul r P)

end G2

/-! ## The Miller loop and the reduced Tate pairing

`f_{r,P}(Q)` for `P ∈ G1` affine and `Q` the twist image of a G2 point, then the final
exponentiation by `(q¹²−1)/r`. The loop is the textbook MSB-first Miller recursion over the bits of
`r` (*not* `bn`'s NAF ate loop): a vertical line whose divisor is zero contributes the factor `1`,
which is what the `none` branches below are.

The line `l(x,y) = y − y_T − λ(x − x_T)` and the vertical `v(x) = x − x_{2T}` are evaluated at
`Q ∈ Fq12`; `λ` is an `Fq` element embedded into `Fq12`. A division by `v` is a multiplication by
`Fq12.inv v` — the honest Miller recursion, not a denominator-eliminated variant, so the definition
is a literal transcription rather than an optimisation. -/

/-- Slope of the line through `T` and `P` (or the tangent at `T` when they coincide); `none` when
the line is vertical, i.e. `T + P = O`. -/
def g1Slope (T P : Nat × Nat) : Option Nat :=
  if T.1 = P.1 then
    (if Fq.add T.2 P.2 = 0 then none
     else some (Fq.mul (Fq.mul 3 (Fq.mul T.1 T.1)) (Fq.inv (Fq.add T.2 T.2))))
  else some (Fq.mul (Fq.sub P.2 T.2) (Fq.inv (Fq.sub P.1 T.1)))

/-- Affine G1 doubling with the same formulas `bn` uses, in affine form. `none` is infinity. -/
def g1Dbl (T : Nat × Nat) : Option (Nat × Nat) :=
  if T.2 = 0 then none
  else
    match g1Slope T T with
    | none => none
    | some lam =>
      let x3 := Fq.sub (Fq.mul lam lam) (Fq.add T.1 T.1)
      let y3 := Fq.sub (Fq.mul lam (Fq.sub T.1 x3)) T.2
      some (x3, y3)

/-- Affine G1 addition; `none` is infinity. -/
def g1AddA (T S : Nat × Nat) : Option (Nat × Nat) :=
  if T.1 = S.1 ∧ Fq.add T.2 S.2 = 0 then none
  else if T = S then g1Dbl T
  else
    match g1Slope T S with
    | none => none
    | some lam =>
      let x3 := Fq.sub (Fq.sub (Fq.mul lam lam) T.1) S.1
      let y3 := Fq.sub (Fq.mul lam (Fq.sub T.1 x3)) T.2
      some (x3, y3)

/-- `f_{r,P}(Q)`: the Miller function of `P` evaluated at the `Fq12` point `Q = (qx, qy)`.
`T` tracks `[k]P`; a `none` accumulator step is the "line at infinity" factor `1`. -/
def millerStep (P : Nat × Nat) (qx qy : Fq12) (i : Nat) (T : Option (Nat × Nat))
    (acc : Fq12) : Option (Nat × Nat) × Fq12 :=
  -- (1) doubling: `acc ← acc² · l_{T,T}(Q) / v_{2T}(Q)`, and `T ← 2T`
  let (Td, acc1) :=
    match T with
    | none => (none, Fq12.sqr acc)
    | some T' =>
      match g1Slope T' T' with
      | none => (none, Fq12.mul (Fq12.sqr acc) (Fq12.sub qx (embedFq T'.1)))
      | some lam =>
        let l := Fq12.sub (Fq12.sub qy (embedFq T'.2))
          (Fq12.mul (embedFq lam) (Fq12.sub qx (embedFq T'.1)))
        let accSq := Fq12.mul (Fq12.sqr acc) l
        match g1Dbl T' with
        | none => (none, accSq)
        | some T2 =>
          match Fq12.inv (Fq12.sub qx (embedFq T2.1)) with
          | none => (some T2, accSq)
          | some vi => (some T2, Fq12.mul accSq vi)
  -- (2) the mixed addition, only when bit `i` of `r` is set; it advances the *doubled* `T`
  if (r / 2 ^ i) % 2 = 0 then (Td, acc1) else
  match Td with
  | none => (some P, Fq12.mul acc1 (Fq12.sub qy (embedFq P.2)))
  | some T' =>
    if T'.1 = P.1 ∧ Fq.add T'.2 P.2 = 0 then
      -- the addition is vertical: the line is `v_T` and the sum is infinity
      (none, Fq12.mul acc1 (Fq12.sub qx (embedFq T'.1)))
    else
      match g1Slope T' P with
      | none => (none, Fq12.mul acc1 (Fq12.sub qx (embedFq T'.1)))
      | some lam =>
        let l := Fq12.sub (Fq12.sub qy (embedFq T'.2))
          (Fq12.mul (embedFq lam) (Fq12.sub qx (embedFq T'.1)))
        let accL := Fq12.mul acc1 l
        match g1AddA T' P with
        | none => (none, accL)
        | some Tn =>
          match Fq12.inv (Fq12.sub qx (embedFq Tn.1)) with
          | none => (some Tn, accL)
          | some vi => (some Tn, Fq12.mul accL vi)

/-- Walk bit indices `i, i-1, …, 0` of `r`, carrying `T = [k]P` and the Miller accumulator.
Structural in `i`, so the kernel can reduce a concrete instance. -/
def millerAux (P : Nat × Nat) (qx qy : Fq12) : Nat → Option (Nat × Nat) → Fq12 → Fq12
  | 0, T, acc => (millerStep P qx qy 0 T acc).2
  | i + 1, T, acc =>
    let (T', acc') := millerStep P qx qy (i + 1) T acc
    millerAux P qx qy i T' acc'

/-- The Miller value `f_{r,P}(Q)` for a finite `P` and the `Fq12` image of a finite `G2` point.

`r` has 254 bits (`Nat.log2 r = 253`), so its bits are `253 … 0`. The MSB (bit 253) is `1` and is
consumed by initialising `T = P` and `f = 1`; the walk therefore covers bits `252 … 0`, which is
`253` steps, exactly `range(r.bit_length()-2, -1, -1)` in the validated prototype. -/
def miller (P : Nat × Nat) (Q : Fq12 × Fq12) : Fq12 :=
  millerAux P Q.1 Q.2 252 (some P) Fq12.one

/-- `(q¹² − 1) / r`, the final exponentiation of the reduced Tate pairing. This is a 3048-bit
literal expressed as the closed form `bn`'s target group has; the compiled evaluator is what
reduces it (`decide` on it would exhaust the elaborator). -/
def finalExp : Nat := (q ^ 12 - 1) / r

/-- The reduced Tate pairing `t(P,Q) = f_{r,P}(Ψ(Q))^((q¹²−1)/r)`. A pair with an infinity
contributes `1`, exactly as `bn`'s `pairing_batch` skips such pairs (`groups/mod.rs:4395-4414`). -/
def pairing (P : Option (Nat × Nat)) (Q : Option (Fq2 × Fq2)) : Fq12 :=
  match P, Q with
  | some Pa, some Qa => Fq12.pow (miller Pa (embedG2 Qa)) finalExp
  | _, _ => Fq12.one

/-- **The host's decision**: `∏ e(g1ᵢ, g2ᵢ) = 1` over the decoded pairs. This is the predicate
`logic/alt_bn128.rs:78-93` computes as `pairing_batch(&elements) == Gt::one()`. -/
def productIsOne (pairs : List (Option (Nat × Nat) × Option (Fq2 × Fq2))) : Bool :=
  (pairs.foldl (fun acc (p, s) => Fq12.mul acc (pairing p s)) Fq12.one) = Fq12.one

/-- An empty product is one, so the host's verdict is `1`: the definitional half of the empty-input
case (`logic/alt_bn128.rs:78-93` multiplies no pairings, and `bn` returns `Fq12::one()` at
`groups/mod.rs:4411-4413`). The numeric half — that `Fq12.one = Fq12.one` — is `rfl` as well, so
this is a complete statement for the empty input. -/
theorem productIsOne_nil : productIsOne [] = true := rfl

/-! ## The wire codec (`logic/alt_bn128.rs:95-169`)

Every decoder rejects a non-canonical 32-byte word with `invalid fq` / `invalid fr`, and the two
coordinate decoders run **x first, then y** (`:114-123`, `:132-142`); the element splitter's error
precedes both (`:25-29`). -/

/-- A 32-byte little-endian word as a `Nat` (`decode_u256`, `:156-161`): the first 16 bytes are the
low half, so plain `leToNat`. -/
def leWord (b : Bytes) : Nat := Bytes.leToNat b

/-- `decode_fq` (`:126-129`): 32 bytes, little-endian, `< q`, else `none`. -/
def decodeFq (b : Bytes) : Option Nat :=
  if b.length = 32 then
    let v := leWord b
    if v < q then some v else none
  else none

/-- `decode_fr` (`:151-154`): 32 bytes, little-endian, `< r`, else `none`. -/
def decodeFr (b : Bytes) : Option Nat :=
  if b.length = 32 then
    let v := leWord b
    if v < r then some v else none
  else none

/-- `decode_bool` (`:163-168`): one byte, `0` or `1`. -/
def decodeBool (b : Bytes) : Option Bool :=
  match b with
  | [0] => some false
  | [1] => some true
  | _ => none

/-- `encode_u256` (`:108-111`): 32 bytes little-endian. -/
def encodeWord (v : Nat) : Bytes := Bytes.leN 32 v

/-- `decode_g1` (`:113-124`): `x` then `y`; `(0, 0)` is infinity; otherwise the curve equation must
hold. `bn`'s `G1Params::subgroup_check` is `true`, so no subgroup test. -/
def decodeG1 (b : Bytes) : Option (Option (Nat × Nat)) :=
  if b.length = 64 then
    match decodeFq (b.take 32), decodeFq (b.drop 32) with
    | some x, some y =>
      if x = 0 ∧ y = 0 then some none
      else if G1.onCurve x y then some (some (x, y)) else none
    | _, _ => none
  else none

/-- `decode_fq2` (`:144-149`): `real ‖ imaginary`, each canonical. -/
def decodeFq2 (b : Bytes) : Option Fq2 :=
  if b.length = 64 then
    match decodeFq (b.take 32), decodeFq (b.drop 32) with
    | some re, some im => some ⟨re, im⟩
    | _, _ => none
  else none

/-- `decode_g2` (`:131-142`): `x` then `y`, each an `Fq2`; `(0, 0)` is infinity; otherwise the twist
equation **and** the `[r]P = O` subgroup check (`check_order() = true`, `groups/mod.rs:672-674`)
must hold. -/
def decodeG2 (b : Bytes) : Option (Option (Fq2 × Fq2)) :=
  if b.length = 128 then
    match decodeFq2 (b.take 64), decodeFq2 (b.drop 64) with
    | some x, some y =>
      if Fq2.isZero x ∧ Fq2.isZero y then some none
      else if G2.onCurve x y ∧ G2.inSubgroup (G2.ofAffine x y) then some (some (x, y)) else none
    | _, _ => none
  else none

/-- `encode_g1` (`:95-102`): infinity encodes as 64 zero bytes; a finite point's affine
coordinates are recovered through `Z⁻¹`. A `Z = 1` result (which every `add`/`dbl` chain leaves
for a finite point, up to the `2YZ` factor) needs the inverse, so this is the general form. -/
def encodeG1 (P : G1) : Bytes :=
  match G1.affine? P with
  | some (x, y) => encodeWord x ++ encodeWord y
  | none => Bytes.leN 32 0 ++ Bytes.leN 32 0

/-- Split a byte string into fixed-size chunks (`stdx::as_chunks_exact`); a trailing partial chunk
is dropped, which the hosts never see because the length gate rejects a non-multiple first. -/
def chunksExact (n : Nat) : Bytes → List Bytes
  | [] => []
  | b => if n = 0 ∨ b.length < n then [] else b.take n :: chunksExact n (b.drop n)
termination_by b => b.length
decreasing_by
  simp only [List.length_drop]
  omega

@[simp] theorem chunksExact_nil (n : Nat) : chunksExact n [] = [] := by
  rw [chunksExact]

/-- `g1_multiexp` (`:36-49`): `(G1, Fr)` pairs; the result is the encoded `∑ kᵢ·Pᵢ`. `bn` runs
Pippenger (`lib.rs:405-414`), which computes the same group element as the plain sum. -/
def g1MultiExp (d : Bytes) : Option Bytes :=
  let rec go : List Bytes → G1 → Option G1
    | [], acc => some acc
    | item :: rest, acc =>
      match decodeG1 (item.take 64), decodeFr (item.drop 64) with
      | some P, some s =>
        let Pj := match P with
          | some (x, y) => G1.ofAffine x y
          | none => G1.inf
        go rest (G1.add acc (G1.smul s Pj))
      | _, _ => none
  match go (chunksExact 96 d) G1.inf with
  | some P => some (encodeG1 P)
  | none => none

/-- `g1_sum` (`:51-73`): `(sign, G1)` pairs, `sign ∈ {0,1}`, summed with negation for `sign = 1`. -/
def g1Sum (d : Bytes) : Option Bytes :=
  let rec go : List Bytes → G1 → Option G1
    | [], acc => some acc
    | item :: rest, acc =>
      match item with
      | [] => none
      | sign :: pt =>
        match decodeBool [sign], decodeG1 pt with
        | some sg, some P =>
          let Pj := match P with
            | some (x, y) => G1.ofAffine x y
            | none => G1.inf
          go rest (if sg then G1.add acc (G1.neg Pj) else G1.add acc Pj)
        | _, _ => none
  match go (chunksExact 65 d) G1.inf with
  | some P => some (encodeG1 P)
  | none => none

/-- `pairing_check` (`:75-93`): the verdict `1` iff `∏ e(g1ᵢ, g2ᵢ) = 1`. A malformed chunk is
`none`, which the host arm turns into `AltBn128InvalidInput`; a well-formed product that is not one
is the `0` verdict, and a product that is one is `1` — matching `logic.rs:1051-1053`
(`Ok(res as u64)`). -/
def pairingCheck (d : Bytes) : Option Nat :=
  let rec go : List Bytes → List (Option (Nat × Nat) × Option (Fq2 × Fq2)) → Option (List (Option (Nat × Nat) × Option (Fq2 × Fq2)))
    | [], acc => some acc
    | item :: rest, acc =>
      match decodeG1 (item.take 64), decodeG2 (item.drop 64) with
      | some P, some Q => go rest (acc ++ [(P, Q)])
      | _, _ => none
  match go (chunksExact 192 d) [] with
  | some pairs => some (if productIsOne pairs then 1 else 0)
  | none => none

end AltBn128
end NearSpecV3
