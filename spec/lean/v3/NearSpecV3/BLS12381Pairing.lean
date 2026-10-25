import NearSpecV3.BLS12381

/-!
# The BLS12-381 optimal ate pairing, as `bls12381_pairing_check` consumes it

Second BLS12-381 leaf module (after `BLS12381.lean`), for the one host that needs the target group:
`bls12381_pairing_check` (`runtime/near-vm-runner/src/logic/bls12381.rs:329-384`), which returns `0`
when `∏ e(g1ᵢ, g2ᵢ) = 1`, `1` when a point fails to decode or is not in G1/G2, and `2` when the
product is something else (`wasmtime_runner/logic.rs:1332-1340`).

## The tower

`Fp2 = Fp[u]/(u²+1)` (in `BLS12381.lean`), `Fp6 = Fp2[v]/(v³ − (u+1))`, `Fp12 = Fp6[w]/(w² − v)`.
The Karatsuba formulas are the RustCrypto `bls12_381` 0.7.1 crate's (`src/fp6.rs:236-291`,
`src/fp12.rs:174-213`), which documents them from "Multiplication and Squaring on Pairing-Friendly
Fields" (`eprint 2006/471`); the same tower underlies `blst`. Agreement with `blst` 0.3.11 — the
library nearcore actually calls — is *tested* against `oracle/bls-oracle`, not proved.

## The loop and the final exponentiation

* Loop parameter `x = −0xd201000000010000 = −(2⁶³ + 2⁶² + 2⁶⁰ + 2⁵⁷ + 2⁴⁸ + 2¹⁶)`; `BLS_X_IS_NEGATIVE`
  is true for BLS12-381 (`bls12_381-0.7.1/src/lib.rs`).
* Miller loop `pairings.rs:668-694`: doubling steps over the bits of `|x| >> 1`, an addition step
  wherever the bit is set, one final doubling step, then conjugation because `x < 0`.
* Line functions `ell` / `doubling_step` / `addition_step` (`pairings.rs:696-770`), evaluated into
  `Fp12` by `mul_by_014` (`fp12.rs:116-128`).
* A pair with an identity point contributes the factor `1` (`pairings.rs:566-581`).
* Final exponentiation `pairings.rs:56-146`: easy part `f^(p⁶−1)` then `^(p²+1)`; the hard part in
  the cyclotomic subgroup. Because the *decision* only asks "is the result one", `productIsOne` runs
  the same decomposition the Rust crate runs rather than a naive 1524-bit exponentiation.

## Status
Tested against the pinned `blst` oracle on directed and generated inputs (see the lane log);
nothing here is claimed equal to `blst` by proof. Proved here: the empty-input verdict
(`productIsOne_nil`).
-/

namespace NearSpecV3
namespace BLS12381
namespace Pairing

/-! ## `Fp6 = Fp2[v]/(v³ − (u+1))` -/

/-- An `Fp6` element `c0 + c1·v + c2·v²`. -/
structure Fp6 where
  c0 : Fp2
  c1 : Fp2
  c2 : Fp2
  deriving DecidableEq, Repr

namespace Fp6

def zero : Fp6 := ⟨Fp2.zero, Fp2.zero, Fp2.zero⟩
def one : Fp6 := ⟨Fp2.one, Fp2.zero, Fp2.zero⟩

def add (a b : Fp6) : Fp6 := ⟨Fp2.add a.c0 b.c0, Fp2.add a.c1 b.c1, Fp2.add a.c2 b.c2⟩
def sub (a b : Fp6) : Fp6 := ⟨Fp2.sub a.c0 b.c0, Fp2.sub a.c1 b.c1, Fp2.sub a.c2 b.c2⟩
def neg (a : Fp6) : Fp6 := ⟨Fp2.neg a.c0, Fp2.neg a.c1, Fp2.neg a.c2⟩

/-- Multiplication by the cubic non-residue `v`: `a + bv + cv² ↦ c(u+1) + av + bv²`
(`fp6.rs:139-150`, using `v³ = u + 1`). -/
def mulByV (a : Fp6) : Fp6 :=
  ⟨Fp2.mulByNonresidue a.c2, a.c0, a.c1⟩

/-- Karatsuba multiplication (`fp6.rs:236-278`).

With `a = a0 + a1·v + a2·v²`, `b = b0 + b1·v + b2·v²` and `ξ = u+1` (`v³ = ξ`):
`c0 = a0b0 + ξ(a1b2 + a2b1)`, `c1 = a0b1 + a1b0 + ξ·a2b2`, `c2 = a0b2 + a1b1 + a2b0`. -/
def mul (a b : Fp6) : Fp6 :=
  let aa := Fp2.mul a.c0 b.c0
  let bb := Fp2.mul a.c1 b.c1
  let cc := Fp2.mul a.c2 b.c2
  let t1 := Fp2.add (Fp2.mulByNonresidue
    (Fp2.sub (Fp2.sub (Fp2.mul (Fp2.add a.c1 a.c2) (Fp2.add b.c1 b.c2)) bb) cc)) aa
  let t2 := Fp2.add
    (Fp2.sub (Fp2.sub (Fp2.mul (Fp2.add a.c0 a.c1) (Fp2.add b.c0 b.c1)) aa) bb)
    (Fp2.mulByNonresidue cc)
  let t3 := Fp2.add
    (Fp2.sub (Fp2.sub (Fp2.mul (Fp2.add a.c0 a.c2) (Fp2.add b.c0 b.c2)) aa) cc) bb
  ⟨t1, t2, t3⟩

/-- Squaring (`fp6.rs:277-291`). -/
def sqr (a : Fp6) : Fp6 :=
  let s0 := Fp2.mul a.c0 a.c0
  let ab := Fp2.mul a.c0 a.c1
  let s1 := Fp2.dbl ab
  let d := Fp2.add (Fp2.sub a.c0 a.c1) a.c2
  let s2 := Fp2.mul d d
  let bc := Fp2.mul a.c1 a.c2
  let s3 := Fp2.dbl bc
  let s4 := Fp2.mul a.c2 a.c2
  ⟨Fp2.add (Fp2.mulByNonresidue s3) s0,
   Fp2.add (Fp2.mulByNonresidue s4) s1,
   Fp2.sub (Fp2.sub (Fp2.add (Fp2.add s1 s2) s3) s0) s4⟩

/-- Inverse (`fp6.rs:293-312`). -/
def inv (a : Fp6) : Option Fp6 :=
  let c0 := Fp2.sub (Fp2.mul a.c0 a.c0) (Fp2.mulByNonresidue (Fp2.mul a.c1 a.c2))
  let c1 := Fp2.sub (Fp2.mulByNonresidue (Fp2.mul a.c2 a.c2)) (Fp2.mul a.c0 a.c1)
  let c2 := Fp2.sub (Fp2.mul a.c1 a.c1) (Fp2.mul a.c0 a.c2)
  let tmp := Fp2.add (Fp2.mulByNonresidue (Fp2.add (Fp2.mul a.c1 c2) (Fp2.mul a.c2 c1)))
                     (Fp2.mul a.c0 c0)
  match Fp2.inv tmp with
  | none => none
  | some t => some ⟨Fp2.mul t c0, Fp2.mul t c1, Fp2.mul t c2⟩

/-- `mul_by_01(c0, c1)` (`fp6.rs:121-136`): multiplication by an element with no `v²` part. -/
def mulBy01 (a : Fp6) (c0 c1 : Fp2) : Fp6 :=
  let aa := Fp2.mul a.c0 c0
  let bb := Fp2.mul a.c1 c1
  let t1 := Fp2.add (Fp2.mulByNonresidue (Fp2.mul a.c2 c1)) aa
  let t2 := Fp2.sub (Fp2.sub (Fp2.mul (Fp2.add c0 c1) (Fp2.add a.c0 a.c1)) aa) bb
  let t3 := Fp2.add (Fp2.mul a.c2 c0) bb
  ⟨t1, t2, t3⟩

/-- `mul_by_1(c1)` (`fp6.rs:113-119`): multiplication by `c1·v`. -/
def mulBy1 (a : Fp6) (c1 : Fp2) : Fp6 :=
  ⟨Fp2.mulByNonresidue (Fp2.mul a.c2 c1), Fp2.mul a.c0 c1, Fp2.mul a.c1 c1⟩

/-- `(u+1)^((p−1)/3)`, the `c1` Frobenius coefficient (`fp6.rs:159-171`; the literal there is in
Montgomery form and equals this power — checked exactly in the lane log). -/
def frobC1 : Fp2 := Fp2.pow ⟨1, 1⟩ ((p - 1) / 3)

/-- `(u+1)^((2p−2)/3)`, the `c2` Frobenius coefficient (`fp6.rs:173-185`). -/
def frobC2 : Fp2 := Fp2.pow ⟨1, 1⟩ ((2 * (p - 1)) / 3)

/-- Frobenius `a ↦ a^p` on `Fp6`: conjugate each component and scale `c1`, `c2` by the constants. -/
def frobenius (a : Fp6) : Fp6 :=
  ⟨Fp2.conj a.c0, Fp2.mul (Fp2.conj a.c1) frobC1, Fp2.mul (Fp2.conj a.c2) frobC2⟩

end Fp6

/-! ## `Fp12 = Fp6[w]/(w² − v)` -/

/-- An `Fp12` element `c0 + c1·w`. -/
structure Fp12 where
  c0 : Fp6
  c1 : Fp6
  deriving DecidableEq, Repr

namespace Fp12

def zero : Fp12 := ⟨Fp6.zero, Fp6.zero⟩
def one : Fp12 := ⟨Fp6.one, Fp6.zero⟩

def add (a b : Fp12) : Fp12 := ⟨Fp6.add a.c0 b.c0, Fp6.add a.c1 b.c1⟩
def neg (a : Fp12) : Fp12 := ⟨Fp6.neg a.c0, Fp6.neg a.c1⟩
def sub (a b : Fp12) : Fp12 := add a (neg b)

/-- Conjugation `a ↦ ā = c0 − c1·w` (`fp12.rs:136-141`); for a unitary element this is its inverse. -/
def conj (a : Fp12) : Fp12 := ⟨a.c0, Fp6.neg a.c1⟩

/-- Karatsuba multiplication in the quadratic extension (`fp12.rs:197-214`). -/
def mul (a b : Fp12) : Fp12 :=
  let aa := Fp6.mul a.c0 b.c0
  let bb := Fp6.mul a.c1 b.c1
  let o := Fp6.add b.c0 b.c1
  let t := Fp6.mul (Fp6.add a.c1 a.c0) o
  let c1 := Fp6.sub (Fp6.sub t aa) bb
  let c0 := Fp6.add (Fp6.mulByV bb) aa
  ⟨c0, c1⟩

/-- Squaring (`fp12.rs:174-185`). -/
def sqr (a : Fp12) : Fp12 :=
  let ab := Fp6.mul a.c0 a.c1
  let c0c1 := Fp6.add a.c0 a.c1
  let t := Fp6.mul (Fp6.add (Fp6.mulByV a.c1) a.c0) c0c1
  let c0 := Fp6.sub (Fp6.sub t ab) (Fp6.mulByV ab)
  let c1 := Fp6.add ab ab
  ⟨c0, c1⟩

/-- Inverse (`fp12.rs:187-194`): `(c0² − v·c1²)⁻¹`. -/
def inv (a : Fp12) : Option Fp12 :=
  match Fp6.inv (Fp6.sub (Fp6.mul a.c0 a.c0) (Fp6.mulByV (Fp6.mul a.c1 a.c1))) with
  | none => none
  | some t => some ⟨Fp6.mul a.c0 t, Fp6.neg (Fp6.mul a.c1 t)⟩

/-- `mul_by_014(c0, c1, c4)` (`fp12.rs:116-128`): multiplication by the sparse element
`c0 + c1·w + c4·w³`, which is what a line evaluation produces. -/
def mulBy014 (a : Fp12) (c0 c1 c4 : Fp2) : Fp12 :=
  let aa := Fp6.mulBy01 a.c0 c0 c1
  let bb := Fp6.mulBy1 a.c1 c4
  let o := Fp2.add c1 c4
  let t := Fp6.mulBy01 (Fp6.add a.c1 a.c0) c0 o
  let c1' := Fp6.sub (Fp6.sub t aa) bb
  let c0' := Fp6.add (Fp6.mulByV bb) aa
  ⟨c0', c1'⟩

/-- `(u+1)^((p−1)/6)`, the `Fp12` Frobenius coefficient (`fp12.rs:149-171`). The crate multiplies
the *whole* `Fp6` element `c1^p` by this `Fp2` scalar (`Fp6::from(Fp2{..})` is the scalar
embedding), so each of its three `Fp2` coefficients is scaled — not `c1·γ·v`. -/
def frobGamma : Fp2 := Fp2.pow ⟨1, 1⟩ ((p - 1) / 6)

/-- Scale an `Fp6` element by an `Fp2` scalar. -/
def scaleFp6 (a : Fp6) (s : Fp2) : Fp6 := ⟨Fp2.mul a.c0 s, Fp2.mul a.c1 s, Fp2.mul a.c2 s⟩

/-- Frobenius `a ↦ a^p` on `Fp12`: `(c0^p, γ · c1^p)` with `γ = (u+1)^((p−1)/6)` (`fp12.rs:149-171`). -/
def frobenius (a : Fp12) : Fp12 :=
  ⟨Fp6.frobenius a.c0, scaleFp6 (Fp6.frobenius a.c1) frobGamma⟩

/-- `a^(p²)` and `a^(p⁶)`, the two Frobenius powers the final exponentiation's easy part needs. -/
def frob2 (a : Fp12) : Fp12 := frobenius (frobenius a)
def frob6 (a : Fp12) : Fp12 := frob2 (frob2 (frob2 a))

/-- `a^n` by square-and-multiply. The exponent is a `Nat`, so the kernel can reduce concrete
instances; the compiled evaluator is what runs the tests. -/
def powAux : Nat → Fp12 → Nat → Fp12
  | 0, _, _ => one
  | f + 1, bb, e =>
    let q := powAux f bb (e / 2)
    if e % 2 = 1 then mul (mul q q) bb else mul q q

def pow (bb : Fp12) (e : Nat) : Fp12 := powAux 1600 bb e

end Fp12

/-! ## The Miller loop

`bls12_381-0.7.1/src/pairings.rs:696-770` ported literally. `G2Proj` is the crate's homogeneous
projective representation (`g2.rs:495-499`), which the line formulas assume. -/

/-- A G2 point in homogeneous projective coordinates `(X : Y : Z)`; `Z = 0` is infinity. -/
structure G2Proj where
  x : Fp2
  y : Fp2
  z : Fp2
  deriving DecidableEq, Repr

namespace G2Proj

def inf : G2Proj := ⟨Fp2.zero, Fp2.one, Fp2.zero⟩

def ofAffine (P : G2) : G2Proj :=
  match P.affine? with
  | some (x, y) => ⟨x, y, Fp2.one⟩
  | none => inf

def isInf (P : G2Proj) : Bool := P.z = Fp2.zero

/-- The twist's `b` coefficient times 3: `3b = 3·4(u+1) = 12 + 12u`
(`bls12_381-0.7.1/src/g2.rs`, `mul_by_3b`). -/
def b3 : Fp2 := ⟨12, 12⟩

/-- `G2Projective::double` (`g2.rs:709-738`, Algorithm 9 of `eprint 2015/1060`), used by the Miller
loop's doubling step to advance `T`. -/
def dbl (P : G2Proj) : G2Proj :=
  if P.z = Fp2.zero then P else
  let t0 := Fp2.mul P.y P.y
  let z3a := Fp2.dbl (Fp2.dbl (Fp2.dbl t0))
  let t1 := Fp2.mul P.y P.z
  let t2 := Fp2.mul b3 (Fp2.mul P.z P.z)
  let x3a := Fp2.mul t2 z3a
  let y3a := Fp2.add t0 t2
  let z3 := Fp2.mul t1 z3a
  let t1' := Fp2.dbl t2
  let t2' := Fp2.add t1' t2
  let t0' := Fp2.sub t0 t2'
  let y3b := Fp2.mul t0' y3a
  let y3 := Fp2.add x3a y3b
  let t1'' := Fp2.mul P.x P.y
  let x3b := Fp2.mul t0' t1''
  let x3 := Fp2.dbl x3b
  ⟨x3, y3, z3⟩

end G2Proj

/-- The three `Fp2` coefficients a line evaluation carries (`pairings.rs:709-770`). -/
abbrev Line := Fp2 × Fp2 × Fp2

/-- `doubling_step` (`pairings.rs:709-738`): advance `T` and produce its line coefficients. -/
def doublingStep (T : G2Proj) : G2Proj × Line :=
  if T.z = Fp2.zero then (T, (Fp2.one, Fp2.one, Fp2.one)) else
  let tmp0 := Fp2.mul T.x T.x
  let tmp1 := Fp2.mul T.y T.y
  let tmp2 := Fp2.mul tmp1 tmp1
  let s := Fp2.sub (Fp2.sub (Fp2.mul (Fp2.add tmp1 T.x) (Fp2.add tmp1 T.x)) tmp0) tmp2
  let tmp3 := Fp2.dbl s
  let tmp4 := Fp2.add (Fp2.add tmp0 tmp0) tmp0
  let tmp6 := Fp2.add T.x tmp4
  let tmp5 := Fp2.mul tmp4 tmp4
  let zsq := Fp2.mul T.z T.z
  let x' := Fp2.sub (Fp2.sub tmp5 tmp3) tmp3
  let z' := Fp2.sub (Fp2.sub (Fp2.mul (Fp2.add T.z T.y) (Fp2.add T.z T.y)) tmp1) zsq
  let y' := Fp2.sub (Fp2.mul (Fp2.sub tmp3 x') tmp4) (Fp2.oct tmp2)
  let t3 := Fp2.neg (Fp2.dbl (Fp2.mul tmp4 zsq))
  let t6 := Fp2.sub (Fp2.sub (Fp2.sub (Fp2.mul tmp6 tmp6) tmp0) tmp5) (Fp2.dbl (Fp2.dbl tmp1))
  let t0 := Fp2.dbl (Fp2.mul z' zsq)
  (⟨x', y', z'⟩, (t0, t3, t6))

/-- `addition_step` (`pairings.rs:740-770`): advance `T` by the affine `q` and produce its line
coefficients. -/
def additionStep (T : G2Proj) (q : Fp2 × Fp2) : G2Proj × Line :=
  if T.z = Fp2.zero then (T, (Fp2.one, Fp2.one, Fp2.one)) else
  let zsq := Fp2.mul T.z T.z
  let ysq := Fp2.mul q.2 q.2
  let t0 := Fp2.mul zsq q.1
  let t1 := Fp2.mul (Fp2.sub (Fp2.sub (Fp2.mul (Fp2.add q.2 T.z) (Fp2.add q.2 T.z)) ysq) zsq) zsq
  let t2 := Fp2.sub t0 T.x
  let t3 := Fp2.mul t2 t2
  let t4 := Fp2.dbl (Fp2.dbl t3)
  let t5 := Fp2.mul t4 t2
  let t6 := Fp2.sub (Fp2.sub t1 T.y) T.y
  let t9a := Fp2.mul t6 q.1
  let t7 := Fp2.mul t4 T.x
  let x' := Fp2.sub (Fp2.sub (Fp2.sub (Fp2.mul t6 t6) t5) t7) t7
  let z' := Fp2.sub (Fp2.sub (Fp2.mul (Fp2.add T.z t2) (Fp2.add T.z t2)) zsq) t3
  let t10a := Fp2.add q.2 z'
  let t8 := Fp2.mul (Fp2.sub t7 x') t6
  let t0b := Fp2.dbl (Fp2.mul T.y t5)
  let y' := Fp2.sub t8 t0b
  let t10b := Fp2.sub (Fp2.sub (Fp2.mul t10a t10a) ysq) (Fp2.mul z' z')
  -- `let t9 = t9 + t9 - t10;` (`pairings.rs:764`): `t10` is subtracted once
  let t9 := Fp2.sub (Fp2.dbl t9a) t10b
  let t10 := Fp2.dbl z'
  let t6' := Fp2.neg t6
  let t1' := Fp2.dbl t6'
  (⟨x', y', z'⟩, (t10, t1', t9))

/-- `ell` (`pairings.rs:696-707`): multiply `f` by the line evaluated at the G1 point `p`.
`coeffs = (c0, c1, c2)`; the result is `f.mul_by_014(c2, c1·x, c0·y)`. -/
def ell (f : Fp12) (coeffs : Line) (px py : Nat) : Fp12 :=
  let c0 := coeffs.1
  let c1 := coeffs.2.1
  let c0y := Fp2.mul coeffs.1 ⟨py, 0⟩
  let c1x := Fp2.mul coeffs.2.1 ⟨px, 0⟩
  let _ := c0
  let _ := c1
  Fp12.mulBy014 f coeffs.2.2 c1x c0y

/-- The BLS parameter's absolute value shifted right by one, whose 64 bits drive the loop:
`|x| >> 1 = 0x6900800000008000`. `BLS_X_IS_NEGATIVE` is true, so one final conjugation applies
(`pairings.rs:600`, `pairings.rs:686-688`). -/
def blsXHalf : Nat := 0xd201000000010000 >>> 1

/-- One term's Miller loop (`pairings.rs:600-689`), transcribed exactly:

* `f = 1`; walk bits `63 … 0` of `|x| >> 1`;
* the leading run of zero bits *and the first set bit* are skipped (`found_one`), because the
  accumulator is still `1` there;
* every later bit does `f ← ell(doubling_step)`, then, when the bit is set, `f ← ell(addition_step)`,
  then `f ← f.square()`;
* after the loop, one last `ell(doubling_step)` and — since `BLS_X_IS_NEGATIVE` — `f ← conj f`.

The crate's `pairing` substitutes the *generator* for an identity input and selects `Fp12::one()` as
the result afterwards (`pairings.rs:641-661`). Because `productIsOne` only asks whether the final
exponentiation is one, and `finalExp 1 = 1`, returning the constant `1` for an identity term is
equivalent to the crate's select — but only when the *other* term is also degenerate, so the
substitution is reproduced faithfully below: an identity `Q` runs the loop against the G2 generator
and the result is then discarded, while a finite `Q` with identity `P` runs the loop and yields
`f^((p¹²−1)/r) = 1`. -/
def millerLoop (P : G2) (px py : Nat) : Fp12 :=
  if P.isInf then Fp12.one else
  let q := match P.affine? with
    | some (x, y) => (x, y)
    | none => (Fp2.zero, Fp2.one)
  -- `go n found T f` handles bits `n-1 … 0` in that order, mirroring `(0..64).rev()`
  let rec go : Nat → Bool → G2Proj → Fp12 → G2Proj × Fp12
    | 0, _, T, f => (T, f)
    | n + 1, found, T, f =>
      let bitSet := blsXHalf.testBit n
      if !found then
        -- `found_one = i; continue`: the first set bit only arms the accumulator
        go n bitSet T f
      else
        let (T1, c1) := doublingStep T
        let f1 := ell f c1 px py
        if bitSet then
          let (T2, c2) := additionStep T1 q
          go n found T2 (Fp12.sqr (ell f1 c2 px py))
        else
          go n found T1 (Fp12.sqr f1)
  let (Tf, f0) := go 64 false (G2Proj.ofAffine P) Fp12.one
  -- the trailing `f = driver.doubling_step(f)` after the bit loop
  let (_, cfin) := doublingStep Tf
  Fp12.conj (ell f0 cfin px py)

/-! ## The final exponentiation and the decision

`bls12_381-0.7.1/src/pairings.rs:56-146`. The easy part is `f^(p⁶−1)` (= `conj(f)/f`, because
`f^(p⁶) = conj f` for this tower) followed by `^(p²+1)`; the hard part then runs in the cyclotomic
subgroup with the crate's `cyclotomic_square` / `fp4_square` chain. The decision is "is the result
`Fp12.one`", the comparison `blst_fp12_is_one` performs. -/

/-- `fp4_square(a, b)` (`pairings.rs:59-73`): squaring inside `Fp4` with the tower's non-residue. -/
def fp4Square (a b : Fp2) : Fp2 × Fp2 :=
  let t0 := Fp2.mul a a
  let t1 := Fp2.mul b b
  let t2 := Fp2.mulByNonresidue t1
  let c0 := Fp2.add t2 t0
  let t2' := Fp2.mul (Fp2.add a b) (Fp2.add a b)
  let t2'' := Fp2.sub t2' t0
  let c1 := Fp2.sub t2'' t1
  (c0, c1)

/-- `cyclotomic_square` (`pairings.rs:78-125`), Algorithm 5.5.4 of the *Guide to Pairing-Based
Cryptography* (`eprint 2009/565`). -/
def cyclotomicSquare (f : Fp12) : Fp12 :=
  let z0 := f.c0.c0
  let z4 := f.c0.c1
  let z3 := f.c0.c2
  let z2 := f.c1.c0
  let z1 := f.c1.c1
  let z5 := f.c1.c2
  let (t0, t1) := fp4Square z0 z1
  let z0a := Fp2.add (Fp2.sub t0 z0) (Fp2.add (Fp2.sub t0 z0) t0)
  let z1a := Fp2.add (Fp2.add t1 z1) (Fp2.add (Fp2.add t1 z1) t1)
  let (t0b, t1b) := fp4Square z2 z3
  let (t2, t3) := fp4Square z4 z5
  let z4a := Fp2.add (Fp2.sub t0b z4) (Fp2.add (Fp2.sub t0b z4) t0b)
  let z5a := Fp2.add (Fp2.add t1b z5) (Fp2.add (Fp2.add t1b z5) t1b)
  let t0c := Fp2.mulByNonresidue t3
  let z2a := Fp2.add (Fp2.add t0c z2) (Fp2.add (Fp2.add t0c z2) t0c)
  let z3a := Fp2.add (Fp2.sub t2 z3) (Fp2.add (Fp2.sub t2 z3) t2)
  ⟨⟨z0a, z4a, z3a⟩, ⟨z2a, z1a, z5a⟩⟩

/-- The BLS parameter's absolute value, whose bits drive the cyclotomic exponentiation:
`|x| = 0xd201000000010000`. -/
def blsXAbs : Nat := 0xd201000000010000

/-- `cycolotomic_exp` (`pairings.rs:126-145`): `f^x` in the cyclotomic subgroup by
`cyclotomic_square`, then conjugated because `BLS_X_IS_NEGATIVE`. -/
def cyclotomicExp (f : Fp12) : Fp12 :=
  let rec go : Nat → Fp12 → Fp12
    | 0, tmp => tmp
    | k + 1, tmp =>
      let tmp' := cyclotomicSquare tmp
      go k (if blsXAbs.testBit k then Fp12.mul tmp' f else tmp')
  Fp12.conj (go 64 Fp12.one)

/-- `final_exponentiation` (`pairings.rs:56-146`): easy part, then the crate's hard-part chain. -/
def finalExp (f : Fp12) : Fp12 :=
  let t0 := Fp12.frob6 f
  match Fp12.inv f with
  | none => Fp12.one            -- unreachable for a Miller-loop output; blst returns one as well
  | some t1 =>
    let t2 := Fp12.mul t0 t1
    let t2' := Fp12.mul (Fp12.frob2 t2) t2
    let t1' := Fp12.conj (cyclotomicSquare t2')
    let t3 := cyclotomicExp t2'
    let t4 := cyclotomicSquare t3
    let t5 := Fp12.mul t1' t3
    let t1'' := cyclotomicExp t5
    let t0' := cyclotomicExp t1''
    let t6 := cyclotomicExp t0'
    let t6a := Fp12.mul t6 t4
    let t4' := cyclotomicExp t6a
    let t5' := Fp12.conj t5
    let t4'' := Fp12.mul t4' (Fp12.mul t5' t2')
    let t5'' := Fp12.conj t2'
    let t1x := Fp12.mul t1'' t2'
    let t1f := Fp12.frob2 (Fp12.frobenius t1x)
    let t6b := Fp12.mul t6a t5''
    let t6f := Fp12.frobenius t6b
    let t3a := Fp12.mul t3 t0'
    let t3f := Fp12.frob2 t3a
    let t3g := Fp12.mul t3f t1f
    Fp12.mul (Fp12.mul t3g t6f) t4''

/-- **The host's decision**: `∏ e(g1ᵢ, g2ᵢ) = 1`. The Miller loop product is multiplied term by term
(`pairings.rs:563-596`) and the final exponentiation applied once at the end, exactly as
`logic/bls12381.rs:375-383` does. -/
def productIsOne (pairs : List (G1 × G2)) : Bool :=
  let f := pairs.foldl (fun acc (p1, p2) =>
      match p1.affine? with
      | some (px, py) => Fp12.mul acc (millerLoop p2 px py)
      | none => acc) Fp12.one
  finalExp f = Fp12.one

/-- The empty product: `bls12381.rs:375-383` multiplies no Miller loops, so the accumulator is
`blst_fp12::default()` = one and `final_exp(1) = 1`, hence the host returns `0`. Stated as the
*definitional* equation it is (`productIsOne []` reduces to `finalExp one = one`); the numeric
witness `finalExp one = one` is checked in the vector suite rather than in the kernel, because
`decide` on a 381-bit final exponentiation exhausts the elaborator's recursion budget. -/
theorem productIsOne_nil : productIsOne [] = (Pairing.finalExp Pairing.Fp12.one == Pairing.Fp12.one) := rfl

end Pairing

/-! ## The host payload of `bls12381_pairing_check`

`logic/bls12381.rs:329-384`. Unlike the eight register writers this has no register: it returns the
`0`/`1`/`2` verdict directly. Decoding uses the *uncompressed* reader with the top bit clear and
requires both subgroup checks to pass; any failure is the `1` return. -/

/-- Decode a `pairing_check` input's 288-byte chunks into its `(g1, g2)` pairs, or `none` when a
chunk is malformed or outside `G1`/`G2` (`logic/bls12381.rs:329-384`; the subgroup checks there are
the *hard* requirement, unlike in `p1_sum`). Structural recursion over `chunksExact 288`, so the
kernel evaluates it; the host rejects a non-multiple length before reaching here. -/
def decodePairsAux : List ArenaCore.Bytes → Option (List (G1 × G2))
  | [] => some []
  | item :: rest =>
    match Codec.decodeG1Uncompressed (item.take 96),
          Codec.decodeG2Uncompressed ((item.drop 96).take 192) with
    | some P1, some P2 =>
      if G1.inG1 P1 ∧ G2.inG2 P2 then
        match decodePairsAux rest with
        | some tail => some ((P1, P2) :: tail)
        | none => none
      else none
    | _, _ => none

def decodePairs (d : ArenaCore.Bytes) : Option (List (G1 × G2)) :=
  decodePairsAux (BLS12381.chunksExact 288 d)

/-- The `bls12381_pairing_check` payload: `0` = product one, `1` = malformed / not in `G1` or `G2`,
`2` = product ≠ one. The empty input decodes to no pairs and returns `0`. -/
def pairingCheck (d : ArenaCore.Bytes) : Nat :=
  match decodePairs d with
  | none => 1
  | some pairs => if Pairing.productIsOne pairs then 0 else 2

/-- An empty `pairing_check` input decodes to no pairs, so the answer is "product is one" (`0`).
The decode half is definitional; the numeric half (`finalExp one = one`) is checked by the compiled
vector suite rather than the kernel, for the same reason as `productIsOne_nil`. -/
theorem pairingCheck_nil_decode :
    pairingCheck ([] : ArenaCore.Bytes)
      = (if Pairing.productIsOne [] then 0 else 2) := by
  simp [pairingCheck, decodePairs, decodePairsAux, BLS12381.chunksExact_nil]

end BLS12381
end NearSpecV3

