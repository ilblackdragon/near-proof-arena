import ArenaCore.Bytes

/-!
# BLS12-381 arithmetic and codec, as performed by nearcore's `bls12381_*` hosts

Leaf module for the crypto-enabled successor domain (L3), third entry after `Secp256k1.lean` and
`P256.lean`. It transcribes the arithmetic and the wire codec of
`runtime/near-vm-runner/src/logic/bls12381.rs` (nearcore `44f7ae6c`, PV86) — which forwards every
byte of decoding and arithmetic to `blst` 0.3.11 — so that the nine `bls12381_*` hosts have a Lean
semantics instead of the blanket `out-of-domain` they get in `D3α`.

Curve: `E: y² = x³ + 4` over `Fp`, `p = 0x1a0111ea…ffffaaab` (381 bits); the twist
`E': y² = x³ + 4(u+1)` over `Fp2 = Fp[u]/(u²+1)`. Group orders: `r` (255 bits), cofactors `h1`
(G1) and `h2` (G2).

## Encoding (big-endian, `logic/bls12381.rs:6-13` sizes; docs of the eight `bls12381_impl!` uses)

| object | wire form |
|---|---|
| `Fp` | 48-byte big-endian, canonical (`< p`) |
| `Fp2` | `c1 ‖ c0`, each 48-byte big-endian — **not** the EIP-2537 order |
| G1 point | uncompressed: `x ‖ y` (96 B); compressed: 48 B, top bit = compressed, `0x40` = infinity, `0x20` = sign |
| G2 point | uncompressed: `x.c1 ‖ x.c0 ‖ y.c1 ‖ y.c0` (192 B); compressed: 96 B, same three flags |
| infinity | the point at infinity encodes as `0x40` followed by zeros in both forms |

## Status
Proved here (axiom-free modulo `propext`/`Quot.sound`, in `NearSpecV3.BLS12381.Lemmas`): the modulus
and cofactor facts (`p_mod_four`, `r_pos`, `h1_pos`, `h2_pos`, `p_lt_256_48`), the generator curve
membership (`G1_gen_on_curve`, `G2_gen_on_curve`), the `Fp` codec round trip on canonical inputs
(`ofBE_toBE`, `toBE_length`) and the resulting canonicity of every decoded value (`ofBE_lt`), and
the empty-input verdicts of the register writers (`p1Sum_nil`, `p2Sum_nil`, `p1Decompress_nil`,
`p2Decompress_nil`, `mapFpToG1_nil`, `mapFp2ToG2_nil`). The subgroup predicate `G1.inG1`/`G2.inG2`
needs 255 scalar doublings and is therefore *tested*, not kernel-reduced. The uncompressed
encode/decode round trip is also tested rather than proved: closing it in the kernel needs the
`beN` top-byte flag analysis, which is not part of the host's decision surface.

Tested, not proved: agreement of every host verdict and register payload with the pinned `blst`
oracle (`oracle/bls-oracle`, blst 0.3.11 = nearcore's locked version): 94 directed fixtures plus
9,360 generated ones across four seeds; see `docs/logs/lean-chunk-L3-bls12381-2026-10-23.md`.
-/

namespace NearSpecV3
namespace BLS12381

open ArenaCore

/-! ## `Fp` — the base field -/

/-- The BLS12-381 base-field modulus
(`runtime/near-vm-runner/src/logic/tests/bls12381.rs:19`, `parameters.snap` consumers). -/
def p : Nat :=
  4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787

/-- The scalar field / G1 group order `r` (`bls12381.rs:21` of the test module). -/
def r : Nat := 52435875175126190479447740508185965837690552500527637822603658699938581184513

/-- G1 cofactor `h1` (`blst` `map_to_g1.c`, `1-z` step): `#E(Fp) = h1 · r`. -/
def h1 : Nat := 76329603384216526031706109802092473003

/-- G2 cofactor `h2`: `#E'(Fp2) = h2 · r`. Derived from `t2 = t² − 2p`, `t = x + 1`,
`x = −0xd201000000010000`, `#E'(Fp2) = p² + 1 − t2`; checked exactly in the lane log. -/
def h2 : Nat :=
  305502333931268344200999753193121504214466019254188142667664032982267604182971884026507427359259977847832272839041692990889188039904403802465579155252111

namespace Fp

def add (a b : Nat) : Nat := (a + b) % p
def sub (a b : Nat) : Nat := (a + (p - b % p)) % p
def mul (a b : Nat) : Nat := (a * b) % p
def neg (a : Nat) : Nat := (p - a % p) % p

/-- `a^e` in `Fp`, square-and-multiply. Structural in the exponent so the kernel can reduce it. -/
def powAux : Nat → Nat → Nat → Nat
  | 0, _, _ => 1
  | f + 1, bb, e =>
    let q := powAux f bb (e / 2)
    if e % 2 = 1 then mul (mul q q) bb else mul q q

def pow (bb e : Nat) : Nat := powAux 400 bb e

/-- `a⁻¹ = a^(p-2)` (`Fp` is a field; `inv 0 = 0`, unused by the hosts). -/
def inv (a : Nat) : Nat := pow a (p - 2)

/-- `sqrt a = a^((p+1)/4)`: valid because `p ≡ 3 (mod 4)` (`p_mod_four`). The hosts only accept
the result after checking `(sqrt a)² = a`, so the choice of root is irrelevant here. -/
def sqrt (a : Nat) : Nat := pow a ((p + 1) / 4)

/-- `blst`'s `sgn0` for `Fp`: `1` when `a > (p−1)/2`, else `0` (`blst/src/no_asm.h:529-536`,
`sgn0_pty_mont_384` → `sgn0_pty_mod_n`, whose sign bit is `a > (p−1)/2`). This is the "sign" bit a
compressed point carries, and the bit `blst` normalises against on decompression. -/
def sgn0 (a : Nat) : Nat := if (p - 1) / 2 < a % p then 1 else 0

/-- The IETF `sgn0` *parity* bit for `Fp`: `a mod 2` (`blst`'s `sgn0_pty_mont_384 & 1`, whose low bit
is the parity of the canonical representative — `no_asm.h:487-514`). This is the sign rule the SSWU
map uses (`map_to_g1.c:319`, `sgn0_fp`), which is *not* the compressed-point sign bit. -/
def parity (a : Nat) : Nat := a % 2

/-- Canonical 48-byte big-endian decoding: `none` when the input is not 48 bytes or not `< p`
(`read_fp_point`, `logic/bls12381.rs:395-415`: the blst `bendian_from_fp` round trip rejects every
non-canonical encoding). -/
def ofBE (b : Bytes) : Option Nat :=
  if b.length = 48 then
    let x := Bytes.beToNat b
    if x < p then some x else none
  else none

def toBE (x : Nat) : Bytes := Bytes.beN 48 x

end Fp

/-! ## `Fp2 = Fp[u]/(u²+1)` -/

/-- An `Fp2` element `c0 + c1·u`, components kept reduced in `Fp`. -/
structure Fp2 where
  c0 : Nat
  c1 : Nat
  deriving DecidableEq, Repr

namespace Fp2

def zero : Fp2 := ⟨0, 0⟩
def one : Fp2 := ⟨1, 0⟩

def add (a b : Fp2) : Fp2 := ⟨Fp.add a.c0 b.c0, Fp.add a.c1 b.c1⟩
def sub (a b : Fp2) : Fp2 := ⟨Fp.sub a.c0 b.c0, Fp.sub a.c1 b.c1⟩
def neg (a : Fp2) : Fp2 := ⟨Fp.neg a.c0, Fp.neg a.c1⟩

/-- `(a0 + a1 u)(b0 + b1 u) = (a0 b0 − a1 b1) + (a0 b1 + a1 b0) u`, since `u² = −1`. -/
def mul (a b : Fp2) : Fp2 :=
  ⟨Fp.sub (Fp.mul a.c0 b.c0) (Fp.mul a.c1 b.c1),
   Fp.add (Fp.mul a.c0 b.c1) (Fp.mul a.c1 b.c0)⟩

/-- `2a` in `Fp2`. -/
def dbl (a : Fp2) : Fp2 := ⟨Fp.add a.c0 a.c0, Fp.add a.c1 a.c1⟩

/-- `3a` in `Fp2`. -/
def triple (a : Fp2) : Fp2 := ⟨Fp.add (Fp.add a.c0 a.c0) a.c0, Fp.add (Fp.add a.c1 a.c1) a.c1⟩

/-- `8a` in `Fp2`. -/
def oct (a : Fp2) : Fp2 := dbl (dbl (dbl a))

/-- Conjugation `ā = c0 − c1·u`. -/
def conj (a : Fp2) : Fp2 := ⟨a.c0, Fp.neg a.c1⟩

/-- Multiplication by the quadratic non-residue `u + 1` used by the `Fp6` tower
(`bls12_381-0.7.1/src/fp2.rs:156-166`): `(a + bu)(u+1) = (a − b) + (a + b)u` because `u² = −1`. -/
def mulByNonresidue (a : Fp2) : Fp2 := ⟨Fp.sub a.c0 a.c1, Fp.add a.c0 a.c1⟩

/-- Norm `N(a) = a0² + a1² = a·ā`. -/
def norm (a : Fp2) : Nat := Fp.add (Fp.mul a.c0 a.c0) (Fp.mul a.c1 a.c1)

/-- Inverse by conjugation: `ā = a0 − a1 u`, so `a⁻¹ = ā / N(a)` (`none` for `0`). -/
def inv (a : Fp2) : Option Fp2 :=
  let n := norm a
  if n = 0 then none
  else
    let ni := Fp.inv n
    some ⟨Fp.mul a.c0 ni, Fp.neg (Fp.mul a.c1 ni)⟩

def powAux : Nat → Fp2 → Nat → Fp2
  | 0, _, _ => one
  | f + 1, bb, e =>
    let q := powAux f bb (e / 2)
    if e % 2 = 1 then mul (mul q q) bb else mul q q

def pow (bb : Fp2) (e : Nat) : Fp2 := powAux 400 bb e

/-- `blst`'s `sgn0` for `Fp2` (`no_asm.h:556-575`, `sgn0_pty_mont_384x`): the sign component is
`sgn0(c1)` when `c1 ≠ 0`, else `sgn0(c0)`. -/
def sgn0 (a : Fp2) : Nat := if a.c1 = 0 then Fp.sgn0 a.c0 else Fp.sgn0 a.c1

/-- The IETF `sgn0` *parity* bit for `Fp2` (`no_asm.h:538-554`, `sgn0_pty_mod_384x`'s low bit): the
parity of `c0` when `c0 ≠ 0`, else the parity of `c1`. The SSWU map's sign fix-up uses this
(`map_to_g2.c:226`, `sgn0_fp2`), not the compressed-point sign bit. -/
def parity (a : Fp2) : Nat := if a.c0 = 0 then Fp.parity a.c1 else Fp.parity a.c0

/-- Square root of an `Fp2` element, or `none` when it is not a square. Uses the standard
`p ≡ 3 (mod 4)` complex method (`blst` `sqrt_fp2`, `blst/src/sqrt.c`; the specific root returned is
irrelevant because decompression normalises the sign afterwards):
`if a1 = 0` split by whether `a0` is a square; else `s = sqrt(a0² + a1²)`, `x = (a0 + s)/2`,
`y = a1/(2x)` with the `(a0 − s)/2` branch when `(a0 + s)/2` is not a square. -/
def sqrt (a : Fp2) : Option Fp2 :=
  if a.c1 = 0 then
    if a.c0 = 0 then some zero
    else
      let y := Fp.sqrt a.c0
      if Fp.mul y y = a.c0 then some ⟨y, 0⟩
      else
        -- `-1` is a non-residue (p ≡ 3 mod 4), so `-a0` is a square when `a0` is not
        let y2 := Fp.sqrt (Fp.neg a.c0)
        if Fp.mul y2 y2 = Fp.neg a.c0 then some ⟨0, y2⟩ else none
  else
    let s := Fp.sqrt (norm a)
    if Fp.mul s s ≠ norm a then none
    else
      let twoInv : Nat := Fp.inv 2
      let x0sq := Fp.mul (Fp.add a.c0 s) twoInv
      let x0 := Fp.sqrt x0sq
      if Fp.mul x0 x0 = x0sq ∧ x0 ≠ 0 then
        let x1 := Fp.mul a.c1 (Fp.inv (Fp.mul 2 x0))
        let r : Fp2 := ⟨x0, x1⟩
        if mul r r = a then some r else some (neg r)
      else
        let x0sq' := Fp.mul (Fp.sub a.c0 s) twoInv
        let x0' := Fp.sqrt x0sq'
        if Fp.mul x0' x0' = x0sq' ∧ x0' ≠ 0 then
          let x1' := Fp.mul a.c1 (Fp.inv (Fp.mul 2 x0'))
          let r : Fp2 := ⟨x0', x1'⟩
          if mul r r = a then some r else some (neg r)
        else none

/-- Canonical `c1 ‖ c0` decoding (`read_fp2_point`, `logic/bls12381.rs:417-446`): 96 bytes, both
components `< p`. -/
def ofBE (b : Bytes) : Option Fp2 :=
  if b.length = 96 then
    match Fp.ofBE (b.drop 48), Fp.ofBE (b.take 48) with
    | some c0, some c1 => some ⟨c0, c1⟩
    | _, _ => none
  else none

/-- `c1 ‖ c0` encoding. -/
def toBE (a : Fp2) : Bytes := Fp.toBE a.c1 ++ Fp.toBE a.c0

end Fp2

/-! ## G1: `E(Fp): y² = x³ + 4` -/

/-- The G1 generator (`bls12381.rs` test module and the IETF draft's `BLS12_381_G1`), used by the
tests and by the round-trip lemmas. -/
def G1x : Nat :=
  0x17F1D3A73197D7942695638C4FA9AC0FC3688C4F9774B905A14E3A3F171BAC586C55E83FF97A1AEFFB3AF00ADB22C6BB
def G1y : Nat :=
  0x08B3F481E3AAA0F1A09E30ED741D8AE4FCF5E095D5D00AF600DB18CB2C04B3EDD03CC744A2888AE40CAA232946C5E7E1

/-- G1 point in Jacobian coordinates; `Z = 0` is the point at infinity (`blst`'s `POINTonE1`). -/
structure G1 where
  X : Nat
  Y : Nat
  Z : Nat
  deriving DecidableEq, Repr

namespace G1

def inf : G1 := ⟨0, 0, 0⟩
def ofAffine (x y : Nat) : G1 := ⟨x % p, y % p, 1⟩
def isInf (P : G1) : Bool := P.Z = 0

/-- `blst`'s "is the point at infinity" test for affine coordinates: both coordinates zero
(`POINTonE1_Deserialize_Z`'s infinity encoding is `0x40` followed by zeros). -/
def affIsInf (x y : Nat) : Bool := x % p = 0 ∧ y % p = 0

/-- `y² = x³ + 4` on affine coordinates. -/
def onCurve (x y : Nat) : Bool := Fp.mul y y == Fp.add (Fp.mul (Fp.mul x x) x) 4

/-- `dbl-2009-l` for `a = 0`: `A = X²`, `B = Y²`, `C = B²`, `D = 2((X+B)² − A − C)`,
`E = 3A`, `F = E²`, `X₃ = F − 2D`, `Y₃ = E(D − X₃) − 8C`, `Z₃ = 2YZ`. -/
def dbl (P : G1) : G1 :=
  if P.Z = 0 ∨ P.Y = 0 then inf else
  let A := Fp.mul P.X P.X
  let B := Fp.mul P.Y P.Y
  let C := Fp.mul B B
  let D := Fp.mul 2 (Fp.sub (Fp.sub (Fp.mul (Fp.add P.X B) (Fp.add P.X B)) A) C)
  let E := Fp.mul 3 A
  let F := Fp.mul E E
  let X3 := Fp.sub F (Fp.mul 2 D)
  let Y3 := Fp.sub (Fp.mul E (Fp.sub D X3)) (Fp.mul 8 C)
  let Z3 := Fp.mul 2 (Fp.mul P.Y P.Z)
  ⟨X3, Y3, Z3⟩

/-- `add-2007-bl` for `a = 0` (the generic Jacobian addition; also correct for `a ≠ 0`). -/
def add (P Q : G1) : G1 :=
  if P.Z = 0 then Q else if Q.Z = 0 then P else
  let Z1Z1 := Fp.mul P.Z P.Z
  let Z2Z2 := Fp.mul Q.Z Q.Z
  let U1 := Fp.mul P.X Z2Z2
  let U2 := Fp.mul Q.X Z1Z1
  let S1 := Fp.mul (Fp.mul P.Y Q.Z) Z2Z2
  let S2 := Fp.mul (Fp.mul Q.Y P.Z) Z1Z1
  if U1 = U2 then (if S1 = S2 then dbl P else inf)
  else
    let H := Fp.sub U2 U1
    let I := Fp.mul (Fp.mul 2 H) (Fp.mul 2 H)
    let J := Fp.mul H I
    let r := Fp.mul 2 (Fp.sub S2 S1)
    let V := Fp.mul U1 I
    let X3 := Fp.sub (Fp.sub (Fp.mul r r) J) (Fp.mul 2 V)
    let Y3 := Fp.sub (Fp.mul r (Fp.sub V X3)) (Fp.mul 2 (Fp.mul S1 J))
    let Z3 := Fp.mul (Fp.sub (Fp.sub (Fp.mul (Fp.add P.Z Q.Z) (Fp.add P.Z Q.Z)) Z1Z1) Z2Z2) H
    ⟨X3, Y3, Z3⟩

/-- Negation: `(X, Y, Z) ↦ (X, −Y, Z)`; the point at infinity is its own negative. -/
def neg (P : G1) : G1 := if P.Z = 0 then P else ⟨P.X, Fp.neg P.Y, P.Z⟩

def smulAux : Nat → Nat → G1 → G1
  | 0, _, _ => inf
  | f + 1, k, P =>
    let Q := smulAux f (k / 2) P
    let Q2 := dbl Q
    if k % 2 = 1 then add Q2 P else Q2

/-- MSB-first double-and-add. For `P` in the order-`r` subgroup, `smul k P = [k mod r] P`, which is
what `blst_p1_mult` computes. -/
def smul (k : Nat) (P : G1) : G1 := smulAux 256 k P

/-- Affine coordinates of a finite point (`none` for infinity). -/
def affine? (P : G1) : Option (Nat × Nat) :=
  if P.Z = 0 then none
  else
    let zi := Fp.inv P.Z
    let zi2 := Fp.mul zi zi
    some (Fp.mul P.X zi2, Fp.mul (Fp.mul P.Y zi2) zi)

/-- `blst_p1_in_g1` / `blst_p1_affine_in_g1`'s predicate, as an exact group-theoretic test: for a
point on `E(Fp)`, `[r]P = O` iff `P` is in the order-`r` subgroup. `#E(Fp) = h1 · r` with
`gcd(h1, r) = 1` (verified exactly in the lane log), so `E(Fp)[r]` *is* G1. -/
def inG1 (P : G1) : Bool := isInf (smul r P)

end G1

/-! ## G2: `E'(Fp2): y² = x³ + 4(u+1)` -/

/-- The G2 generator (IETF draft / `bls12381.rs`), in `c0 + c1·u` components. -/
def G2x0 : Nat :=
  0x024AA2B2F08F0A91260805272DC51051C6E47AD4FA403B02B4510B647AE3D1770BAC0326A805BBEFD48056C8C121BDB8
def G2x1 : Nat :=
  0x13E02B6052719F607DACD3A088274F65596BD0D09920B61AB5DA61BBDC7F5049334CF11213945D57E5AC7D055D042B7E
def G2y0 : Nat :=
  0x0CE5D527727D6E118CC9CDC6DA2E351AADFD9BAA8CBDD3A76D429A695160D12C923AC9CC3BACA289E193548608B82801
def G2y1 : Nat :=
  0x0606C4A02EA734CC32ACD2B02BC28B99CB3E287E85A763AF267492AB572E99AB3F370D275CEC1DA1AAA9075FF05F79BE

def G2gen : Fp2 := ⟨G2x0, G2x1⟩
def G2genY : Fp2 := ⟨G2y0, G2y1⟩

/-- G2 point in Jacobian coordinates over `Fp2`; `Z = 0` is infinity. -/
structure G2 where
  X : Fp2
  Y : Fp2
  Z : Fp2
  deriving DecidableEq, Repr

namespace G2

def inf : G2 := ⟨Fp2.zero, Fp2.zero, Fp2.zero⟩
def ofAffine (x y : Fp2) : G2 := ⟨x, y, Fp2.one⟩
def isInf (P : G2) : Bool := P.Z = Fp2.zero
def affIsInf (x y : Fp2) : Bool := x = Fp2.zero ∧ y = Fp2.zero

/-- `4(u+1) = 4 + 4u` (`B_E2` in `blst/src/e2.c:14`). -/
def b2 : Fp2 := ⟨4, 4⟩

def onCurve (x y : Fp2) : Bool :=
  Fp2.mul y y == Fp2.add (Fp2.mul (Fp2.mul x x) x) b2

def dbl (P : G2) : G2 :=
  if P.Z = Fp2.zero ∨ P.Y = Fp2.zero then inf else
  let A := Fp2.mul P.X P.X
  let B := Fp2.mul P.Y P.Y
  let C := Fp2.mul B B
  let D := Fp2.dbl (Fp2.sub (Fp2.sub (Fp2.mul (Fp2.add P.X B) (Fp2.add P.X B)) A) C)
  let E := Fp2.triple A
  let F := Fp2.mul E E
  let X3 := Fp2.sub F (Fp2.dbl D)
  let Y3 := Fp2.sub (Fp2.mul E (Fp2.sub D X3)) (Fp2.oct C)
  let Z3 := Fp2.dbl (Fp2.mul P.Y P.Z)
  ⟨X3, Y3, Z3⟩

def add (P Q : G2) : G2 :=
  if P.Z = Fp2.zero then Q else if Q.Z = Fp2.zero then P else
  let Z1Z1 := Fp2.mul P.Z P.Z
  let Z2Z2 := Fp2.mul Q.Z Q.Z
  let U1 := Fp2.mul P.X Z2Z2
  let U2 := Fp2.mul Q.X Z1Z1
  let S1 := Fp2.mul (Fp2.mul P.Y Q.Z) Z2Z2
  let S2 := Fp2.mul (Fp2.mul Q.Y P.Z) Z1Z1
  if U1 = U2 then (if S1 = S2 then dbl P else inf)
  else
    let H := Fp2.sub U2 U1
    let I := Fp2.mul (Fp2.dbl H) (Fp2.dbl H)
    let J := Fp2.mul H I
    let r := Fp2.dbl (Fp2.sub S2 S1)
    let V := Fp2.mul U1 I
    let X3 := Fp2.sub (Fp2.sub (Fp2.mul r r) J) (Fp2.dbl V)
    let Y3 := Fp2.sub (Fp2.mul r (Fp2.sub V X3)) (Fp2.dbl (Fp2.mul S1 J))
    let Z3 := Fp2.mul (Fp2.sub (Fp2.sub (Fp2.mul (Fp2.add P.Z Q.Z) (Fp2.add P.Z Q.Z)) Z1Z1) Z2Z2) H
    ⟨X3, Y3, Z3⟩

def neg (P : G2) : G2 := if P.Z = Fp2.zero then P else ⟨P.X, Fp2.neg P.Y, P.Z⟩

def smulAux : Nat → Nat → G2 → G2
  | 0, _, _ => inf
  | f + 1, k, P =>
    let Q := smulAux f (k / 2) P
    let Q2 := dbl Q
    if k % 2 = 1 then add Q2 P else Q2

def smul (k : Nat) (P : G2) : G2 := smulAux 256 k P

def affine? (P : G2) : Option (Fp2 × Fp2) :=
  if P.Z = Fp2.zero then none
  else
    match Fp2.inv P.Z with
    | none => none
    | some zi =>
      let zi2 := Fp2.mul zi zi
      some (Fp2.mul P.X zi2, Fp2.mul (Fp2.mul P.Y zi2) zi)

/-- `blst_p2_in_g2`: for a point on the twist, `[r]P = O` iff `P ∈ G2`
(`#E'(Fp2) = h2 · r`, `gcd(h2, r) = 1`, verified exactly in the lane log). -/
def inG2 (P : G2) : Bool := isInf (smul r P)

end G2

/-! ## The `blst` codec, branch by branch

`blst`'s `blst_p1_deserialize` / `blst_p1_uncompress` (`blst/src/e1.c:270-355`) are the only decoders
nearcore calls. The branches nearcore can reach are narrower than blst's, because every host first
rejects an input whose first byte has the top bit set when the argument is an *uncompressed* point
(`parse_p1`/`parse_p2`, `logic/bls12381.rs:120-140`), and first rejects one whose top bit is *clear*
when the argument is a *compressed* point (`p1_decompress`/`p2_decompress`,
`logic/bls12381.rs:203-240`). The functions below are the reachable subsets, named accordingly. -/
namespace Codec

/-! ### G1 -/

/-- Outcome of decoding an *uncompressed* G1 point, i.e. `blst_p1_deserialize` restricted to inputs
whose top bit is clear. `none` is `BLST_BAD_ENCODING` or `BLST_POINT_NOT_ON_CURVE`; the
`(0, ±2)` `BLST_POINT_NOT_IN_GROUP` case is *decoded* here and rejected by the caller, exactly as
`parse_p1` does at `version = 0` (PV86). -/
def decodeG1Uncompressed (b : Bytes) : Option G1 :=
  if b.length ≠ 96 then none
  else
    let in0 := b.getD 0 0
    if in0.toNat &&& 0x80 ≠ 0 then none            -- unreachable in nearcore; blst would uncompress
    else if in0.toNat &&& 0x40 ≠ 0 then
      -- infinity: `0x40` followed by 95 zeros (`POINTonE1_Deserialize_Z`)
      if in0.toNat = 0x40 ∧ b.drop 1 = List.replicate 95 0 then some G1.inf else none
    else
      -- `POINTonE1_Deserialize_BE`: `x ‖ y`, both canonical, on the curve
      match Fp.ofBE (b.take 48), Fp.ofBE (b.drop 48) with
      | some x, some y => if G1.onCurve x y then some (G1.ofAffine x y) else none
      | _, _ => none

/-- The `(0, ±2)` "on the curve but outside G1" case `blst` reports as `BLST_POINT_NOT_IN_GROUP`
(`blst/src/e1.c:288-290`): `x = 0` with a valid `y`. -/
def g1NotInGroup (b : Bytes) : Bool :=
  match decodeG1Uncompressed b with
  | some P => P.X % p = 0
  | none => false

/-- `parse_p1` at a given protocol version (`logic/bls12381.rs:120-140`): decode, then reject the
`(0, ±2)` case unless the NEP-488 fix is active. PV86 has `bls12381_not_in_group_fix = false`
(`parameters.snap:289`), i.e. `version = 0`.

The `(0, ±2)` test is the *affine* `BLST_POINT_NOT_IN_GROUP` return of
`POINTonE1_Deserialize_BE` (`blst/src/e1.c:288-290`), so it applies only to finite points: the
infinity encoding short-circuits to `BLST_SUCCESS` in `POINTonE1_Deserialize_Z` (`e1.c:315-325`)
before that check, hence `P.Z = 0` is always accepted. -/
def parseG1 (b : Bytes) (version : Nat) : Option G1 :=
  match decodeG1Uncompressed b with
  | some P => if version ≥ 1 ∨ P.Z = 0 ∨ P.X % p ≠ 0 then some P else none
  | none => none

/-- `blst_p1_affine_serialize` (`blst/src/e1.c:153-163`): infinity → `0x40` ++ 95 zeros; otherwise
`x ‖ y` as 48-byte big-endian each. -/
def encodeG1Affine (x y : Nat) : Bytes :=
  if G1.affIsInf x y then 0x40 :: List.replicate 95 0
  else Fp.toBE x ++ Fp.toBE y

/-- `blst_p1_to_affine` then `blst_p1_affine_serialize`, the pair `serialize_p1` performs. -/
def encodeG1 (P : G1) : Bytes :=
  match P.affine? with
  | some (x, y) => encodeG1Affine x y
  | none => 0x40 :: List.replicate 95 0

/-- Outcome of decoding a *compressed* G1 point, i.e. `blst_p1_uncompress` (`blst/src/e1.c:243-293`)
restricted to inputs whose top bit is set. `none` covers `BLST_BAD_ENCODING` and
`BLST_POINT_NOT_ON_CURVE`; the `(0, ±2)` `BLST_POINT_NOT_IN_GROUP` case decodes and the caller
rejects it at `version = 0`.

The chosen root is the one whose `blst` sign (`Fp.sgn0`, i.e. `y > (p−1)/2`) equals the encoded sign
bit — a root's two preimages under `sgn0` are complementary because `p` is odd, so this matches
`blst`'s `cneg_fp` normalisation without needing blst's particular `sqrt_fp` output. -/
def decodeG1Compressed (b : Bytes) : Option G1 :=
  if b.length ≠ 48 then none
  else
    let in0 := b.getD 0 0
    if in0.toNat &&& 0x80 = 0 then none
    else if in0.toNat &&& 0x40 ≠ 0 then
      if in0.toNat &&& 0x3f = 0 ∧ b.drop 1 = List.replicate 47 0 then some G1.inf else none
    else
      -- clear the compressed/sign/infinity bits, keeping the low 5 bits of the top byte
      let xb := UInt8.ofNat (in0.toNat &&& 0x1f) :: b.drop 1
      match Fp.ofBE xb with
      | none => none
      | some x =>
        let rhs := Fp.add (Fp.mul (Fp.mul x x) x) 4
        let y0 := Fp.sqrt rhs
        if Fp.mul y0 y0 ≠ rhs then none
        else
          let signBit := (in0.toNat >>> 5) &&& 1
          let y := if Fp.sgn0 y0 = signBit then y0 else Fp.neg y0
          some (G1.ofAffine x y)

/-- `blst`'s `(0, ±2)` test for a compressed G1 input: the decoded point has `x = 0`. -/
def g1CompressedNotInGroup (b : Bytes) : Bool :=
  match decodeG1Compressed b with
  | some P => P.X % p = 0
  | none => false

/-! ### G2 -/

/-- Outcome of decoding an *uncompressed* G2 point (`blst_p2_deserialize`,
`blst/src/e2.c:345-405`), restricted to inputs whose top bit is clear. -/
def decodeG2Uncompressed (b : Bytes) : Option G2 :=
  if b.length ≠ 192 then none
  else
    let in0 := b.getD 0 0
    if in0.toNat &&& 0x80 ≠ 0 then none
    else if in0.toNat &&& 0x40 ≠ 0 then
      if in0.toNat = 0x40 ∧ b.drop 1 = List.replicate 191 0 then some G2.inf else none
    else
      -- `x.c1 ‖ x.c0 ‖ y.c1 ‖ y.c0`
      match Fp.ofBE (b.take 48), Fp.ofBE ((b.drop 48).take 48),
            Fp.ofBE ((b.drop 96).take 48), Fp.ofBE (b.drop 144) with
      | some x1, some x0, some y1, some y0 =>
        let x : Fp2 := ⟨x0, x1⟩
        let y : Fp2 := ⟨y0, y1⟩
        if G2.onCurve x y then some (G2.ofAffine x y) else none
      | _, _, _, _ => none

/-- `blst_p2_affine_serialize` (`blst/src/e2.c:194-205`): infinity → `0x40` ++ 191 zeros;
otherwise `x.c1 ‖ x.c0 ‖ y.c1 ‖ y.c0`. -/
def encodeG2Affine (x y : Fp2) : Bytes :=
  if G2.affIsInf x y then 0x40 :: List.replicate 191 0
  else Fp.toBE x.c1 ++ Fp.toBE x.c0 ++ Fp.toBE y.c1 ++ Fp.toBE y.c0

def encodeG2 (P : G2) : Bytes :=
  match P.affine? with
  | some (x, y) => encodeG2Affine x y
  | none => 0x40 :: List.replicate 191 0

/-- Outcome of decoding a *compressed* G2 point (`blst_p2_uncompress`, `blst/src/e2.c:312-343`),
restricted to inputs whose top bit is set. -/
def decodeG2Compressed (b : Bytes) : Option G2 :=
  if b.length ≠ 96 then none
  else
    let in0 := b.getD 0 0
    if in0.toNat &&& 0x80 = 0 then none
    else if in0.toNat &&& 0x40 ≠ 0 then
      if in0.toNat &&& 0x3f = 0 ∧ b.drop 1 = List.replicate 95 0 then some G2.inf else none
    else
      -- clear the compressed/sign/infinity bits, keeping the low 5 bits of the top byte
      let xb := UInt8.ofNat (in0.toNat &&& 0x1f) :: b.drop 1
      -- `x.c1 ‖ x.c0`; the sign bit describes `y`
      match Fp.ofBE (xb.take 48), Fp.ofBE (xb.drop 48) with
      | some x1, some x0 =>
        let x : Fp2 := ⟨x0, x1⟩
        let rhs := Fp2.add (Fp2.mul (Fp2.mul x x) x) G2.b2
        match Fp2.sqrt rhs with
        | none => none
        | some y0 =>
          let signBit := (in0.toNat >>> 5) &&& 1
          let y := if Fp2.sgn0 y0 = signBit then y0 else Fp2.neg y0
          some (G2.ofAffine x y)
      | _, _ => none

/-- `parse_p2` at a given protocol version (`logic/bls12381.rs:142-160`). `blst_p2_deserialize`'s
`POINT_NOT_IN_GROUP` result only arises for the `(0, ±2)` G1 corner case, which has no G2 analogue
(`blst/src/e2.c:345-405` has no such branch), so the version gate changes nothing for G2 — exactly as
in the source. -/
def parseG2 (b : Bytes) (_version : Nat) : Option G2 :=
  match decodeG2Uncompressed b with
  | some P => some P
  | none => none

end Codec

/-- The protocol version the hosts run at: `bls12381_not_in_group_fix = false` at PV86
(`parameters.snap:289`) selects `version = 0` (`logic/bls12381.rs:17-28`). Kept as a named constant
so the post-NEP-488 behaviour is one edit away. -/
def bls12381Version : Nat := 0

/-! ## The eight register-writing payloads

Each is the `Option<Vec<u8>>` half of a `bls12381_impl!` host: `none` means "return 1 and write
nothing". The length gate is *not* here — the host arm in `Wasm/CryptoHost.lean` owns the
`BLS12381InvalidInput` error and its position in the charge order (`check_input_size` runs after the
read), so these functions receive an input whose length is already known to be a multiple of the
element size. -/

/-- Split a byte string into fixed-size chunks (`blst`'s `chunks_exact`); a trailing partial chunk
is dropped, which the hosts never see because `check_input_size` rejects a non-multiple first. -/
def chunksExact (n : Nat) : Bytes → List Bytes
  | [] => []
  | b => if n = 0 ∨ b.length < n then [] else b.take n :: chunksExact n (b.drop n)
termination_by b => b.length
decreasing_by
  simp only [List.length_drop]
  omega

@[simp] theorem chunksExact_nil (n : Nat) : chunksExact n [] = [] := by
  rw [chunksExact]

/-- `p1_sum` (`logic/bls12381.rs:130-170`): `(sign, P)` pairs, `sign ∈ {0,1}`, sum with negation for
`sign = 1`. A bad sign byte or an undecodable point is `none`. -/
def p1Sum (version : Nat) (d : Bytes) : Option Bytes :=
  let rec go : List Bytes → G1 → Option G1
    | [], acc => some acc
    | item :: rest, acc =>
      match item with
      | [] => none
      | sign :: pt =>
        match Codec.parseG1 pt version with
        | none => none
        | some P =>
          if sign.toNat = 1 then go rest (G1.add acc (G1.neg P))
          else if sign.toNat = 0 then go rest (G1.add acc P)
          else none
  match go (chunksExact 97 d) G1.inf with
  | some P => some (Codec.encodeG1 P)
  | none => none

/-- `p2_sum` (`logic/bls12381.rs:172-215`), the G2 twin. -/
def p2Sum (version : Nat) (d : Bytes) : Option Bytes :=
  let rec go : List Bytes → G2 → Option G2
    | [], acc => some acc
    | item :: rest, acc =>
      match item with
      | [] => none
      | sign :: pt =>
        match Codec.parseG2 pt version with
        | none => none
        | some P =>
          if sign.toNat = 1 then go rest (G2.add acc (G2.neg P))
          else if sign.toNat = 0 then go rest (G2.add acc P)
          else none
  match go (chunksExact 193 d) G2.inf with
  | some P => some (Codec.encodeG2 P)
  | none => none

/-- `g1_multiexp`: `(P, s)` with the 32-byte **little-endian** scalar and the extra subgroup gate
`blst_p1_in_g1` (`logic/bls12381.rs:189-195`). -/
def g1Multiexp (version : Nat) (d : Bytes) : Option Bytes :=
  let rec go : List Bytes → G1 → Option G1
    | [], acc => some acc
    | item :: rest, acc =>
      match Codec.parseG1 (item.take 96) version with
      | none => none
      | some P =>
        if !G1.inG1 P then none
        else
          let s := Bytes.leToNat ((item.drop 96).take 32)
          go rest (G1.add acc (G1.smul s P))
  match go (chunksExact 128 d) G1.inf with
  | some P => some (Codec.encodeG1 P)
  | none => none

/-- `g2_multiexp`, the G2 twin (`logic/bls12381.rs:217-260`). -/
def g2Multiexp (version : Nat) (d : Bytes) : Option Bytes :=
  let rec go : List Bytes → G2 → Option G2
    | [], acc => some acc
    | item :: rest, acc =>
      match Codec.parseG2 (item.take 192) version with
      | none => none
      | some P =>
        if !G2.inG2 P then none
        else
          let s := Bytes.leToNat ((item.drop 192).take 32)
          go rest (G2.add acc (G2.smul s P))
  match go (chunksExact 224 d) G2.inf with
  | some P => some (Codec.encodeG2 P)
  | none => none

/-- `p1_decompress` (`logic/bls12381.rs:203-240`): each 48-byte chunk must have the compressed bit;
the `(0, ±2)` case is rejected at `version = 0` (the `min_pk` wrapper path). -/
def p1Decompress (version : Nat) (d : Bytes) : Option Bytes :=
  let rec go : List Bytes → Bytes → Option Bytes
    | [], acc => some acc
    | item :: rest, acc =>
      match Codec.decodeG1Compressed item with
      | none => none
      -- the `(0, ±2)` not-in-group case needs a *finite* point: `blst`'s
      -- `POINTonE1_Deserialize_Z` returns SUCCESS for the `0x40` infinity encoding before the
      -- affine curve check, and `PublicKey::uncompress` accepts it, so `Z = 0` must not be gated.
      | some P => if version = 0 ∧ P.Z ≠ 0 ∧ P.X % p = 0 then none
                  else go rest (acc ++ Codec.encodeG1 P)
  go (chunksExact 48 d) []

/-- `p2_decompress`, the G2 twin (`logic/bls12381.rs:242-280`). Note that `blst`'s
`POINTonE2_Uncompress_Z` does **not** report the `(0, ±2)` case as not-in-group (there is no such
check in `e2.c:312-343`), so the `version = 0` gate changes nothing for G2 — matching the source. -/
def p2Decompress (_version : Nat) (d : Bytes) : Option Bytes :=
  let rec go : List Bytes → Bytes → Option Bytes
    | [], acc => some acc
    | item :: rest, acc =>
      match Codec.decodeG2Compressed item with
      | none => none
      | some P => go rest (acc ++ Codec.encodeG2 P)
  go (chunksExact 96 d) []

/-! ## The SSWU maps (`map_fp_to_g1`, `map_fp2_to_g2`)

`blst_map_to_g1` / `blst_map_to_g2` (`blst/src/map_to_g1.c:404-420`, `blst/src/map_to_g2.c:372-390`)
are simplified-SWU maps onto the *isogenous* curves `E1': y² = x³ + A'x + B'` and
`E2': y² = x³ + A'x + B'`, followed by the 11-isogeny (G1) / 3-isogeny (G2) onto the real curve and
cofactor clearing by the BLS parameter's structure. This namespace is a literal port in ordinary
modular arithmetic: every constant below is the corresponding C constant converted out of blst's
Montgomery form (`c_mont * R^-1 mod p`), so the same field elements are produced without blst's
representation. Every step is transcribed in the order the C code performs it — including blst's
choice of *which* SSWU root (`x1` when `g(x1)` is square, else `x2`), the `Z`-power weighting of the
isogeny coefficients, and the final sign normalisation against `sgn0(u)` — so the mapped points are
byte-identical to the host's.

Two `sgn0` flavours appear and both are modelled:
* the *sign* bit (`Fp.sgn0`, `Fp2.sgn0`): "greater than `(p-1)/2`"; this is what a compressed point
  carries and what decompression normalises;
* the *parity* bit (`Fp.parity`, `Fp2.parity`): the IETF `sgn0` used by the SSWU sign fix-up in
  `map_to_g1.c:357-359` and `map_to_g2.c:265-267` (`sgn0_pty_mont_384 & 1`, whose bit 0 is the
  parity of `c0` when `c0 != 0`, else of `c1`). -/

namespace Map

/-! ### SSWU parameters and isogeny coefficients -/

/-- `A'` of the 11-isogenous curve `E1': y² = x³ + A'x + B'` (`map_to_g1.c:15-21`, `Aprime_E1`, converted out of Montgomery form). -/
def A1 : Nat := 12190336318893619529228877361869031420615612348429846051986726275283378313155663745811710833465465981901188123677

/-- `B'` of `E1'` (`map_to_g1.c:22-28`, `Bprime_E1`). -/
def B1 : Nat := 2906670324641927570491258158026293881577086121416628140204402091718288198173574630967936031029026176254968826637280

/-- The SSWU non-square `Z = 11` for G1 (`map_to_g1.c:292-296`, `Z`). -/
def Z1 : Nat := 11

/-- `−A'` for G1 (`map_to_g1.c:287-291`, `minus_A`). -/
def minusA1 : Nat := 3990219218902773773888560948374035125136267207590578039280071409848748272177682200696875918295550198055993084436110

/-- `Z·A'` for G1 (`map_to_g1.c:302-306`, `ZxA`), substituted when `−A'·tv2` vanishes. -/
def ZxA1 : Nat := 134093699507829814821517650980559345626771735832728306571853989028117161444712301203928819168120125800913069360447

/-- `sqrt(−Z³)` for G1 (`map_to_g1.c:297-301`, `sqrt_minus_ZZZ`). -/
def sqrtMinusZ3 : Nat := 590728492726997966099618626120482682095437733689734941576187760067601492637096712773899690116980580577616657575925

/-- `x`-numerator of the 11-isogeny: 12 coefficients, degree 11 (`map_to_g1.c:56-98`). -/
def g1IsogenyXNum : List Nat := [
  2712959285290305970661081772124144179193819192423276218370281158706191519995889425075952244140278856085036081760695,
  3564859427549639835253027846704205725951033235539816243131874237388832081954622352624080767121604606753339903542203,
  2051387046688339481714726479723076305756384619135044672831882917686431912682625619320120082313093891743187631791280,
  3612713941521031012780325893181011392520079402153354595775735142359240110423346445050803899623018402874731133626465,
  2247053637822768981792833880270996398470828564809439728372634811976089874056583714987807553397615562273407692740057,
  3415427104483187489859740871640064348492611444552862448295571438270821994900526625562705192993481400731539293415811,
  2067521456483432583860405634125513059912765526223015704616050604591207046392807563217109432457129564962571408764292,
  3650721292069012982822225637849018828271936405382082649291891245623305084633066170122780668657208923883092359301262,
  1239271775787030039269460763652455868148971086016832054354147730155061349388626624328773377658494412538595239256855,
  3479374185711034293956731583912244564891370843071137483962415222733470401948838363051960066766720884717833231600798,
  2492756312273161536685660027440158956721981129429869601638362407515627529461742974364729223659746272460004902959995,
  1058488477413994682556770863004536636444795456512795473806825292198091015005841418695586811009326456605062948114985,
]

/-- `x`-denominator of the 11-isogeny: 10 coefficients, degree 10 with leading `x¹⁰ = 1` (`map_to_g1.c:99-118`). -/
def g1IsogenyXDen : List Nat := [
  1353092447850172218905095041059784486169131709710991428415161466575141675351394082965234118340787683181925558786844,
  2822220997908397120956501031591772354860004534930174057793539372552395729721474912921980407622851861692773516917759,
  1717937747208385987946072944131378949849282930538642983149296304709633281382731764122371874602115081850953846504985,
  501624051089734157816582944025690868317536915684467868346388760435016044027032505306995281054569109955275640941784,
  3025903087998593826923738290305187197829899948335370692927241015584233559365859980023579293766193297662657497834014,
  2224140216975189437834161136818943039444741035168992629437640302964164227138031844090123490881551522278632040105125,
  1146414465848284837484508420047674663876992808692209238763293935905506532411661921697047880549716175045414621825594,
  3179090966864399634396993677377903383656908036827452986467581478509513058347781039562481806409014718357094150199902,
  1549317016540628014674302140786462938410429359529923207442151939696344988707002602944342203885692366490121021806145,
  1442797143427491432630626390066422021593505165588630398337491100088557278058060064930663878153124164818522816175370,
]

/-- `y`-numerator of the 11-isogeny: 16 coefficients, degree 15 (`map_to_g1.c:124-160`). -/
def g1IsogenyYNum : List Nat := [
  1393399195776646641963150658816615410692049723305861307490980409834842911816308830479576739332720113414154429643571,
  2968610969752762946134106091152102846225411740689724909058016729455736597929366401532929068084731548131227395540630,
  122933100683284845219599644396874530871261396084070222155796123161881094323788483360414289333111221370374027338230,
  303251954782077855462083823228569901064301365507057490567314302006681283228886645653148231378803311079384246777035,
  1353972356724735644398279028378555627591260676383150667237975415318226973994509601413730187583692624416197017403099,
  3443977503653895028417260979421240655844034880950251104724609885224259484262346958661845148165419691583810082940400,
  718493410301850496156792713845282235942975872282052335612908458061560958159410402177452633054233549648465863759602,
  1466864076415884313141727877156167508644960317046160398342634861648153052436926062434809922037623519108138661903145,
  1536886493137106337339531461344158973554574987550750910027365237255347020572858445054025958480906372033954157667719,
  2171468288973248519912068884667133903101171670397991979582205855298465414047741472281361964966463442016062407908400,
  3915937073730221072189646057898966011292434045388986394373682715266664498392389619761133407846638689998746172899634,
  3802409194827407598156407709510350851173404795262202653149767739163117554648574333789388883640862266596657730112910,
  1707589313757812493102695021134258021969283151093981498394095062397393499601961942449581422761005023512037430861560,
  349697005987545415860583335313370109325490073856352967581197273584891698473628451945217286148025358795756956811571,
  885704436476567581377743161796735879083481447641210566405057346859953524538988296201011389016649354976986251207243,
  3370924952219000111210625390420697640496067348723987858345031683392215988129398381698161406651860675722373763741188,
]

/-- `y`-denominator of the 11-isogeny: 15 coefficients, degree 14 (`map_to_g1.c:161-190`). -/
def g1IsogenyYDen : List Nat := [
  3396434800020507717552209507749485772788165484415495716688989613875369612529138640646200921379825018840894888371137,
  3907278185868397906991868466757978732688957419873771881240086730384895060595583602347317992689443299391009456758845,
  854914566454823955479427412036002165304466268547334760894270240966182605542146252771872707010378658178126128834546,
  3496628876382137961119423566187258795236027183112131017519536056628828830323846696121917502443333849318934945158166,
  1828256966233331991927609917644344011503610008134915752990581590799656305331275863706710232159635159092657073225757,
  1362317127649143894542621413133849052553333099883364300946623208643344298804722863920546222860227051989127113848748,
  3443845896188810583748698342858554856823966611538932245284665132724280883115455093457486044009395063504744802318172,
  3484671274283470572728732863557945897902920439975203610275006103818288159899345245633896492713412187296754791689945,
  3755735109429418587065437067067640634211015783636675372165599470771975919172394156249639331555277748466603540045130,
  3459661102222301807083870307127272890283709299202626530836335779816726101522661683404130556379097384249447658110805,
  742483168411032072323733249644347333168432665415341249073150659015707795549260947228694495111018381111866512337576,
  1662231279858095762833829698537304807741442669992646287950513237989158777254081548205552083108208170765474149568658,
  1668238650112823419388205992952852912407572045257706138925379268508860023191233729074751042562151098884528280913356,
  369162719928976119195087327055926326601627748362769544198813069133429557026740823593067700396825489145575282378487,
  2164195715141237148945939585099633032390257748382945597506236650132835917087090097395995817229686247227784224263055,
]

/-- `A' = 240i` for `E2'` (`map_to_g2.c:15-21`, `Aprime_E2`). -/
def A2 : Fp2 := ⟨0, 240⟩

/-- `B' = 1012 + 1012i` for `E2'` (`map_to_g2.c:22-30`, `Bprime_E2`). -/
def B2 : Fp2 := ⟨1012, 1012⟩

/-- The SSWU non-square `Z = −2 − i` for G2 (`map_to_g2.c:229-238`, `Z`). -/
def Z2 : Fp2 := ⟨4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559785, 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559786⟩

/-- `−A'` for G2 (`map_to_g2.c:225-229`, `minus_A`). -/
def minusA2 : Fp2 := ⟨0, 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559547⟩

/-- `Z·A'` for G2 (`map_to_g2.c:245-252`, `ZxA`). -/
def ZxA2 : Fp2 := ⟨240, 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559307⟩

/-- `1/(1+i)^((p−1)/3)`, the `X` factor of the `Ψ` endomorphism (`blst/src/e2.c:457-464`,
`frobenius_x`, in blst's `c0 + c1·u` order — the C constant's first limb group is the *imaginary*
part, matching `vec384x`'s layout). -/
def psiX : Fp2 := ⟨0, 0x1a0111ea397fe699ec02408663d4de85aa0d857d89759ad4897d29650fb85f9b409427eb4f49fffd8bfd00000000aaad⟩

/-- `1/(1+i)^((p−1)/2)`, the `Y` factor of `Ψ` (`blst/src/e2.c:465-476`, `frobenius_y`). -/
def psiY : Fp2 :=
  ⟨0x135203e60180a68ee2e9c448d77a2cd91c3dedd930b1cf60ef396489f61eb45e304466cf3e67fa0af1ee7b04121bdea2,
   0x6af0e0437ff400b6831e36d6bd17ffe48395dabc2d3435e77f76e17009241c5ee67992f72ec05f4c81084fbede3cc09⟩

/-- `x`-numerator of the 3-isogeny: 4 coefficients, degree 3 (`map_to_g2.c:51-66`). -/
def g2IsogenyXNum : List Fp2 := [
  ⟨889424345604814976315064405719089812568196182208668418962679585805340366775741747653930584250892369786198727235542, 889424345604814976315064405719089812568196182208668418962679585805340366775741747653930584250892369786198727235542⟩,
  ⟨0, 2668273036814444928945193217157269437704588546626005256888038757416021100327225242961791752752677109358596181706522⟩,
  ⟨2668273036814444928945193217157269437704588546626005256888038757416021100327225242961791752752677109358596181706526, 1334136518407222464472596608578634718852294273313002628444019378708010550163612621480895876376338554679298090853261⟩,
  ⟨3557697382419259905260257622876359250272784728834673675850718343221361467102966990615722337003569479144794908942033, 0⟩,
]

/-- `x`-denominator of the 3-isogeny: 2 coefficients, degree 2 with leading `x² = 1` (`map_to_g2.c:67-78`). -/
def g2IsogenyXDen : List Fp2 := [
  ⟨0, 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559715⟩,
  ⟨12, 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559775⟩,
]

/-- `y`-numerator of the 3-isogeny: 4 coefficients, degree 3 (`map_to_g2.c:79-97`). -/
def g2IsogenyYNum : List Fp2 := [
  ⟨3261222600550988246488569487636662646083386001431784202863158481286248011511053074731078808919938689216061999863558, 3261222600550988246488569487636662646083386001431784202863158481286248011511053074731078808919938689216061999863558⟩,
  ⟨0, 889424345604814976315064405719089812568196182208668418962679585805340366775741747653930584250892369786198727235518⟩,
  ⟨2668273036814444928945193217157269437704588546626005256888038757416021100327225242961791752752677109358596181706524, 1334136518407222464472596608578634718852294273313002628444019378708010550163612621480895876376338554679298090853263⟩,
  ⟨2816510427748580758331037284777117739799287910327449993381818688383577828123182200904113516794492504322962636245776, 0⟩,
]

/-- `y`-denominator of the 3-isogeny: 3 coefficients, degree 2 (`map_to_g2.c:98-121`). -/
def g2IsogenyYDen : List Fp2 := [
  ⟨4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559355, 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559355⟩,
  ⟨0, 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559571⟩,
  ⟨18, 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559769⟩,
]

/-! ### SSWU onto the isogenous curves -/

/-- `Z`-powers in `blst`'s descending layout for G1 (`map_to_g1.c:222-240`): index `j` holds
`Z^(2·(15−j))`, so `j = 14` is `Z²` and `j = 0` is `Z³⁰`. -/
def g1ZPows (Z : Nat) : List Nat := (List.range 15).map (fun j => Fp.pow Z (2 * (15 - j)))

/-- `Z`-powers in `blst`'s descending layout for G2 (`map_to_g2.c:135-139`): index `j` holds
`Z^(2·(3−j))`, so `j = 2` is `Z²` and `j = 0` is `Z⁶`. -/
def g2ZPows (Z : Fp2) : List Fp2 := (List.range 3).map (fun j => Fp2.pow Z (2 * (3 - j)))

/-- `map_fp(acc, x, map, n)` (`map_to_g1.c:40-46`): Horner over `n` weighted coefficients, the
highest first. -/
def horner (acc x : Nat) (ms : List Nat) : Nat := ms.foldl (fun a c => Fp.add (Fp.mul a x) c) acc

/-- `map_fp2`'s Horner (`map_to_g2.c:28-34`), the `Fp2` twin of `horner`. -/
def horner2 (acc x : Fp2) (ms : List Fp2) : Fp2 := ms.foldl (fun a c => Fp2.add (Fp2.mul a x) c) acc

/-- The G1 SSWU point on `E1': y² = x³ + A'x + B'`, in the Jacobian coordinates
`blst`'s `map_to_isogenous_E1` builds (`map_to_g1.c:307-380`): `(xn·xd, y·gxd, xd)` with
`gxd = xd³`.

`blst` picks `x1 = x1n/xd` when `g(x1)` is a square and `x2 = Z·u²·x1` otherwise (`vec_select`
keeps its *first* argument when the mask is set, so `vec_select(xn, x1n, x2n, e2)` is `e2 ? x1n :
x2n` with `e2 = "tv4 is a square"`). The chosen `y` is negated when its IETF parity differs from
`u`'s (`cneg_fp`, `map_to_g1.c:366-368`), which fixes the sign without depending on which square
root `sqrt` returned. -/
def sswuG1 (u : Nat) : G1 :=
  let uu := Fp.mul u u
  let zuu := Fp.mul Z1 uu
  let tv2 := Fp.add (Fp.mul zuu zuu) zuu
  let x1n := Fp.mul (Fp.add tv2 1) B1
  let x2n := Fp.mul zuu x1n
  let xd0 := Fp.mul (Fp.neg A1) tv2
  let xd := if xd0 = 0 then ZxA1 else xd0
  let gxd := Fp.mul xd (Fp.mul xd xd)
  let xd2 := Fp.mul xd xd
  -- `gx1 = x1n³ + A'·x1n·xd² + B'·xd³`, the `x1` candidate's un-normalised `g`
  let gx1 := Fp.add (Fp.add (Fp.mul (Fp.mul x1n x1n) x1n) (Fp.mul A1 (Fp.mul x1n xd2)))
    (Fp.mul B1 gxd)
  let gx1aff := Fp.mul gx1 (Fp.inv gxd)
  let s := Fp.sqrt gx1aff
  let isSq := Fp.mul s s = gx1aff
  let x2aff := Fp.mul x2n (Fp.inv xd)
  let gx2aff := Fp.add (Fp.add (Fp.mul (Fp.mul x2aff x2aff) x2aff) (Fp.mul A1 x2aff)) B1
  let s2 := Fp.sqrt gx2aff
  let y := if isSq then (if Fp.parity s = Fp.parity u then s else Fp.neg s)
           else (if Fp.parity s2 = Fp.parity u then s2 else Fp.neg s2)
  let xn := if isSq then x1n else x2n
  ⟨Fp.mul xn xd, Fp.mul y gxd, xd⟩

/-- The 11-isogeny `E1' → E1` (`map_to_g1.c:49-273`), transcribed with `blst`'s `Z`-power
weighting and its Jacobian output convention
`(Z, X, Y) = (xd·yd, xn·yd·Z, Z²·xd·yn)`. -/
def isoG1 (P : G1) : G1 :=
  if P.Z = 0 then G1.inf else
  let X := P.X
  let Y := P.Y
  let Z := P.Z
  let z := g1ZPows Z
  -- x numerator: coefficients 0..10 weighted by `Zz[4+i]`, then Horner down to 0
  let xm := (List.range 11).map (fun i => Fp.mul (g1IsogenyXNum.getD i 0) (z.getD (4 + i) 0))
  let xn := horner (Fp.add (Fp.mul X (g1IsogenyXNum.getD 11 0)) (xm.getD 10 0)) X
    ((xm.take 10).reverse)
  -- x denominator: coefficients 0..9 weighted by `Zz[5+i]`, leading `x¹⁰` unweighted, times `Z²`
  let xm2 := (List.range 10).map (fun i => Fp.mul (g1IsogenyXDen.getD i 0) (z.getD (5 + i) 0))
  let xd := Fp.mul (horner (Fp.add X (xm2.getD 9 0)) X ((xm2.take 9).reverse)) (z.getD 14 0)
  -- y numerator: coefficients 0..14 weighted by `Zz[i]`, times the input's `Y`
  let ym := (List.range 15).map (fun i => Fp.mul (g1IsogenyYNum.getD i 0) (z.getD i 0))
  let yn := Fp.mul (horner (Fp.add (Fp.mul X (g1IsogenyYNum.getD 15 0)) (ym.getD 14 0)) X
    ((ym.take 14).reverse)) Y
  -- y denominator: coefficients 0..14 weighted by `Zz[i]`, times `Z³`
  let ym2 := (List.range 15).map (fun i => Fp.mul (g1IsogenyYDen.getD i 0) (z.getD i 0))
  let yd := Fp.mul (horner (Fp.add X (ym2.getD 14 0)) X ((ym2.take 14).reverse))
    (Fp.mul (z.getD 14 0) Z)
  let Zout := Fp.mul xd yd
  ⟨Fp.mul (Fp.mul xn yd) Zout, Fp.mul (Fp.mul (Fp.mul Zout Zout) xd) yn, Zout⟩

/-- **`blst_map_to_g1`'s output for one `Fp` element** (`map_to_g1.c:404-420`): SSWU onto `E1'`, the
11-isogeny onto `E`, then cofactor clearing by `1 − z = 0xd201000000010001`
(`POINTonE1_times_minus_z` computes `[|z|]P` and the following `dadd` adds `P`, so the pair is one
scalar multiplication by `|z| + 1`). The result is in G1. -/
def mapToG1 (u : Nat) : G1 := G1.smul 0xd201000000010001 (isoG1 (sswuG1 u))

/-- The `Ψ` endomorphism of `E'(Fp²)` (`blst/src/e2.c:455-482`, `psi`): conjugate each coordinate
and scale `X`, `Y` by `1/(1+i)^((p−1)/3)` and `1/(1+i)^((p−1)/2)` respectively. -/
def psiG2 (P : G2) : G2 :=
  ⟨Fp2.mul (Fp2.conj P.X) psiX, Fp2.mul (Fp2.conj P.Y) psiY, Fp2.conj P.Z⟩

/-- `Ψ²(2P) − P − Ψ(P) + [|z|]([|z|+1]P − Ψ(P))` — the G2 cofactor clearing of
`blst/src/map_to_g2.c:330-350` (`clear_cofactor`, "A. Budroni, F. Pintore, Efficient hash maps to
G2 on BLS curves"). -/
def clearCofactorG2 (P : G2) : G2 :=
  let out0 := psiG2 (psiG2 (G2.dbl P))
  let t0 := G2.neg P
  let t1 := psiG2 t0
  let out1 := G2.add (G2.add out0 t0) t1
  let u0 := G2.add (G2.smul 0xd201000000010000 P) P
  let u0' := G2.add u0 t1
  G2.add out1 (G2.smul 0xd201000000010000 u0')

/-- The G2 SSWU point on `E2'`, in the Jacobian coordinates of `map_to_isogenous_E2`
(`map_to_g2.c:240-310`): `(xn·xd, y·gxd, xd)`. As in G1 the candidate is `x1` when `g(x1)` is a
square, else `x2`, and the sign is normalised against the IETF parity of `u`. -/
def sswuG2 (u : Fp2) : G2 :=
  let uu := Fp2.mul u u
  let zuu := Fp2.mul Z2 uu
  let tv2 := Fp2.add (Fp2.mul zuu zuu) zuu
  let x1n := Fp2.mul (Fp2.add tv2 Fp2.one) B2
  let x2n := Fp2.mul zuu x1n
  let xd0 := Fp2.mul minusA2 tv2
  let xd := if xd0 = Fp2.zero then ZxA2 else xd0
  let gxd := Fp2.mul xd (Fp2.mul xd xd)
  let xd2 := Fp2.mul xd xd
  let gx1 := Fp2.add (Fp2.add (Fp2.mul (Fp2.mul x1n x1n) x1n) (Fp2.mul A2 (Fp2.mul x1n xd2)))
    (Fp2.mul B2 gxd)
  let gx1aff := Fp2.mul gx1 ((Fp2.inv gxd).getD Fp2.zero)
  let s? := Fp2.sqrt gx1aff
  let isSq := match s? with
    | some s => Fp2.mul s s = gx1aff
    | none => false
  if isSq = true then
    let s := s?.getD Fp2.zero
    let y := if Fp2.parity s = Fp2.parity u then s else Fp2.neg s
    ⟨Fp2.mul x1n xd, Fp2.mul y gxd, xd⟩
  else
    let x2aff := Fp2.mul x2n ((Fp2.inv xd).getD Fp2.zero)
    let gx2aff := Fp2.add (Fp2.add (Fp2.mul (Fp2.mul x2aff x2aff) x2aff) (Fp2.mul A2 x2aff)) B2
    match Fp2.sqrt gx2aff with
    | some s2 =>
      let y := if Fp2.parity s2 = Fp2.parity u then s2 else Fp2.neg s2
      ⟨Fp2.mul x2n xd, Fp2.mul y gxd, xd⟩
    | none => G2.inf

/-- The 3-isogeny `E2' → E2` (`map_to_g2.c:31-166`), with the same `Z`-power weighting and Jacobian
output convention as `isoG1`. -/
def isoG2 (P : G2) : G2 :=
  if P.Z = Fp2.zero then G2.inf else
  let X := P.X
  let Y := P.Y
  let Z := P.Z
  let z := g2ZPows Z
  let xm := (List.range 3).map (fun i => Fp2.mul (g2IsogenyXNum.getD i Fp2.zero) (z.getD i Fp2.zero))
  let xn := horner2 (Fp2.add (Fp2.mul X (g2IsogenyXNum.getD 3 Fp2.zero)) (xm.getD 2 Fp2.zero)) X
    ((xm.take 2).reverse)
  let xm2 := (List.range 2).map (fun i => Fp2.mul (g2IsogenyXDen.getD i Fp2.zero) (z.getD (1 + i) Fp2.zero))
  let xd := Fp2.mul (horner2 (Fp2.add X (xm2.getD 1 Fp2.zero)) X ((xm2.take 1).reverse)) (z.getD 2 Fp2.zero)
  let ym := (List.range 3).map (fun i => Fp2.mul (g2IsogenyYNum.getD i Fp2.zero) (z.getD i Fp2.zero))
  let yn := Fp2.mul (horner2 (Fp2.add (Fp2.mul X (g2IsogenyYNum.getD 3 Fp2.zero)) (ym.getD 2 Fp2.zero))
    X ((ym.take 2).reverse)) Y
  let ym2 := (List.range 3).map (fun i => Fp2.mul (g2IsogenyYDen.getD i Fp2.zero) (z.getD i Fp2.zero))
  let yd := Fp2.mul (horner2 (Fp2.add X (ym2.getD 2 Fp2.zero)) X ((ym2.take 2).reverse))
    (Fp2.mul (z.getD 2 Fp2.zero) Z)
  let Zout := Fp2.mul xd yd
  ⟨Fp2.mul (Fp2.mul xn yd) Zout, Fp2.mul (Fp2.mul (Fp2.mul Zout Zout) xd) yn, Zout⟩

/-- **`blst_map_to_g2`'s output for one `Fp2` element** (`map_to_g2.c:372-390`): SSWU onto `E2'`, the
3-isogeny onto `E'`, then the `Ψ`-based cofactor clearing. -/
def mapToG2 (u : Fp2) : G2 := clearCofactorG2 (isoG2 (sswuG2 u))

end Map

/-! ## The two map payloads (`map_fp_to_g1`, `map_fp2_to_g2`)

`logic/bls12381.rs:246-262`: per element, `read_fp_point` / `read_fp2_point` — the canonical
big-endian round trip, which is exactly `Fp.ofBE` / `Fp2.ofBE` — then `blst_map_to_g1` /
`blst_map_to_g2` and the ordinary affine serializer. `none` when an element is not canonical. -/

/-- `map_fp_to_g1`: one 96-byte G1 point per 48-byte canonical `Fp` element. -/
def mapFpToG1 (d : Bytes) : Option Bytes :=
  let rec go : List Bytes → Bytes → Option Bytes
    | [], acc => some acc
    | item :: rest, acc =>
      match Fp.ofBE item with
      | none => none
      | some u => go rest (acc ++ Codec.encodeG1 (Map.mapToG1 u))
  go (chunksExact 48 d) []

/-- `map_fp2_to_g2`: one 192-byte G2 point per 96-byte canonical `Fp2` element. -/
def mapFp2ToG2 (d : Bytes) : Option Bytes :=
  let rec go : List Bytes → Bytes → Option Bytes
    | [], acc => some acc
    | item :: rest, acc =>
      match Fp2.ofBE item with
      | none => none
      | some u => go rest (acc ++ Codec.encodeG2 (Map.mapToG2 u))
  go (chunksExact 96 d) []

/-! ## Axiom-free lemmas

The structural facts the hosts rest on. Each is closed by kernel reduction over concrete values or
by definitional equality; no axiom beyond Lean's own kernel is used. The subgroup predicate
`G1.inG1`/`G2.inG2` needs 255 scalar doublings and is therefore tested against the oracle rather
than kernel-reduced. -/

namespace Lemmas

/-- `p ≡ 3 (mod 4)`, which is why `Fp.sqrt a = a^((p+1)/4)` returns a square root. -/
theorem p_mod_four : p % 4 = 3 := by decide

/-- `r > 0`, so the subgroup test `smul r P` is a genuine 255-bit multiplication. -/
theorem r_pos : 0 < r := by decide

theorem h1_pos : 0 < h1 := by decide

theorem h2_pos : 0 < h2 := by decide

/-- The G1 generator satisfies `y² = x³ + 4`. -/
theorem G1_gen_on_curve : G1.onCurve G1x G1y = true := by decide

/-- The G2 generator satisfies `y² = x³ + 4(u+1)`. -/
theorem G2_gen_on_curve : G2.onCurve G2gen G2genY = true := by decide

/-- `p` fits in 48 bytes, so every canonical `Fp` encoding is exactly one 48-byte element. -/
theorem p_lt_256_48 : p < 256 ^ 48 := by decide

/-- A canonical `Fp` value encodes into 48 bytes. -/
theorem toBE_length {x : Nat} : (Fp.toBE x).length = 48 := Bytes.beN_length 48 x

/-- `Fp.ofBE` inverts `Fp.toBE` on canonical values: the 48-byte big-endian encoding decodes back to
the same field element. This is the codec round trip the uncompressed readers depend on. -/
theorem ofBE_toBE {x : Nat} (hx : x < p) : Fp.ofBE (Fp.toBE x) = some x := by
  have hp : p < 256 ^ 48 := by decide
  have hlt : x % 256 ^ 48 = x := Nat.mod_eq_of_lt (by omega)
  unfold Fp.ofBE Fp.toBE
  have hlen : (Bytes.beN 48 x).length = 48 := Bytes.beN_length 48 x
  rw [hlen, Bytes.beToNat_beN, hlt]
  simp [hx]

/-- Every 48-byte big-endian string decodes to a value `< 256^48`; combined with `ofBE`'s `< p`
gate, a decoded value is always canonical. -/
theorem ofBE_lt {b : Bytes} {x : Nat} (h : Fp.ofBE b = some x) : x < p := by
  unfold Fp.ofBE at h
  by_cases hlen : b.length = 48
  · simp only [hlen, ite_true] at h
    by_cases hcanon : Bytes.beToNat b < p
    · simp only [hcanon, ite_true] at h
      exact Option.some.inj h ▸ hcanon
    · simp only [hcanon, ite_false] at h
      exact absurd h (by simp)
  · simp only [hlen, ite_false] at h
    exact absurd h (by simp)

/-- The empty `p1_sum` input is the identity, encoded as the 96-byte infinity form. -/
theorem p1Sum_nil : p1Sum bls12381Version [] = some (0x40 :: List.replicate 95 0) := by
  simp only [p1Sum, bls12381Version, chunksExact_nil]
  rfl

/-- The empty `p2_sum` input is the identity, encoded as the 192-byte infinity form. -/
theorem p2Sum_nil : p2Sum bls12381Version [] = some (0x40 :: List.replicate 191 0) := by
  simp only [p2Sum, bls12381Version, chunksExact_nil]
  rfl

/-- The empty `p1_decompress` input writes an empty register. -/
theorem p1Decompress_nil : p1Decompress bls12381Version [] = some [] := by
  rw [p1Decompress, chunksExact_nil]
  rfl

/-- The empty `p2_decompress` input writes an empty register. -/
theorem p2Decompress_nil : p2Decompress bls12381Version [] = some [] := by
  rw [p2Decompress, chunksExact_nil]
  rfl

/-- The empty `map_fp_to_g1` input writes an empty register. -/
theorem mapFpToG1_nil : mapFpToG1 [] = some [] := by
  rw [mapFpToG1, chunksExact_nil]
  rfl

/-- The empty `map_fp2_to_g2` input writes an empty register. -/
theorem mapFp2ToG2_nil : mapFp2ToG2 [] = some [] := by
  rw [mapFp2ToG2, chunksExact_nil]
  rfl

end Lemmas

end BLS12381
end NearSpecV3
