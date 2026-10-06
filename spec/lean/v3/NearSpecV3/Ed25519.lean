import ArenaCore.Bytes
import NearSpecV3.SHA512

/-!
# Ed25519 signature verification as performed by nearcore

Leaf module of `near/pv86/chunk-validation/v0` (domain D1, signed transactions).
`Ed25519.verify pk sig msg` is the Boolean that nearcore computes for
`Signature::ED25519(ed25519_dalek::Signature::from_bytes(sig)).verify(msg, &PublicKey::ED25519(pk))`
with nearcore pinned at `44f7ae6cd7ef08bab604e20a473bf77e35d4c993`, ed25519-dalek 2.2.0
(features `hazmat`, `rand_core`; **not** `legacy_compatibility`), ed25519 2.2.3,
curve25519-dalek 4.1.3. `sigEncodingOk sig` is nearcore's separate Borsh-decoding
check on the signature bytes; it is *not* part of `verify`.

## Source semantics (each point re-read in the pinned sources)

| # | rule | source |
|---|------|--------|
| 1 | `Signature::verify` (ED25519, ED25519): `VerifyingKey::from_bytes(pk)`; `Err` ⇒ `false`; else `verify(data, sig).is_ok()` | nearcore `core/crypto/src/signature.rs:1086-1093` |
| 2 | Borsh decoding of an ED25519 signature rejects `sig[63] & 0b1110_0000 ≠ 0`, then `ed25519_dalek::Signature::from_bytes` (infallible) | nearcore `core/crypto/src/signature.rs:1174-1183` → `sigEncodingOk` |
| 3 | `ed25519::Signature::from_bytes` / `to_bytes` store and return `R = sig[0..32]`, `s = sig[32..64]` verbatim | ed25519-2.2.3 `src/lib.rs:313-322, 351-357` |
| 4 | `VerifyingKey::from_bytes(pk)` = `CompressedEdwardsY(pk).decompress()`, keeps the original 32 bytes as `compressed` | ed25519-dalek-2.2.0 `src/verifying.rs:165-174` |
| 5 | decompress: `Y = FieldElement::from_bytes(pk)` (bit 255 masked off, value **not** required `< p`: non-canonical `y ∈ [p, 2^255)` is accepted and used mod `p`); `u = Y²−1`, `v = d·Y²+1`; `(ok, X) = sqrt_ratio_i(u, v)`; `None` unless `ok` | curve25519-dalek-4.1.3 `src/edwards.rs:194-220`; `src/backend/serial/u64/field.rs:338-363` |
| 6 | `sqrt_ratio_i(u,v)`: `r = (u v³)(u v⁷)^((p−5)/8)`, `check = v r²`; `check = u` ⇒ ok with `r`; `check = −u` ⇒ ok with `r·√−1`; otherwise not ok (incl. `check = −u·√−1`); finally `r := |r|`, negated iff its canonical encoding is odd ("nonnegative root"). `u = 0` gives `r = 0`, `check = 0 = u` ⇒ ok | curve25519-dalek-4.1.3 `src/field.rs:243-289`, `is_negative` `:101-104` |
| 7 | `X.conditional_negate(pk[31] >> 7)`: `x = 0` with sign bit 1 is **accepted** (`−0 = 0`); `T = X·Y`, `Z = 1` | curve25519-dalek-4.1.3 `src/edwards.rs:223-241` |
| 8 | `raw_verify`: `InternalSignature::try_from(sig)` then `RCompute::compute`; accept iff the recomputed **compressed** `R` equals `signature.R` byte-for-byte (R is never decompressed; a non-canonical R encoding never matches) | ed25519-dalek-2.2.0 `src/verifying.rs:201-218`; `Verifier::verify` = `raw_verify::<Sha512>` `:563-565` |
| 9 | `InternalSignature::from_bytes`: `s = check_scalar(sig[32..64])` = `Scalar::from_canonical_bytes`: requires bit 255 clear **and** `s` canonical, i.e. `LE(s) < ℓ` | ed25519-dalek-2.2.0 `src/signature.rs:89-96, 151-163`; curve25519-dalek-4.1.3 `src/scalar.rs:261-265, 1125-1136` |
| 10 | `k = Scalar::from_hash(SHA-512(R_bytes ‖ A.compressed ‖ M))` = `LE(digest) mod ℓ` (`A.compressed` = the original, possibly non-canonical, pk bytes) | ed25519-dalek-2.2.0 `src/verifying.rs:521-559`; curve25519-dalek-4.1.3 `src/scalar.rs:250-252, 671-678` |
| 11 | `R' = vartime_double_scalar_mul_basepoint(k, −A, s) = [k](−A) + [s]B` (cofactorless; exact group arithmetic on all of `E(𝔽_p)`, small-order / mixed-order `A` allowed), then `compress`: `y = Y/Z` canonical LE bytes, bit 255 := LSB of canonical `x = X/Z` | ed25519-dalek-2.2.0 `src/verifying.rs:552-559`; curve25519-dalek-4.1.3 `src/edwards.rs:566-575, 902-908` |

Lengths: nearcore's types are fixed-size (`[u8; 32]`, `[u8; 64]`); here `verify` returns
`false` for any other length.

## Modelling choices
* Field elements are `Nat` values in `[0, p)`; every operation reduces `% p`.
* Points use extended homogeneous coordinates and the complete addition law of
  RFC 8032 §5.1.4 (`a = −1`; complete because `d` is a non-square and `−1` a square
  in `𝔽_p`, Hisil–Wong–Carter–Dawson 2008 §3.1 — the two facts are kernel-checked
  below). Any correct group law yields the same group element, and `encode` normalises
  projectively, so the encoding of `R'` is independent of the representation chosen.
* `[n]P` is MSB-first double-and-add over 256 bits (`n < 2^256` always holds here).
* Inversion is `z^(p−2)` (Fermat; `p` prime).
* All recursion is structural (fuel = bit count), so `decide +kernel` can evaluate
  `verify` on concrete inputs (`NearSpecV3/Examples/Ed25519Kernel.lean`).

## Status (proved vs tested)
* Proved here: `verify_false_of_pk_length`, `verify_false_of_sig_length`,
  `verify_false_of_s_ge` (`s ≥ ℓ` ⇒ `false`), `verify_false_of_decode_none`,
  `sigEncodingOk_of_verify` (`verify` ⇒ the Borsh check passes, because `s < ℓ < 2^253`;
  hence nearcore's post-Borsh verdict `sigEncodingOk sig && verify pk sig msg` and
  `verify pk sig msg` coincide);
  kernel-checked constants facts (`d`, `−1/d` non-squares, `√−1² = −1`, basepoint on the
  curve, `decode (encode B) = B`, `encode B` = RFC 8032 basepoint bytes).
* Not proved: primality of `p`/`ℓ`, completeness of the addition law, or any
  equivalence with dalek's code. Faithfulness to nearcore is **tested**:
  `nearspec-v3-test-ed25519` checks `verify = verify_raw` and `sigEncodingOk = sig_decodes`
  on every vector in `oracle/fixtures/v3/ed25519/` (verdicts from nearcore itself via
  `near-arena-oracle-v3 ed25519-judge`).
-/

namespace NearSpecV3
namespace Ed25519

open ArenaCore

/-- The field prime `p = 2^255 − 19`. -/
def p : Nat := 2 ^ 255 - 19

/-- The prime order of the basepoint, `ℓ = 2^252 + 27742317777372353535851937790883648493`. -/
def L : Nat := 2 ^ 252 + 27742317777372353535851937790883648493

/-- Edwards `d = −121665/121666 mod p` (RFC 8032 §5.1). -/
def d : Nat := 37095705934669439343138083508754565189542113879843219016388785533085940283555

/-- `√−1 = 2^((p−1)/4) mod p` (curve25519-dalek `constants::SQRT_M1`, RFC 8032 §5.1.1). -/
def sqrtM1 : Nat := 19681161376707505956807079304988542015446066515923890162744021073123829784752

/-! ## Field 𝔽_p -/
namespace F

def add (a b : Nat) : Nat := (a + b) % p
def sub (a b : Nat) : Nat := (a + (p - b % p)) % p
def mul (a b : Nat) : Nat := (a * b) % p
def neg (a : Nat) : Nat := (p - a % p) % p

/-- `powAux f b e = b^(e mod 2^f) mod p`, MSB-first square-and-multiply. -/
def powAux : Nat → Nat → Nat → Nat
  | 0, _, _ => 1
  | f + 1, b, e =>
    let r := powAux f b (e / 2)
    if e % 2 = 1 then mul (mul r r) b else mul r r

/-- `b^e mod p` for `e < 2^256`. -/
def pow (b e : Nat) : Nat := powAux 256 b e

/-- `a^(p−2)` (= `a⁻¹` for `a ≢ 0`; `0 ↦ 0`). -/
def inv (a : Nat) : Nat := pow a (p - 2)

/-- `is_negative`: LSB of the canonical encoding (curve25519-dalek `field.rs:101-104`). -/
def isNeg (a : Nat) : Bool := a % p % 2 == 1

/-- The "nonnegative" representative of `±a`. -/
def abs (a : Nat) : Nat := if isNeg a then neg a else a % p

/-- `sqrt_ratio_i(u, v)` restricted to its `Choice` and result
(curve25519-dalek-4.1.3 `src/field.rs:243-289`): `some r` with `r` the nonnegative root
when `u/v` is a square (incl. `u = 0`), `none` otherwise. -/
def sqrtRatio (u v : Nat) : Option Nat :=
  let v3 := mul (mul v v) v
  let v7 := mul (mul v3 v3) v
  let r := mul (mul u v3) (pow (mul u v7) ((p - 5) / 8))
  let check := mul v (mul r r)
  if check = u % p then some (abs r)
  else if check = neg u then some (abs (mul r sqrtM1))
  else none

end F

/-! ## Points (extended homogeneous coordinates, RFC 8032 §5.1.4) -/

/-- `(X : Y : Z : T)` with `x = X/Z`, `y = Y/Z`, `x·y = T/Z`. -/
structure Point where
  X : Nat
  Y : Nat
  Z : Nat
  T : Nat
  deriving DecidableEq, Repr

/-- The neutral element `(0, 1)`. -/
def Point.zero : Point := ⟨0, 1, 1, 0⟩

/-- Affine point `(x, y)` in extended coordinates. -/
def Point.ofAffine (x y : Nat) : Point := ⟨x % p, y % p, 1, F.mul x y⟩

/-- Complete addition for `a = −1` (RFC 8032 §5.1.4, "add-2008-hwcd-3"). -/
def Point.add (P Q : Point) : Point :=
  let a := F.mul (F.sub P.Y P.X) (F.sub Q.Y Q.X)
  let b := F.mul (F.add P.Y P.X) (F.add Q.Y Q.X)
  let c := F.mul (F.mul P.T (F.mul 2 d)) Q.T
  let dd := F.mul (F.mul P.Z 2) Q.Z
  let e := F.sub b a
  let f := F.sub dd c
  let g := F.add dd c
  let h := F.add b a
  ⟨F.mul e f, F.mul g h, F.mul f g, F.mul e h⟩

/-- `−(x, y) = (−x, y)`. -/
def Point.neg (P : Point) : Point := ⟨F.neg P.X, P.Y, P.Z, F.neg P.T⟩

/-- `smulAux f n P = [n mod 2^f] P` (MSB-first double-and-add). -/
def smulAux : Nat → Nat → Point → Point
  | 0, _, _ => Point.zero
  | f + 1, n, P =>
    let Q := smulAux f (n / 2) P
    let Q2 := Point.add Q Q
    if n % 2 = 1 then Point.add Q2 P else Q2

/-- `[n] P` for `n < 2^256`. -/
def smul (n : Nat) (P : Point) : Point := smulAux 256 n P

/-- Affine coordinates `(X/Z, Y/Z)`. -/
def Point.affine (P : Point) : Nat × Nat :=
  let zi := F.inv P.Z
  (F.mul P.X zi, F.mul P.Y zi)

/-- `compress` (curve25519-dalek `edwards.rs:566-575`, RFC 8032 §5.1.2): canonical
little-endian `y` with bit 255 := LSB of canonical `x`. -/
def encode (P : Point) : Bytes :=
  let (x, y) := P.affine
  Bytes.leN 32 (y + 2 ^ 255 * (x % 2))

/-- `CompressedEdwardsY::decompress` (curve25519-dalek `edwards.rs:194-241`): `y` is the
little-endian value with bit 255 cleared, taken mod `p` (non-canonical `y ≥ p` accepted);
`x` is the nonnegative root of `(y²−1)/(dy²+1)`, negated iff bit 255 is set
(`x = 0` with the sign bit set is accepted). -/
def decode (b : Bytes) : Option Point :=
  let n := Bytes.leToNat b
  let y := n % 2 ^ 255 % p
  let sign := n / 2 ^ 255 % 2
  let yy := F.mul y y
  let u := F.sub yy 1
  let v := F.add (F.mul d yy) 1
  match F.sqrtRatio u v with
  | none => none
  | some x0 =>
    let x := if sign = 1 then F.neg x0 else x0
    some ⟨x, y, 1, F.mul x y⟩

/-- The Ed25519 basepoint `B = (x, 4/5)` with `x` even (RFC 8032 §5.1). -/
def B : Point :=
  Point.ofAffine 15112221349535400772501151409588531511454012693041857206046113283949847762202
    46316835694926478169428394003475163141307993866256225615783033603165251855960

/-- The curve equation `−x² + y² = 1 + d x² y²` on an affine pair. -/
def onCurve (x y : Nat) : Bool :=
  F.sub (F.mul y y) (F.mul x x) == F.add 1 (F.mul d (F.mul (F.mul x x) (F.mul y y)))

/-- nearcore's Borsh check on ED25519 signature bytes
(`core/crypto/src/signature.rs:1174-1183`): the top three bits of `sig[63]` are zero.
Not part of `verify`. -/
def sigEncodingOk (sig : Bytes) : Bool := (sig.getD 63 0 &&& 0xE0) == 0

/-- The scalar `s = LE(sig[32..64])`. -/
def sigS (sig : Bytes) : Nat := Bytes.leToNat (sig.drop 32)

/-- The core check, given the decoded public key `A`. -/
def verifyWith (A : Point) (pk sig msg : Bytes) : Bool :=
  let Rb := sig.take 32
  let s := sigS sig
  if L ≤ s then false
  else
    let k := Bytes.leToNat (sha512 (Rb ++ pk ++ msg)) % L
    encode (Point.add (smul s B) (smul k A.neg)) == Rb

/-- nearcore's `Signature::verify` for an ED25519 key/signature pair: see the table in the
module docstring. -/
def verify (pk sig msg : Bytes) : Bool :=
  if pk.length = 32 ∧ sig.length = 64 then
    match decode pk with
    | none => false
    | some A => verifyWith A pk sig msg
  else false

/-! ## Basic facts -/

theorem verify_false_of_pk_length {pk sig msg : Bytes} (h : pk.length ≠ 32) :
    verify pk sig msg = false := by
  simp [verify, h]

theorem verify_false_of_sig_length {pk sig msg : Bytes} (h : sig.length ≠ 64) :
    verify pk sig msg = false := by
  simp [verify, h]

theorem verify_false_of_decode_none {pk sig msg : Bytes} (h : decode pk = none) :
    verify pk sig msg = false := by
  simp [verify, h]

/-- A scalar `s ≥ ℓ` is rejected (`Scalar::from_canonical_bytes`). -/
theorem verify_false_of_s_ge {pk sig msg : Bytes} (h : L ≤ sigS sig) :
    verify pk sig msg = false := by
  unfold verify
  split
  · split
    · rfl
    · simp [verifyWith, h]
  · rfl

/-- `p = 2^255 − 19` as a literal. -/
theorem p_eq : p = 57896044618658097711785492504343953926634992332820282019728792003956564819949 := by
  decide +kernel

/-- `ℓ` as a literal. -/
theorem L_eq : L = 7237005577332262213973186563042994240857116359379907606001950938285454250989 := by
  decide +kernel

/-- `d · (−121666) = 121665` in `𝔽_p`, i.e. `d = −121665/121666`. -/
theorem d_def : F.mul d (F.neg 121666) = 121665 := by decide +kernel

/-- `√−1² = −1`, so `−1` is a square (needed for completeness of the `a = −1` law). -/
theorem sqrtM1_sq : F.mul sqrtM1 sqrtM1 = p - 1 := by decide +kernel

/-- `d` is a non-square (Euler's criterion; `p` prime). -/
theorem d_nonsquare : F.pow d ((p - 1) / 2) = p - 1 := by decide +kernel

/-- `−1/d` is a non-square, hence `v = d·y² + 1 ≠ 0` in `decode` for every `y`. -/
theorem neg_inv_d_nonsquare : F.pow (F.neg (F.inv d)) ((p - 1) / 2) = p - 1 := by
  decide +kernel

/-- The basepoint satisfies the curve equation. -/
theorem B_onCurve : onCurve B.X B.Y = true := by decide +kernel

/-- `encode B` is RFC 8032's basepoint encoding `0x58666…66` (y = 4/5, x even). -/
theorem encode_B : encode B = 0x58 :: List.replicate 31 0x66 := by decide +kernel

/-- `decode (encode B) = B` (round trip). -/
theorem decode_encode_B : decode (encode B) = some B := by decide +kernel

/-! ## Borsh check is implied by acceptance -/
theorem leToNat_ge_getD : ∀ (l : Bytes) (n : Nat),
    256 ^ n * (l.getD n 0).toNat ≤ Bytes.leToNat l
  | [], n => by simp
  | x :: xs, 0 => by simp [Bytes.leToNat]
  | x :: xs, n + 1 => by
    have ih := leToNat_ge_getD xs n
    simp only [Bytes.leToNat, List.getD_cons_succ, Nat.pow_succ]
    have : 256 ^ n * 256 * (xs.getD n 0).toNat = 256 * (256 ^ n * (xs.getD n 0).toNat) := by
      rw [Nat.mul_comm (256 ^ n) 256, Nat.mul_assoc]
    omega

theorem uint8_lt32 (b : UInt8) (h : b.toNat < 32) : (b &&& 0xE0) = 0 := by
  have key : ∀ n, n < 32 → n &&& 224 = 0 := by decide
  apply UInt8.toNat_inj.mp
  rw [UInt8.toNat_and]
  exact key _ h

/-- A signature that verifies passes nearcore's Borsh check, so on every 64-byte `sig`
nearcore's post-decoding verdict `sigEncodingOk sig && verify pk sig msg` equals
`verify pk sig msg`. -/
theorem sigEncodingOk_of_verify {pk sig msg : Bytes} (h : verify pk sig msg = true) :
    sigEncodingOk sig = true := by
  have hs : sigS sig < L := by
    rcases Nat.lt_or_ge (sigS sig) L with h' | h'
    · exact h'
    · rw [verify_false_of_s_ge h'] at h; cases h
  have hb := leToNat_ge_getD (sig.drop 32) 31
  have hL : L < 256 ^ 31 * 32 := by decide +kernel
  have h63 : ((sig.drop 32).getD 31 0).toNat < 32 := by
    unfold sigS at hs
    have := Nat.lt_of_le_of_lt hb (Nat.lt_trans hs hL)
    exact Nat.lt_of_mul_lt_mul_left this
  have : (sig.drop 32).getD 31 0 = sig.getD 63 0 := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop]
  rw [this] at h63
  unfold sigEncodingOk
  rw [uint8_lt32 _ h63]
  rfl
end Ed25519
end NearSpecV3
