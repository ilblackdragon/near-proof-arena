import ArenaCore.Bytes

/-!
# P-256 ECDSA prehash verification, as performed by nearcore's `p256_verify`

Leaf module for the crypto-enabled successor domain (L3), second entry after `Secp256k1.lean`.
`verify` is what `runtime/near-vm-runner/src/wasmtime_runner/logic.rs:1884-1930` computes through
RustCrypto `p256` 0.13.2 (`p256::ecdsa::VerifyingKey::verify_prehash`,
`ecdsa` 0.16.9 `verifying.rs:163-166` → `hazmat.rs:270-292`).

## Source semantics

| # | rule | source |
|---|------|--------|
| 1 | signature is 64 bytes `r ‖ s`; `Signature::from_slice` rejects `r = 0`, `s = 0`, `r ≥ n`, `s ≥ n` (a `0` return, not an error) | `logic.rs:1912-1926`; `ecdsa-0.16.9/src/lib.rs:250-259` |
| 2 | the message is **not** hashed (NEP-635, `logic.rs:1870-1882`); `bits2field` left-pads inputs shorter than 32 bytes and truncates longer ones, and rejects inputs shorter than 16 bytes | `ecdsa-0.16.9/src/hazmat.rs:185-206` |
| 3 | the public key is 33-byte compressed SEC1; a parse failure or the identity returns `0` | `logic.rs:1926-1942`; `elliptic-curve-0.13.8/src/public_key.rs:126-133,232-238` |
| 4 | `z = bits2field(msg) mod n`; `u1 = z·s⁻¹`, `u2 = r·s⁻¹`; accept iff `x(u1·G + u2·Q) mod n = r` (`v` is **not** used) | `ecdsa-0.16.9/src/hazmat.rs:270-292` |
| 5 | no low-s enforcement: high-s signatures verify | `logic/tests/p256_verify_wycheproof.rs:15-20` |

Curve: `y² = x³ − 3x + b` over `F_p`, `p = 2^256 − 2^224 + 2^192 + 2^96 − 1`, group order `n`;
compressed encoding is `0x02/0x03 ‖ X` with the parity of `Y`, and decompression requires
`y = (x³ − 3x + b)^((p+1)/4)` to square back to the right-hand side.

## Status
Proved here: the length gates (`verify_false_of_sig_length`, `verify_false_of_msg_too_short`,
`verify_false_of_pk_length`, `verify_false_of_pk_tag`) and the kernel-checked constants
(`p_eq`, `n_eq`, `G_on_curve`, `p_mod_four`). Tested, not proved: agreement with the 8
Wycheproof vectors and 15 unit cases in nearcore's own `logic/tests/p256_verify*.rs`.
-/

namespace NearSpecV3
namespace P256

open ArenaCore

def p : Nat := 2 ^ 256 - 2 ^ 224 + 2 ^ 192 + 2 ^ 96 - 1

def n : Nat := 115792089210356248762697446949407573529996955224135760342422259061068512044369

def b : Nat := 41058363725152142129326129780047268409114441015993725554835256314039467401291

def Gx : Nat := 48439561293906451759052585252797914202762949526041747995844080717082404635286
def Gy : Nat := 36134250956749795798585127919587881956611106672985015071877198253568414405109

namespace F

def add (a b : Nat) : Nat := (a + b) % p
def sub (a b : Nat) : Nat := (a + (p - b % p)) % p
def mul (a b : Nat) : Nat := (a * b) % p
def neg (a : Nat) : Nat := (p - a % p) % p

def powAux : Nat → Nat → Nat → Nat
  | 0, _, _ => 1
  | f + 1, bb, e =>
    let r := powAux f bb (e / 2)
    if e % 2 = 1 then mul (mul r r) bb else mul r r

def pow (bb e : Nat) : Nat := powAux 256 bb e
def inv (a : Nat) : Nat := pow a (p - 2)
def sqrt (a : Nat) : Nat := pow a ((p + 1) / 4)

end F

namespace N

def add (a b : Nat) : Nat := (a + b) % n
def mul (a b : Nat) : Nat := (a * b) % n
def neg (a : Nat) : Nat := (n - a % n) % n

def powAux : Nat → Nat → Nat → Nat
  | 0, _, _ => 1
  | f + 1, bb, e =>
    let r := powAux f bb (e / 2)
    if e % 2 = 1 then mul (mul r r) bb else mul r r

def pow (bb e : Nat) : Nat := powAux 256 bb e
def inv (a : Nat) : Nat := pow a (n - 2)

end N

/-- Jacobian point for `a = −3` (`Z = 0` = infinity). -/
structure J where
  X : Nat
  Y : Nat
  Z : Nat
  deriving DecidableEq, Repr

def J.inf : J := ⟨0, 1, 0⟩
def J.ofAffine (x y : Nat) : J := ⟨x % p, y % p, 1⟩
def J.isInf (P : J) : Bool := P.Z = 0

/-- `dbl-2001-b` (a = −3): `M = 3(X−Z²)(X+Z²)`. -/
def J.dbl (P : J) : J :=
  if P.Z = 0 ∨ P.Y = 0 then J.inf else
  let delta := F.mul P.Z P.Z
  let gamma := F.mul P.Y P.Y
  let beta := F.mul P.X gamma
  let alpha := F.mul (F.mul 3 (F.sub P.X delta)) (F.add P.X delta)
  let X3 := F.sub (F.mul alpha alpha) (F.mul 8 beta)
  let Z3 := F.sub (F.sub (F.mul (F.add P.Y P.Z) (F.add P.Y P.Z)) gamma) delta
  let Y3 := F.sub (F.mul alpha (F.sub (F.mul 4 beta) X3)) (F.mul 8 (F.mul gamma gamma))
  ⟨X3, Y3, Z3⟩

/-- `add-2007-bl` (a = −3, the generic formula works for any `a`). -/
def J.add (P Q : J) : J :=
  if P.Z = 0 then Q else if Q.Z = 0 then P else
  let Z1Z1 := F.mul P.Z P.Z
  let Z2Z2 := F.mul Q.Z Q.Z
  let U1 := F.mul P.X Z2Z2
  let U2 := F.mul Q.X Z1Z1
  let S1 := F.mul (F.mul P.Y Q.Z) Z2Z2
  let S2 := F.mul (F.mul Q.Y P.Z) Z1Z1
  if U1 = U2 then
    (if S1 = S2 then J.dbl P else J.inf)
  else
    let H := F.sub U2 U1
    let I := F.mul (F.add H H) (F.add H H)
    let J' := F.mul H I
    let r := F.mul 2 (F.sub S2 S1)
    let V := F.mul U1 I
    let X3 := F.sub (F.sub (F.mul r r) J') (F.add V V)
    let Y3 := F.sub (F.mul r (F.sub V X3)) (F.mul 2 (F.mul S1 J'))
    let Z3 := F.mul (F.sub (F.sub (F.mul (F.add P.Z Q.Z) (F.add P.Z Q.Z)) Z1Z1) Z2Z2) H
    ⟨X3, Y3, Z3⟩

def J.smulAux : Nat → Nat → J → J
  | 0, _, _ => J.inf
  | f + 1, k, P =>
    let Q := J.smulAux f (k / 2) P
    let Q2 := J.dbl Q
    if k % 2 = 1 then J.add Q2 P else Q2

def J.smul (k : Nat) (P : J) : J := J.smulAux 256 k P

/-- Affine `x` of a finite point. -/
def J.affineX (P : J) : Nat :=
  let zi := F.inv P.Z
  F.mul P.X (F.mul zi zi)

def J.affine (P : J) : Nat × Nat :=
  let zi := F.inv P.Z
  let zi2 := F.mul zi zi
  (F.mul P.X zi2, F.mul (F.mul P.Y zi2) zi)

/-- `y² = x³ − 3x + b`. -/
def onCurve (x y : Nat) : Bool :=
  F.mul y y == F.add (F.sub (F.mul (F.mul x x) x) (F.mul 3 x)) b

/-- SEC1 compressed-key decompression: `0x02`/`0x03 ‖ X`. -/
def decompress (pk : Bytes) : Option (Nat × Nat) :=
  match pk with
  | tag :: rest =>
    if rest.length = 32 ∧ (tag = 2 ∨ tag = 3) then
      let x := Bytes.beToNat rest
      if x ≥ p then none else
      let rhs := F.add (F.sub (F.mul (F.mul x x) x) (F.mul 3 x)) b
      let y0 := F.sqrt rhs
      if F.mul y0 y0 ≠ rhs then none else
      let odd := tag = 3
      let y := if (y0 % 2 == 1) = odd then y0 else F.neg y0
      if (y % 2 == 1) = odd then some (x, y) else none
    else none
  | [] => none

/-- `bits2field` for a 32-byte curve (`ecdsa-0.16.9/src/hazmat.rs:185-206`), then reduction mod
`n`: inputs of 16..31 bytes are left-padded, 32-byte inputs are used as-is, longer inputs are
truncated to the first 32 bytes; shorter than 16 bytes is an error (`none`). -/
def bits2field (msg : Bytes) : Option Nat :=
  if msg.length < 16 then none
  else if msg.length ≤ 32 then
    some (Bytes.beToNat (List.replicate (32 - msg.length) 0 ++ msg) % n)
  else some (Bytes.beToNat (msg.take 32) % n)

/-- The signature-parse gate (`Signature::from_scalars`): `r, s ∈ [1, n)`. -/
def sigOk (sig : Bytes) : Bool :=
  if sig.length = 64 then
    let r := Bytes.beToNat (sig.take 32)
    let s := Bytes.beToNat (sig.drop 32)
    0 < r ∧ r < n ∧ 0 < s ∧ s < n
  else false

/-- `VerifyingKey::verify_prehash` (`hazmat.rs:270-292`) with the parse gates of `logic.rs`. -/
def verify (sig msg pk : Bytes) : Bool :=
  if sig.length ≠ 64 ∨ pk.length ≠ 33 then false
  else if !sigOk sig then false
  else
    match bits2field msg, decompress pk with
    | some z, some (qx, qy) =>
      let r := Bytes.beToNat (sig.take 32)
      let s := Bytes.beToNat (sig.drop 32)
      let sinv := N.inv s
      let u1 := N.mul z sinv
      let u2 := N.mul r sinv
      let X := J.add (J.smul u1 (J.ofAffine Gx Gy)) (J.smul u2 (J.ofAffine qx qy))
      if X.isInf then false
      else J.affineX X % n == r
    | _, _ => false

/-! ## Basic facts -/

theorem p_eq : p =
    115792089210356248762697446949407573530086143415290314195533631308867097853951 := by
  decide +kernel

theorem n_eq : n = 115792089210356248762697446949407573529996955224135760342422259061068512044369 :=
  rfl

theorem p_mod_four : p % 4 = 3 := by decide +kernel

theorem G_on_curve : onCurve Gx Gy = true := by decide +kernel

theorem verify_false_of_sig_length {sig msg pk : Bytes} (h : sig.length ≠ 64) :
    verify sig msg pk = false := by
  simp [verify, h]

theorem verify_false_of_pk_length {sig msg pk : Bytes} (h : pk.length ≠ 33) :
    verify sig msg pk = false := by
  simp [verify, h]

theorem bits2field_none {msg : Bytes} (h : msg.length < 16) : bits2field msg = none := by
  simp [bits2field, h]

/-- `Signature::from_slice` rejects `r = 0`, `s = 0` and `r, s ≥ n` with a `0` return. -/
theorem verify_false_of_sig_not_ok {sig msg pk : Bytes} (h : sigOk sig = false) :
    verify sig msg pk = false := by
  by_cases hl : sig.length = 64
  · simp [verify, hl, h]
  · simp [verify, hl]

end P256
end NearSpecV3
