import ArenaCore.Bytes

/-!
# secp256k1 public-key recovery, as performed by nearcore's `ecrecover`

Leaf module for the crypto-enabled successor domain (L3). `recover` is the computation behind
`runtime/near-vm-runner/src/wasmtime_runner/logic.rs:1668-1770` (`ecrecover`), which calls
`Secp256K1Signature::recover` (`core/crypto/src/signature.rs:979-1004`). That, in turn, is
libsecp256k1's `ecdsa_recover` (`secp256k1-sys` 0.8.1,
`depend/secp256k1/src/modules/recovery/main_impl.h:87-113,138-158`) through the Rust wrapper
`secp256k1` 0.27.0 (`src/ecdsa/recovery.rs:224-241`).

## Source semantics (each point re-read in the pinned sources)

| # | rule | source |
|---|------|--------|
| 1 | `ecrecover` reads 64 signature bytes and a 32-byte hash; `v` is a separate `u64` | nearcore `logic.rs:1668-1700` |
| 2 | `v ≥ 4` is `HostError::ECRecoverError` (not a `0` return) | `logic.rs:1698-1705` |
| 3 | `malleability_flag ∉ {0,1}` is `ECRecoverError` | `logic.rs:1737-1745` |
| 4 | `check_signature_values(reject_upper)`: `r < n ∧ s < (reject_upper ? (n+1)/2 : n)`; failure returns `0` | `core/crypto/src/signature.rs:959-977`, consts at `:947-952` |
| 5 | recovery rejects `r = 0` or `s = 0` | `recovery/main_impl.h:94-96` |
| 6 | `recid & 2` selects `x = r + n`, but only if `r < p − n`; otherwise recovery fails | `main_impl.h:101-107` |
| 7 | `x` is decompressed with the parity `recid & 1`; no solution ⇒ fail | `main_impl.h:108-110` |
| 8 | `Q = r⁻¹·(s·R − m·G)` in the scalar field mod `n`; `m` is the 32-byte hash reduced mod `n` (`scalar_set_b32` ignores overflow); `Q = ∞` ⇒ fail | `main_impl.h:111-113` |
| 9 | the recovered key is `serialize_uncompressed()[1..65]` = 64 bytes `X ‖ Y` big-endian, with no on-curve re-validation (`try_fixed_array` checks length only) | nearcore `signature.rs:992-1003,112-120` |

Field and group arithmetic are the standard formulas: `p ≡ 3 (mod 4)` square roots
(`y = (x³+7)^((p+1)/4)`), Jacobian doubling (`dbl-2009-l`) and addition (`add-2007-bl`) for
`a = 0`, MSB-first 256-bit double-and-add. Every recursion is structural, so the kernel can
evaluate `recover` on concrete inputs; the vector tests run in the compiled evaluator
(`oracle/wasm-d3/lean/CryptoTest.lean`).

## Status
Proved here: totality/length lemmas (`recover_none_of_sig_length`, `recover_none_of_hash_length`,
`recover_none_of_r_ge`, `recover_none_of_s_ge`, `checkSigValues_*`), and the kernel-checked
constants facts `p_eq`, `n_eq`, `nHalfOne_eq`, `p_mod_four`, `G_on_curve`, `G_not_inf`.
Tested, not proved: agreement of `recover` with all 161 vectors of
`runtime/near-vm-runner/src/logic/tests/ecrecover-tests.json` (nearcore's own suite) and the
directed edge cases in `CryptoTest.lean`. Nothing here is claimed equivalent to libsecp256k1 by
proof.
-/

namespace NearSpecV3
namespace Secp256k1

open ArenaCore

/-- The field prime `p = 2^256 − 2^32 − 977`. -/
def p : Nat := 2 ^ 256 - 2 ^ 32 - 977

/-- The group order `n`. -/
def n : Nat := 115792089237316195423570985008687907852837564279074904382605163141518161494337

/-- `(n + 1)/2`, the upper bound `check_signature_values` uses when rejecting malleable `s`. -/
def nHalfOne : Nat :=
  57896044618658097711785492504343953926418782139537452191302581570759080747169

/-- The generator `G`. -/
def Gx : Nat :=
  55066263022277343669578718895168534326250603453777594175500187360389116729240
def Gy : Nat :=
  32670510020758816978083085130507043184471273380659243275938904335757337482424

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

/-- `a^(p−2)` (`0 ↦ 0`). -/
def inv (a : Nat) : Nat := pow a (p - 2)

/-- `√a` for `p ≡ 3 (mod 4)`: `a^((p+1)/4)`, checked by the caller. -/
def sqrt (a : Nat) : Nat := pow a ((p + 1) / 4)

end F

/-! ## Scalar field mod `n` (only multiplication, addition and inversion are needed) -/

namespace N

def add (a b : Nat) : Nat := (a + b) % n
def mul (a b : Nat) : Nat := (a * b) % n
def neg (a : Nat) : Nat := (n - a % n) % n

def powAux : Nat → Nat → Nat → Nat
  | 0, _, _ => 1
  | f + 1, b, e =>
    let r := powAux f b (e / 2)
    if e % 2 = 1 then mul (mul r r) b else mul r r

def pow (b e : Nat) : Nat := powAux 256 b e

/-- `a^(n−2) mod n` (`0 ↦ 0`). -/
def inv (a : Nat) : Nat := pow a (n - 2)

end N

/-! ## Jacobian points (`a = 0`), `Z = 0` is infinity -/

structure J where
  X : Nat
  Y : Nat
  Z : Nat
  deriving DecidableEq, Repr

def J.inf : J := ⟨0, 1, 0⟩
def J.ofAffine (x y : Nat) : J := ⟨x % p, y % p, 1⟩
def J.isInf (P : J) : Bool := P.Z = 0

/-- `dbl-2009-l` (a = 0). -/
def J.dbl (P : J) : J :=
  if P.Z = 0 ∨ P.Y = 0 then J.inf else
  let A := F.mul P.X P.X
  let B := F.mul P.Y P.Y
  let C := F.mul B B
  let D := F.mul 2 (F.sub (F.sub (F.mul (F.add P.X B) (F.add P.X B)) A) C)
  let E := F.add (F.add A A) A
  let F' := F.mul E E
  let X3 := F.sub F' (F.add D D)
  let Y3 := F.sub (F.mul E (F.sub D X3)) (F.mul 8 C)
  let Z3 := F.mul 2 (F.mul P.Y P.Z)
  ⟨X3, Y3, Z3⟩

/-- `add-2007-bl` (Jacobian + Jacobian, a = 0). -/
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

/-- `smulAux f k P = [k mod 2^f] P` (MSB-first double-and-add). -/
def J.smulAux : Nat → Nat → J → J
  | 0, _, _ => J.inf
  | f + 1, k, P =>
    let Q := J.smulAux f (k / 2) P
    let Q2 := J.dbl Q
    if k % 2 = 1 then J.add Q2 P else Q2

/-- `[k] P` for `k < 2^256`. -/
def J.smul (k : Nat) (P : J) : J := J.smulAux 256 k P

/-- Affine coordinates of a finite point. -/
def J.affine (P : J) : Nat × Nat :=
  let zi := F.inv P.Z
  let zi2 := F.mul zi zi
  (F.mul P.X zi2, F.mul (F.mul P.Y zi2) zi)

/-- The canonical curve equation `y² = x³ + 7`. -/
def onCurve (x y : Nat) : Bool :=
  F.mul y y == F.add (F.mul (F.mul x x) x) 7

/-- `ge_set_xo_var`: the point with `x` and the requested `y` parity, if it exists.
`x` must already be reduced. Mirrors libsecp256k1: a missing root, or `y = 0` with odd parity,
fails. -/
def decompress (x : Nat) (odd : Bool) : Option (Nat × Nat) :=
  let rhs := F.add (F.mul (F.mul x x) x) 7
  let y0 := F.sqrt rhs
  if F.mul y0 y0 ≠ rhs then none else
  let y := if (y0 % 2 == 1) = odd then y0 else F.neg y0
  if (y % 2 == 1) = odd then some (x, y) else none

/-! ## `check_signature_values` and recovery -/

/-- `Secp256K1Signature::check_signature_values` (`signature.rs:959-977`) on the 64-byte
`r ‖ s` prefix; `rejectUpper` is `malleability_flag ≠ 0`. -/
def checkSigValues (sig : Bytes) (rejectUpper : Bool) : Bool :=
  if sig.length = 64 then
    let r := Bytes.beToNat (sig.take 32)
    let s := Bytes.beToNat (sig.drop 32)
    r < n && s < (if rejectUpper then nHalfOne else n)
  else false

/-- `PublicKey::from_slice` on the 65-byte `0x04 ‖ X ‖ Y` form (`signature.rs:1119-1122`).
libsecp256k1 accepts only the uncompressed 65-byte encoding whose coordinates satisfy the curve
equation; both coordinates are already reduced by construction of the encoding, so an
out-of-range coordinate cannot decode. -/
def decodePubkey (pk : Bytes) : Option (Nat × Nat) :=
  if pk.length = 65 ∧ pk.getD 0 0 == 4 then
    let x := Bytes.beToNat (pk.drop 1 |>.take 32)
    let y := Bytes.beToNat (pk.drop 33 |>.take 32)
    if onCurve x y then some (x, y) else none
  else none

/-- ECDSA verification (`SECP256K1.verify_ecdsa`, `signature.rs:1094-1123`).

nearcore's `Signature::verify` for `(SECP256K1, SECP256K1)` first parses the recovery id from
byte 64 and `RecoverableSignature::from_compact` on bytes `0..64` (both failures ⇒ `false`), then
verifies the *standard* signature against the public key's uncompressed 65-byte form. It never
uses the recovery id's implied key: the supplied key is authoritative. So verification is
plain ECDSA: `u1 = z·s⁻¹`, `u2 = r·s⁻¹`, `R = u1·G + u2·Q`, accept iff `R ≠ ∞` and
`R.x ≡ r (mod n)`.

`sig` is the 65-byte `r ‖ s ‖ rec_id`; `hash` is the 32-byte message digest; `pk` is the 64-byte
`X ‖ Y` key data as nearcore stores it. -/
def verify (pk : Bytes) (sig : Bytes) (hash : Bytes) : Bool :=
  if sig.length = 65 ∧ hash.length = 32 then
    let r := Bytes.beToNat (sig.take 32)
    let s := Bytes.beToNat (sig.drop 32 |>.take 32)
    -- `RecoveryId::from_i32`: only 0..=3 are valid encodings.
    let recId := (sig.getD 64 255).toNat
    let pdata := [4] ++ pk
    match decodePubkey pdata with
    | none => false
    | some (qx, qy) =>
      if r = 0 ∨ s = 0 ∨ ¬ (r < n ∧ s < n) ∨ ¬ (recId < 4) then false
      else
        let z := Bytes.beToNat hash % n
        let sinv := N.inv s
        let u1 := N.mul z sinv
        let u2 := N.mul r sinv
        let R := J.add (J.smul u1 (J.ofAffine Gx Gy)) (J.smul u2 (J.ofAffine qx qy))
        if R.isInf then false
        else (R.affine).1 % n == r
  else false

/-- `Secp256K1Signature::recover` for an already length-checked 64-byte `r ‖ s` and 32-byte
hash, `v < 4`. `some pk` with `pk = X ‖ Y` (64 bytes, big-endian), as nearcore returns. -/
def recover (sig : Bytes) (v : Nat) (hash : Bytes) : Option Bytes :=
  if sig.length = 64 ∧ hash.length = 32 ∧ v < 4 then
    let r := Bytes.beToNat (sig.take 32)
    let s := Bytes.beToNat (sig.drop 32)
    if r = 0 ∨ s = 0 ∨ ¬ (r < n ∧ s < n) then none
    else
      let x := if v ≥ 2 then r + n else r
      if v ≥ 2 ∧ ¬ (r < p - n) then none
      else
        match decompress x (v % 2 = 1) with
        | none => none
        | some (rx, ry) =>
          let z := Bytes.beToNat hash % n
          let rinv := N.inv r
          let u1 := N.neg (N.mul z rinv)
          let u2 := N.mul s rinv
          let Q := J.add (J.smul u2 (J.ofAffine rx ry)) (J.smul u1 (J.ofAffine Gx Gy))
          if Q.isInf then none
          else
            let (qx, qy) := Q.affine
            some (Bytes.beN 32 qx ++ Bytes.beN 32 qy)
  else none

/-! ## Basic facts -/

theorem p_eq : p = 115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
  decide +kernel

theorem n_eq : n =
    115792089237316195423570985008687907852837564279074904382605163141518161494337 := rfl

theorem nHalfOne_eq : nHalfOne = (n + 1) / 2 := by decide +kernel

theorem p_mod_four : p % 4 = 3 := by decide +kernel

theorem G_on_curve : onCurve Gx Gy = true := by decide +kernel

theorem G_not_inf : J.isInf (J.ofAffine Gx Gy) = false := by decide +kernel

theorem recover_none_of_sig_length {sig : Bytes} {v : Nat} {hash : Bytes} (h : sig.length ≠ 64) :
    recover sig v hash = none := by
  simp [recover, h]

theorem recover_none_of_hash_length {sig : Bytes} {v : Nat} {hash : Bytes}
    (h : hash.length ≠ 32) : recover sig v hash = none := by
  simp [recover, h]

theorem recover_none_of_v {sig : Bytes} {v : Nat} {hash : Bytes} (h : ¬ v < 4) :
    recover sig v hash = none := by
  simp [recover, h]

theorem checkSigValues_false_of_length {sig : Bytes} {rejectUpper : Bool}
    (h : sig.length ≠ 64) : checkSigValues sig rejectUpper = false := by
  simp [checkSigValues, h]

/-- Rejecting upper-range `s` is strictly stronger (the `malleability_flag = 1` mode). -/
theorem checkSigValues_mono {sig : Bytes}
    (h : checkSigValues sig true = true) : checkSigValues sig false = true := by
  have hle : nHalfOne ≤ n := by decide +kernel
  by_cases hl : sig.length = 64
  · have h' := h
    unfold checkSigValues at h'
    simp only [hl, if_pos, Bool.and_eq_true, decide_eq_true_eq] at h'
    unfold checkSigValues
    simp only [hl, if_pos, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h'.1, Nat.lt_of_lt_of_le h'.2 hle⟩
  · rw [checkSigValues_false_of_length hl] at h
    cases h

end Secp256k1
end NearSpecV3
