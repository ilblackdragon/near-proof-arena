import NearSpecV3.Secp256k1

/-!
# `Secp256k1.verify` against a known-good ECDSA vector

W06 records that `Secp256k1.verify` was "landed but uncalled and checked only against a Python
reference". This module turns that into a checked-in Lean evaluation against a vector produced by an
independent implementation (`python-cryptography`, OpenSSL-backed), so a regression in the arithmetic
or in the signature parsing fails the build instead of surfacing as 34 unexplained state-root
disagreements.

Key: the well-known secp256k1 test keypair. Message: `sha256("test message")`. Signature: a real
ECDSA/SHA-256 signature over it, recovery id 0. `verify` asserts the recovered key's x-coordinate
mod `n` equals `r`, which is what nearcore's `Signature::verify` checks through libsecp256k1.
-/

namespace NearSpecV3.Examples.SecpVerifyVector

open ArenaCore NearSpecV3

/-- Hex → `Bytes`, so the vectors are copy-pasteable from the reference implementation. -/
def hexDigits : List Char → List UInt8
  | [] => []
  | [_] => []
  | hi :: lo :: rest =>
    let d (c : Char) : UInt8 :=
      UInt8.ofNat (if c.toNat ≤ 57 then c.toNat - 48 else c.toNat - 87)
    (d hi * 16 + d lo) :: hexDigits rest

def hex (s : String) : Bytes := hexDigits s.toList

/-- Signing public key, `X ‖ Y`, 64 bytes big-endian. -/
def pk : Bytes :=
  hex "567b7512001f3cc4dcb8b8096c046fff571ab07adb2126cd42908f2ff1ca424a" ++
  hex "3ab781fe65ba2bbc50b71532312b3836793be62bc4f313e8874fa8a2b1cacea1"

/-- `r ‖ s ‖ recId`, 65 bytes. -/
def sig : Bytes :=
  hex "e168e7ffb9aa740d27fc3a465e5e5bd3019f5c4453ab9820b322eb4355f0d7c8" ++
  hex "7a926ccd1892399cee231ae9990963d8aa1c8d392ddcf9fc813d9da51450d8d4" ++
  [0]

/-- `sha256("test message")`. -/
def msgHash : Bytes :=
  hex "3f0a377ba0a4a460ecb616f6507ce0d8cfa3e704025d4fda3ed0c5ca05468728"

/-- Shape guard so the `decide` below is not run on a mistyped vector. -/
theorem lengths : pk.length = 64 ∧ sig.length = 65 ∧ msgHash.length = 32 := by decide +kernel

/-- The independent reference's answer. If this fails, `Secp256k1.verify` disagrees with
nearcore's curve library on a *valid* signature, which is the defect behind the tx-key gap. -/
theorem verify_accepts_known_good : Secp256k1.verify pk sig msgHash = true := by decide +kernel

end NearSpecV3.Examples.SecpVerifyVector
