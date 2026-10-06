import NearSpecV3.Ed25519

/-!
# Kernel non-vacuity checks for `NearSpecV3.sha512` and `NearSpecV3.Ed25519.verify`

NOT imported by `NearSpecV3.lean`. Every statement is closed by `decide +kernel`
(evaluation by the Lean kernel itself; no `native_decide`, no compiled code).
Check with `lake env lean NearSpecV3/Examples/Ed25519Kernel.lean`.

* SHA-512 of "abc" and of "" equal the FIPS 180-4 example digests
  (FIPS 180-2 Appendix C.1 / NIST CSRC SHA-512 examples).
* RFC 8032 §7.1 TEST 1 verifies; a one-bit mutation of its signature, a non-empty message
  and a flipped sign bit of the public key do not.
* RFC 8032 §7.1 TEST 2 verifies.
* Two dalek-specific accept-side edge cases (nearcore verdict `verify_raw = true`, from
  `oracle/fixtures/v3/ed25519/edge.jsonl`): the public key `0x01‖0^30‖0x80`
  (y = 1, x = 0 with the sign bit set — rejected by RFC 8032 §5.1.3, accepted by dalek)
  and the non-canonical public key `y = p + 1` (y ≥ p, accepted by dalek), both with
  crafted signatures that hold under the cofactorless equation.
-/

namespace NearSpecV3.Ed25519.KernelExamples
open ArenaCore

def hex (s : String) : Bytes := (Bytes.ofHex? s).getD []

theorem sha512_abc : sha512 (Bytes.ofString "abc") = hex
    "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f" := by
  decide +kernel

theorem sha512_empty : sha512 [] = hex
    "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e" := by
  decide +kernel

def t1pk : Bytes := hex "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"
def t1sig : Bytes := hex "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b"

theorem rfc8032_test1 : verify t1pk t1sig [] = true := by decide +kernel

theorem rfc8032_test1_sig_mutated :
    verify t1pk (t1sig.set 0 (t1sig.getD 0 0 ^^^ 1)) [] = false := by decide +kernel

theorem rfc8032_test1_msg_mutated : verify t1pk t1sig [0] = false := by decide +kernel

theorem rfc8032_test1_pk_signflip :
    verify (t1pk.set 31 (t1pk.getD 31 0 ^^^ 0x80)) t1sig [] = false := by decide +kernel

theorem rfc8032_test2 :
    verify (hex "3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c")
      (hex "92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00")
      [0x72] = true := by decide +kernel

/-- y = 1, x = 0 with the sign bit set (dalek accepts; RFC 8032 §5.1.3 would reject). -/
theorem dalek_x0_signbit_accepted :
    verify (hex "0100000000000000000000000000000000000000000000000000000000000080")
      (hex "00db3c5c380f9b8e2d90b75ed9caccb72d0b138ead0dc16d8dd1826f8127de37a117d395fc1a81a001d3e95933e2c366a3ebec13637ce772a9e0b7a0b7b1120b")
      [] = true := by decide +kernel

/-- Non-canonical y = p + 1 (dalek accepts; RFC 8032 §5.1.3 would reject). -/
theorem dalek_noncanonical_A_accepted :
    verify (hex "eeffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f")
      (hex "e7bedf670499925ee30678ed56206d2b3b3361be523ec2e4bf70d95cd576be352268916237a10b500c59e0fab5862359563e116d2ff1aa569f2d32703ad8800f")
      [0x6e, 0x63] = true := by decide +kernel

end NearSpecV3.Ed25519.KernelExamples
