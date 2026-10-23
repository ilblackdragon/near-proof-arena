import NearSpecV3.Wasm.Host
import NearSpecV3.Secp256k1
import NearSpecV3.P256

/-!
# Host semantics of the crypto host functions (successor domain `D3γ`)

`ecrecover` (`runtime/near-vm-runner/src/wasmtime_runner/logic.rs:1668-1770`) and `p256_verify`
(`logic.rs:1884-1930`) as host computations in `HM`, with nearcore's **order of charges and
checks**: gas is paid before bounds checks, each input is charged when read, `write_register` is
charged only when a value is actually written, and a malformed length is a host error while a
failed verification is a `0` return.

`D3α` (`Wasm.Host.hostCall`) deliberately has no arm for any of these names: `Exec.callHost`
reports `unmodeled` and `D3.functionCall` turns that into `out of domain (e.wasm-α)`. This module
adds the arms for the successor relation without touching `hostCall`, so `checkD3`, `RelD3` and
the signed `near-chunk-v3` statement are unchanged.

The arms are named `cryptoHostCall`; `cryptoHosts` is the same 14-name list as `Exec.curveHosts`
(the guard that keeps them out of D3α). `ecrecover` and `p256_verify` have semantics here; the
alt_bn128 / BLS12-381 names stay unmodelled and return `none` from the table (see
`docs/research/lean-chunk-crypto-L3.md`).

## Costs (PV86 `parameters.snap`, `core/parameters/res/runtime_configs/`)

| cost | gas |
|---|---|
| `wasm_ecrecover_base` | 278_821_988_457 |
| `wasm_p256_verify_base` | 1_300_000_000_000 |
| `wasm_p256_verify_byte` | 13_000_000 |

plus `base`/`read_memory_*`/`read_register_*`/`write_register_*` from `Machine.C` for the inputs
and the output register.
-/
namespace NearSpecV3.Wasm

open NearSpecV3

/-- `wasm_ecrecover_base` (`parameters.snap:137`, after `48.yaml`: `old: 3_365_369_625_000,
new: 278_821_988_457`). -/
def ecrecoverBase : Cost := ⟨278821988457, 278821988457, none⟩

/-- `wasm_p256_verify_base` / `wasm_p256_verify_byte` (`parameters.snap:140-141`). -/
def p256VerifyBase : Cost := ⟨1300000000000, 1300000000000, none⟩
def p256VerifyByte : Cost := ⟨13000000, 13000000, none⟩

/-- The 14 host functions that `D3α` excludes (`Exec.curveHosts`, same order and spelling —
`D3.CryptoDomain.cryptoHosts_iff_curveHosts` is `rfl`); `D3γ` models `ecrecover` here. -/
def cryptoHosts : List String :=
  ["alt_bn128_g1_multiexp", "alt_bn128_g1_sum", "alt_bn128_pairing_check",
   "bls12381_p1_sum", "bls12381_p2_sum", "bls12381_g1_multiexp",
   "bls12381_g2_multiexp", "bls12381_map_fp_to_g1", "bls12381_map_fp2_to_g2",
   "bls12381_pairing_check", "bls12381_p1_decompress", "bls12381_p2_decompress",
   "ecrecover", "p256_verify"]

/-- `ecrecover` (`logic.rs:1668-1770`). Arguments are the wasm operands in declaration order:
`hash_len, hash_ptr, sig_len, sig_ptr, v, malleability_flag, register_id`. -/
def hostEcrecover (a : Vector Nat 7) : HM Unit := do
  payBaseH ecrecoverBase
  let hashLen := a[0]; let hashPtr := a[1]
  let sigLen := a[2]; let sigPtr := a[3]
  let v := a[4]; let flag := a[5]; let reg := a[6]
  -- 1. signature first (nearcore reads it before the hash; the `v` gate follows it)
  let sig ← memOrRegH sigPtr sigLen
  if sig.size ≠ 64 then
    hErr s!"ECRecoverError \{ msg: \"The length of the signature: {sig.size}, exceeds the limit of 64 bytes\" }"
  if v ≥ 4 then
    hErr s!"ECRecoverError \{ msg: \"V recovery byte 0 through 3 are valid but was provided {v}\" }"
  -- 2. hash
  let hash ← memOrRegH hashPtr hashLen
  if hash.size ≠ 32 then
    hErr s!"ECRecoverError \{ msg: \"The length of the hash: {hash.size}, exceeds the limit of 32 bytes\" }"
  -- 3. malleability flag
  if flag ≠ 0 ∧ flag ≠ 1 then
    hErr s!"ECRecoverError \{ msg: \"Malleability flag needs to be 0 or 1, but is instead {flag}\" }"
  -- 4. signature value range (a `0` return, not an error)
  if !Secp256k1.checkSigValues sig.toList (flag != 0) then pushRet 0 else
  -- 5. recovery; a successful recovery writes the 64-byte key to the register
  match Secp256k1.recover sig.toList v hash.toList with
  | some pk => regSetH reg (ByteArray.mk pk.toArray); pushRet 1
  | none => pushRet 0

/-- `p256_verify` (`logic.rs:1884-1930`). Arguments in declaration order:
`sig_len, sig_ptr, msg_len, msg_ptr, pk_len, pk_ptr`. Note the order of charges and checks differs
from `ecrecover`: the message is read (and charged per byte) **before** the public key, and every
parse failure is a `0` return, not a host error. -/
def hostP256Verify (a : Vector Nat 6) : HM Unit := do
  payBaseH p256VerifyBase
  let sigLen := a[0]; let sigPtr := a[1]
  let msgLen := a[2]; let msgPtr := a[3]
  let pkLen := a[4]; let pkPtr := a[5]
  let sig ← memOrRegH sigPtr sigLen
  if sig.size ≠ 64 then
    hErr "P256VerifyInvalidInput { msg: \"invalid signature length\" }"
  -- `Signature::from_slice`: r = 0, s = 0, r ≥ n or s ≥ n is a `0` return
  if !P256.sigOk sig.toList then pushRet 0 else
  let msg ← memOrRegH msgPtr msgLen
  payPerH p256VerifyByte msg.size
  let pk ← memOrRegH pkPtr pkLen
  if pk.size ≠ 33 then
    hErr "P256VerifyInvalidInput { msg: \"invalid public key length\" }"
  pushRet (if P256.verify sig.toList msg.toList pk.toList then 1 else 0)

/-- `cryptoHostCall`: the `D3γ` host table. `none` for every name whose semantics is not
implemented yet (including the alt_bn128 / BLS12-381 families), which the successor call loop
reports as out of domain rather than guessing. -/
def cryptoHostCall (name : String) : Option (HM Unit) :=
  match name with
  | "ecrecover" => some do hostEcrecover (← popArgs 7)
  | "p256_verify" => some do hostP256Verify (← popArgs 6)
  | _ => none

end NearSpecV3.Wasm
