import NearSpecV3.Wasm.Host
import NearSpecV3.Secp256k1
import NearSpecV3.P256
import NearSpecV3.BLS12381
import NearSpecV3.BLS12381Pairing

/-!
# Host semantics of the crypto host functions (successor domain `D3γ`)

`ecrecover` (`runtime/near-vm-runner/src/wasmtime_runner/logic.rs:1668-1757`) and `p256_verify`
(`wasmtime_runner/logic.rs:1884-1950`) as host computations in `HM`, with nearcore's **order of charges and
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

/-- `ecrecover` (`wasmtime_runner/logic.rs:1668-1757`). Arguments are the wasm operands in declaration order:
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

/-- `p256_verify` (`wasmtime_runner/logic.rs:1884-1950`). Arguments in declaration order:
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

/-! ## BLS12-381 (`bls12381_*`, 9 hosts)

All nine hosts share the `bls12381_impl!` shape (`wasmtime_runner/logic.rs:33-83`) except
`pairing_check`, which has its own body (`wasmtime_runner/logic.rs:1352-1376`). The difference
matters for gas and for the error/return split:

* `bls12381_impl!` — `pay_base`, `pay_per(element, len / ITEM_SIZE)`, **then** read the input, then
  decode. A length that is not a multiple of `ITEM_SIZE` still pays base and `len / ITEM_SIZE`
  elements, then raises `BLS12381InvalidInput` from `check_input_size`
  (`logic/bls12381.rs:438-452`).
* `bls12381_pairing_check` — `pay_base`, **then read**, then `pay_per(pairing_element, len / 288)`,
  then decode. So an out-of-bounds read burns base + the read cost but no per-element charge.

Gas values are the PV86 `parameters.snap:184-201` keys (the same numbers `parameters.yaml` carries).
Compute costs equal gas costs for every one of these keys (no `compute:` annotation in the snapshot),
so only gas is modelled. Each call additionally pays the generic read/write charges of `Wasm.Host`.

Return split: success returns `0` and writes the payload to `register_id`; a decode/curve/subgroup
failure returns `1` and writes nothing. `pairing_check` writes nothing at all and returns
`0` (product `= 1`), `1` (malformed / not in G1 or G2) or `2` (product `≠ 1`)
(`wasmtime_runner/logic.rs:1333-1340`).

`bls12381_not_in_group_fix` is **false** at PV86 (`parameters.snap:289`), so every decode runs at
`version = 0` and rejects the `(0, ±2)` subgroup corner case in `sum` and `decompress`
(`logic/bls12381.rs:17-28`, NEP-488). -/

/-- `wasm_bls12381_p1_sum_base` / `_element` (`parameters.snap:184-185`). -/
def p1SumBase : Cost := ⟨16500000000, 16500000000, none⟩
def p1SumElement : Cost := ⟨6000000000, 6000000000, none⟩
/-- `wasm_bls12381_p2_sum_base` / `_element` (`parameters.snap:186-187`). -/
def p2SumBase : Cost := ⟨18600000000, 18600000000, none⟩
def p2SumElement : Cost := ⟨15000000000, 15000000000, none⟩
/-- `wasm_bls12381_g1_multiexp_base` / `_element` (`parameters.snap:188-189`). -/
def g1MultiexpBase : Cost := ⟨16500000000, 16500000000, none⟩
def g1MultiexpElement : Cost := ⟨930000000000, 930000000000, none⟩
/-- `wasm_bls12381_g2_multiexp_base` / `_element` (`parameters.snap:190-191`). -/
def g2MultiexpBase : Cost := ⟨18600000000, 18600000000, none⟩
def g2MultiexpElement : Cost := ⟨1995000000000, 1995000000000, none⟩
/-- `wasm_bls12381_map_fp_to_g1_base` / `_element` (`parameters.snap:192-193`). -/
def mapFpToG1Base : Cost := ⟨1500000000, 1500000000, none⟩
def mapFpToG1Element : Cost := ⟨252000000000, 252000000000, none⟩
/-- `wasm_bls12381_map_fp2_to_g2_base` / `_element` (`parameters.snap:194-195`). -/
def mapFp2ToG2Base : Cost := ⟨1500000000, 1500000000, none⟩
def mapFp2ToG2Element : Cost := ⟨900000000000, 900000000000, none⟩
/-- `wasm_bls12381_pairing_base` / `_element` (`parameters.snap:196-197`). -/
def pairingBase : Cost := ⟨2130000000000, 2130000000000, none⟩
def pairingElement : Cost := ⟨2130000000000, 2130000000000, none⟩
/-- `wasm_bls12381_p1_decompress_base` / `_element` (`parameters.snap:198-199`). -/
def p1DecompressBase : Cost := ⟨15000000000, 15000000000, none⟩
def p1DecompressElement : Cost := ⟨81000000000, 81000000000, none⟩
/-- `wasm_bls12381_p2_decompress_base` / `_element` (`parameters.snap:200-201`). -/
def p2DecompressBase : Cost := ⟨15000000000, 15000000000, none⟩
def p2DecompressElement : Cost := ⟨165000000000, 165000000000, none⟩

/-- The protocol version the hosts run at: `bls12381_not_in_group_fix = false` at PV86
(`parameters.snap:289`) selects `version = 0` (`logic/bls12381.rs:17-28`). Kept as a named constant
so the post-NEP-488 behaviour is one edit away. -/
def bls12381Version : Nat := 0

/-- `BLS12381InvalidInput`'s payload for `check_input_size` (`logic/bls12381.rs:438-450`), formatted
as nearcore's `Display` prints the variant: `BLS12-381 invalid input: {msg}`
(`logic/errors.rs:622`). `hErr` supplies the surrounding `HostError(...)`, so this string must not
repeat it. -/
def blsInvalidLength (fnName : String) (len item : Nat) : String :=
  s!"BLS12-381 invalid input: Incorrect input length for {fnName}: {len} is not divisible by {item}"

/-- The shared `bls12381_impl!` body: base, per-element, read, decode, then register write and `0`
on success or `1` on a decode failure. `decode` gets the whole input and returns `none` when the
host must return `1`. -/
def blsWriter (base element : Cost) (itemSize : Nat) (fnName : String)
    (decode : ArenaCore.Bytes → Option ArenaCore.Bytes) (a : Vector Nat 3) : HM Unit := do
  payBaseH base
  let len := a[0]; let ptr := a[1]; let reg := a[2]
  payPerH element (len / itemSize)
  let data ← memOrRegH ptr len
  if data.size % itemSize ≠ 0 then hErr (blsInvalidLength fnName data.size itemSize)
  match decode data.toList with
  | some out => regSetH reg (ByteArray.mk out.toArray); pushRet 0
  | none => pushRet 1

/-- `bls12381_p1_sum` (`wasmtime_runner/logic.rs:1056-1099`): `[(sign: u8, p1: 96 B)]`, sign ∈ {0,1}, output the
96-byte sum. Decoding runs at `version = 0`, so `(0, ±2)` is rejected (`parse_p1`). -/
def hostP1Sum (a : Vector Nat 3) : HM Unit :=
  blsWriter p1SumBase p1SumElement 97 "bls12381_p1_sum" (fun d => BLS12381.p1Sum bls12381Version d) a

/-- `bls12381_p2_sum` (`wasmtime_runner/logic.rs:1101-1145`): `[(sign: u8, p2: 192 B)]`. -/
def hostP2Sum (a : Vector Nat 3) : HM Unit :=
  blsWriter p2SumBase p2SumElement 193 "bls12381_p2_sum" (fun d => BLS12381.p2Sum bls12381Version d) a

/-- `bls12381_g1_multiexp` (`wasmtime_runner/logic.rs:1147-1190`): `[(p1: 96 B, scalar: 32 B LE)]`, with the extra
`blst_p1_in_g1` subgroup gate on every point (`logic/bls12381.rs:185-187`). -/
def hostG1Multiexp (a : Vector Nat 3) : HM Unit :=
  blsWriter g1MultiexpBase g1MultiexpElement 128 "bls12381_p1_multiexp"
    (fun d => BLS12381.g1Multiexp bls12381Version d) a

/-- `bls12381_g2_multiexp` (`wasmtime_runner/logic.rs:1192-1236`): `[(p2: 192 B, scalar: 32 B LE)]`. -/
def hostG2Multiexp (a : Vector Nat 3) : HM Unit :=
  blsWriter g2MultiexpBase g2MultiexpElement 224 "bls12381_p2_multiexp"
    (fun d => BLS12381.g2Multiexp bls12381Version d) a

/-- `bls12381_p1_decompress` (`wasmtime_runner/logic.rs:1378-1420`): `[compressed p1: 48 B]`, output 96 B. At
`version = 0` this goes through `blst::min_pk::PublicKey::uncompress`
(`logic/bls12381.rs:214-224`), which rejects the `(0, ±2)` subgroup case. -/
def hostP1Decompress (a : Vector Nat 3) : HM Unit :=
  blsWriter p1DecompressBase p1DecompressElement 48 "bls12381_p1_decompress"
    (fun d => BLS12381.p1Decompress bls12381Version d) a

/-- `bls12381_p2_decompress`: `[compressed p2: 96 B]`, output 192 B. -/
def hostP2Decompress (a : Vector Nat 3) : HM Unit :=
  blsWriter p2DecompressBase p2DecompressElement 96 "bls12381_p2_decompress"
    (fun d => BLS12381.p2Decompress bls12381Version d) a

/-- `bls12381_map_fp_to_g1` (`wasmtime_runner/logic.rs:1238-1274`): `[fp: 48 B]` per element, output 96 B per element.
A non-canonical `Fp` (`>= p`) is a `1` return, not an error. -/
def hostMapFpToG1 (a : Vector Nat 3) : HM Unit :=
  blsWriter mapFpToG1Base mapFpToG1Element 48 "bls12381_map_fp_to_g1"
    (fun d => BLS12381.mapFpToG1 d) a

/-- `bls12381_map_fp2_to_g2` (`wasmtime_runner/logic.rs:1276-1312`): `[fp2: 96 B]` per element, output 192 B per
element. -/
def hostMapFp2ToG2 (a : Vector Nat 3) : HM Unit :=
  blsWriter mapFp2ToG2Base mapFp2ToG2Element 96 "bls12381_map_fp2_to_g2"
    (fun d => BLS12381.mapFp2ToG2 d) a

/-- `bls12381_pairing_check` (`wasmtime_runner/logic.rs:1352-1376`): `[(p1: 96 B, p2: 192 B)]`, no register,
returns `0`/`1`/`2`. Note the charge order: base, **read**, per-element, decode. Unlike the eight
`bls12381_impl!` writers — which divide the *operand* `value_len` — this body computes
`elements_count = data.len() / ITEM_SIZE` from the **read data** (`wasmtime_runner/logic.rs:1371`), so a
register-sourced input (`value_len = u64::MAX`) is charged for the register's own length. -/
def hostPairingCheck (a : Vector Nat 2) : HM Unit := do
  payBaseH pairingBase
  let len := a[0]; let ptr := a[1]
  let data ← memOrRegH ptr len
  payPerH pairingElement (data.size / 288)
  if data.size % 288 ≠ 0 then hErr (blsInvalidLength "bls12381_pairing_check" data.size 288)
  pushRet (BLS12381.pairingCheck data.toList)

/-- `cryptoHostCall`: the `D3γ` host table. `none` for every name whose semantics is not
implemented yet (the alt_bn128 family), which the successor call loop reports as out of domain
rather than guessing. -/
def cryptoHostCall (name : String) : Option (HM Unit) :=
  match name with
  | "ecrecover" => some do hostEcrecover (← popArgs 7)
  | "p256_verify" => some do hostP256Verify (← popArgs 6)
  | "bls12381_p1_sum" => some do hostP1Sum (← popArgs 3)
  | "bls12381_p2_sum" => some do hostP2Sum (← popArgs 3)
  | "bls12381_g1_multiexp" => some do hostG1Multiexp (← popArgs 3)
  | "bls12381_g2_multiexp" => some do hostG2Multiexp (← popArgs 3)
  | "bls12381_p1_decompress" => some do hostP1Decompress (← popArgs 3)
  | "bls12381_p2_decompress" => some do hostP2Decompress (← popArgs 3)
  | "bls12381_map_fp_to_g1" => some do hostMapFpToG1 (← popArgs 3)
  | "bls12381_map_fp2_to_g2" => some do hostMapFp2ToG2 (← popArgs 3)
  | "bls12381_pairing_check" => some do hostPairingCheck (← popArgs 2)
  | _ => none

end NearSpecV3.Wasm
