# L3 crypto and key coverage — inventory of the 15 missing rows

Date: 2026-10-23. Lane L3 of `docs/requirements/LEAN_CHUNK_TRANSITION_PLAN.md` §4 L3.
Worktree `lean-chunk-L3`, branch `lane/lean-chunk-L3`, base `a5ef42e0c` (L0 inventory merged).
Pinned target: nearcore `44f7ae6cd7ef08bab604e20a473bf77e35d4c993`, PV 86.

This document is the plan's required "inventory actual missing paths before implementation".
It records, for each of the 14 curve hosts plus the exclusion guard, the exact signature, input
and output encoding, error/return convention and **host gas**, with `file:line` citations into the
pinned nearcore, and what is now implemented in Lean. Statuses are in the plan's vocabulary and
are honest about the difference between *implemented at the host* and *exercised through a whole
chunk*.

Gas values are read from the PV86 snapshot `core/parameters/res/runtime_configs/parameters.snap`
(the same numbers are in `parameters.yaml`, which is the mainnet config the snapshot is generated
from). Compute costs equal gas costs for every one of these hosts (no `compute:` annotation in the
snapshot for these keys), so only gas is listed. All 14 hosts additionally pay the generic input
cost of `logic.rs:85-136`: `base` per host call is charged by the wasm layer, and each input read
pays `read_memory_base + len·read_memory_byte` (memory) or `read_register_base + len·read_register_byte`
(register, `len = u64::MAX`); each register write pays `write_register_base + len·write_register_byte`.
Those generic costs are already modelled in `Wasm.Host` (`readMemH`, `regSetH`, `memOrRegH`).

Common source facts:

* Import table and Wasm-visible signatures: `runtime/near-vm-runner/src/imports.rs:145-161`
  (`ed25519_verify`, `p256_verify`, `ecrecover`) and `:354-368` (alt_bn128 / BLS12-381), mirrored in
  the Lean `Wasm.HostSigs.hostSigs` (`HostSigs.lean:37-39,84-95`).
* `get_memory_or_register` (`logic.rs:134-146`): a length of `u64::MAX` means "the value is register
  `ptr`". Charge order everywhere: base cost, then each input as it is read, then the
  host-specific per-element cost, then the register write.
* Production enablement: all 14 are unconditionally in the `env` table at PV86
  (`imports.rs:354-368`); `p256_verify` is gated by `p256_verify_host_fn`, which is `true` from PV85
  (`runtime_configs/85.yaml:4`, `parameters.snap:286`). `ed25519_verify` has no gate.
  `bls12381_not_in_group_fix` is **false** at PV86 (`parameters.snap:289`), i.e. the BLS hosts run
  with `BLS12381_NOT_IN_GROUP_FIX_VERSION = 0` (`logic/bls12381.rs:17-28`), which rejects the
  `(0, ±2)` subgroup corner case that version 1 accepts.

| host | Lean status after L3 | what exists |
|---|---|---|
| `ecrecover` | `partial` | full secp256k1 recovery + host arm with exact charge order, 161 nearcore vectors + 23 host cases; no whole-chunk case |
| `ed25519_verify` (L4 row) | `implemented` (unchanged) | host arm `Host.lean:1024-1033` over `Ed25519.verify`; whole-chunk cases exist (see §3) |
| `p256_verify` | `partial` | full P-256 verification + host arm with exact charge order, 8 Wycheproof vectors + 9 gates + 13 host cases; no whole-chunk case |
| 12 alt_bn128 / BLS12-381 hosts | `missing` | nothing |
| `L0-W-015` (guard) | `missing` (guard is as designed) | kernel-checked `hostCall_no_arm` for all 14 names + 411-case OOD replay |

## 1. Per-host inventory

### 1.1 `ecrecover` — implemented (host level)

* Signature: `ecrecover<[hash_len, hash_ptr, sig_len, sig_ptr, v, malleability_flag, register_id]
  -> [u64]>` (`imports.rs:160`); Rust `logic.rs:1668-1770`.
* Input: 64-byte `r ‖ s` (`sig_len` must be 64, else `ECRecoverError`), 32-byte hash (`hash_len`
  must be 32, else `ECRecoverError`), `v ∈ {0,1,2,3}` (else `ECRecoverError`),
  `malleability_flag ∈ {0,1}` (else `ECRecoverError`).
* Output: `u64` `1` on success **and** the 64-byte uncompressed key `X ‖ Y` (big-endian, no `0x04`
  prefix: `signature.rs:992-1003` slices `serialize_uncompressed()[1..65]` into a
  `Secp256K1PublicKey([u8; 64])`, `signature.rs:112-120`) written to `register_id`; `0` on failure
  with **no** register write.
* Return/error split (`logic.rs:1679-1768`): malformed **lengths**, `v ≥ 4` and a bad
  malleability flag are host errors; an out-of-range `(r, s)` or an unrecoverable signature is a
  `0` return. Order: base → read sig → length check → `v` check → read hash → hash length check →
  flag check → `check_signature_values` → recover.
* Semantics: `Secp256K1Signature::check_signature_values` (`core/crypto/src/signature.rs:959-977`,
  constants `:947-952`) then `recover` (`:979-1004`), i.e. libsecp256k1
  `ecdsa_recover` (`secp256k1-sys` 0.8.1 —
  `depend/secp256k1/src/modules/recovery/main_impl.h:87-113,138-158`): `r, s ≠ 0`; `x = r` (or
  `r + n` for `recid & 2`, requiring `r < p − n`); decompress with parity `recid & 1`;
  `Q = r⁻¹(sR − mG)` with `m` the hash reduced mod `n`; `Q = ∞` fails.
* Gas: `ecrecover_base = 278_821_988_457` (`parameters.snap:137`; lowered from
  3_365_369_625_000 by `48.yaml:2`), plus the reads (2 × `read_memory_base` + 96 ×
  `read_memory_byte` for the two inputs) and, only on success, `write_register_base + 64 ×
  write_register_byte`. The doc comment at `logic.rs:1667` states exactly this.
* Lean: `NearSpecV3/Secp256k1.lean` (`checkSigValues`, `recover`), `Wasm/CryptoHost.lean`
  (`ecrecoverBase`, `hostEcrecover`, `cryptoHostCall`). Tests: `oracle/wasm-d3/lean/CryptoTest.lean`
  (`nearspec-v3-test-crypto`, modes `vectors`/`edge`/`host`).

### 1.2 `p256_verify` — implemented (host level)

* Signature: `p256_verify<[sig_len, sig_ptr, msg_len, msg_ptr, pk_len, pk_ptr] -> [u64]>`
  (`imports.rs:152`); Rust `logic.rs:1884-1930`.
* Input: 64-byte `r ‖ s` P-256 signature (`Signature::from_slice`; a well-sized but unparseable
  `(r,s)` — `r`/`s` zero or `≥ n` — returns `0`); arbitrary-length **prehashed** message (NEP-635:
  the host does not hash; `bits2field` pads short inputs on the left and truncates long ones,
  `ecdsa-0.16.9/src/hazmat.rs:185-206`); 33-byte compressed SEC1 public key (`from_sec1_bytes`,
  parse failure returns `0`).
* Output: `u64` `1`/`0`; never writes a register.
* Return/error split: `sig_len ≠ 64` and `pk_len ≠ 33` are `P256VerifyInvalidInput` host errors;
  every parse or verification failure is `0`. Note the asymmetry against `ecrecover`: p256 checks
  the **message before the public key**, and pays `p256_verify_byte × msg.len()` in between.
* Verification: RustCrypto `p256` 0.13.2 (`verify_prehash`): `z = bits2field(msg) mod n`,
  `u1 = z·s⁻¹`, `u2 = r·s⁻¹`, accept iff `x(u1·G + u2·Q) mod n = r`. **No low-s enforcement**
  (`logic/tests/p256_verify_wycheproof.rs:15-20`: high-s is accepted, deliberately).
* Gas: `p256_verify_base = 1_300_000_000_000`, `p256_verify_byte = 13_000_000`
  (`parameters.snap:140-141`), plus the three input reads.
* Lean: `NearSpecV3/P256.lean` (`bits2field`, `sigOk`, `decompress`, `verify`),
  `Wasm/CryptoHost.lean` (`p256VerifyBase`, `p256VerifyByte`, `hostP256Verify`,
  `cryptoHostCall`). Tests in `CryptoTest.lean` modes `p256` (8 Wycheproof vectors + 9 directed
  gates) and `p256host` (13 gas/return/error cases).

### 1.3 `ed25519_verify` — implemented (L4's row, verified here)

* Signature: `ed25519_verify<[sig_len, sig_ptr, msg_len, msg_ptr, pk_len, pk_ptr] -> [u64]>`
  (`imports.rs:145`); Rust `logic.rs:1783-1857`.
* Input: 64-byte signature, arbitrary message, 32-byte public key.
* Return/error split: `sig_len ≠ 64` → `Ed25519VerifyInvalidInput`; then the pre-dalek-2 check
  `sig[63] & 0xE0 ≠ 0` returns `0` **before reading the message** (so the message read is not
  charged); `msg` read and charged `ed25519_verify_byte × len`; `pk_len ≠ 32` →
  `Ed25519VerifyInvalidInput`; a non-decompressible key returns `0`; otherwise
  `ed25519_dalek::Verifier::verify`.
* Gas: `ed25519_verify_base = 210_000_000_000`, `ed25519_verify_byte = 9_000_000`
  (`parameters.snap:138-139`).
* Lean: `Wasm/Host.lean:1024-1033` shares `NearSpecV3.Ed25519.verify` with D1/D2 transaction
  signatures (`Ed25519.lean:8-74`), including the `sig[63] & 0xE0` early return and both length
  errors. `curveHosts` does **not** contain `ed25519_verify`
  (`D3/CryptoDomain.ed25519_not_excluded`, by `decide`), and `hostCall` does have an arm
  (`ed25519_has_arm`, by `decide`). The L0 inventory row is `L0-host-ed25519_verify`, owner L4.

### 1.4 alt_bn128 family (3 hosts) — missing

Curve: `y² = x³ + 3` over `Fq`, `q = 21888242871839275222246405745257275088696311157297823662689037894645226208583`;
scalars in `Fr` of order
`21888242871839275222246405745257275088548364400416034343698204186575808495617`. Encoding is
**little-endian u256** (`logic/alt_bn128.rs:156-161`, `decode_u256` splits two 16-byte LE halves).

| host | input element | size | return |
|---|---|---|---|
| `alt_bn128_g1_multiexp<[value_len, value_ptr, register_id] -> []>` | `(g1: 64 B, fr: 32 B)` | 96 | **no** return value: writes 64-byte point to the register, or `AltBn128InvalidInput` |
| `alt_bn128_g1_sum<[value_len, value_ptr, register_id] -> []>` | `(sign: u8, g1: 64 B)` | 65 | as above |
| `alt_bn128_pairing_check<[value_len, value_ptr] -> [u64]>` | `(g1: 64 B, g2: 128 B)` | 192 | `1` iff `∏ e(g1,g2) = 1`, else `0`; malformed input is `AltBn128InvalidInput` |

* Sources: `imports.rs:354-356`; Rust `logic.rs:932-1055`; decoding/encoding
  `logic/alt_bn128.rs:25-104` (`split_elements`, `decode_g1`, `decode_g2`, `decode_fq`, `decode_fr`,
  `decode_bool`; `(0,0)` decodes as the point at infinity; every other `(x,y)` must satisfy the
  curve equation, and scalars must be `< Fr` — no subgroup check for G1, which is safe because
  `G1` is prime order).
* Gas (`parameters.snap:173-178`): multiexp `713_000_000_000 + 320_000_000_000·n`;
  g1_sum `3_000_000_000 + 5_000_000_000·n`; pairing `9_686_000_000_000 + 5_102_000_000_000·n`.
  The Rust code charges the per-element cost **before** the input read for multiexp/g1_sum
  (`logic.rs:939-951`: `pay_base`, read, `split_elements`, `pay_per`) — note the split happens
  before `pay_per`, so a length that is not a multiple of the element size pays base + the read
  and then errors without the per-element charge. For pairing it is the same
  (`logic.rs:1040-1052`).
* Implementation cost in Lean: full `Fq`/`Fr` arithmetic, G1 affine/Jacobian arithmetic, Fq2,
  G2 on the twist, Miller loop + final exponentiation for the pairing. The last is the expensive
  one (a correct `ate` pairing plus `Fq12` arithmetic, ~1–2k lines) and is the reason this lane
  stopped at the two "pure verification" hosts.

### 1.5 BLS12-381 family (9 hosts) — missing

Curve `y² = x³ + 4` over `Fp`, `p = 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787`;
encoding is **big-endian 48-byte `Fp`**; `Fp2` elements are `c1 ‖ c0` (`logic/bls12381.rs:6-13` for
the sizes). The `bls12381_impl!` macro (`logic.rs:33-105`) defines the common shape:
`pay_base`, `pay_per(element, value_len / ITEM_SIZE)`, read the input, run blst, then on success
write the register and return `0`; on a decode/curve failure return `1` **without** writing the
register. Lengths that are not multiples of `ITEM_SIZE` are `BLS12381InvalidInput` with the message
`Incorrect input length for <fn>: <len> is not divisible by <item>` (`logic/bls12381.rs:438-450`).

| host | element | size | output |
|---|---|---|---|
| `bls12381_p1_sum` | `(sign: u8, p1: 96 B)` | 97 | 96 B, `0`/`1` |
| `bls12381_p2_sum` | `(sign: u8, p2: 192 B)` | 193 | 192 B, `0`/`1` |
| `bls12381_g1_multiexp` | `(p1: 96 B, scalar: 32 B LE)` | 128 | 96 B, `0`/`1` |
| `bls12381_g2_multiexp` | `(p2: 192 B, scalar: 32 B LE)` | 224 | 192 B, `0`/`1` |
| `bls12381_map_fp_to_g1` | `fp: 48 B` | 48 | 96 B, `0`/`1` |
| `bls12381_map_fp2_to_g2` | `fp2: 96 B` | 96 | 192 B, `0`/`1` |
| `bls12381_p1_decompress` | `compressed p1: 48 B` | 48 | 96 B, `0`/`1` |
| `bls12381_p2_decompress` | `compressed p2: 96 B` | 96 | 192 B, `0`/`1` |
| `bls12381_pairing_check` | `(p1: 96 B, p2: 192 B)` | 288 | **no** register; returns `0` (product `= 1`), `1` (invalid / not in group), `2` (product `≠ 1`) |

* Sources: `imports.rs:360-368`; Rust `logic.rs:1056-1520` (the eight `bls12381_impl!` uses) and
  `logic.rs:1340-1370` (`bls12381_pairing_check`, which pays `base`, reads, then `pay_per` on
  `len / 288`); decode/verify `logic/bls12381.rs:120-360` (blst `*_deserialize`, `*_in_g1`/`_in_g2`,
  `*_uncompress`, `*_map_to_g1/g2`); the three return codes for `pairing_check` are documented at
  `logic.rs:1329-1338` and implemented at `logic/bls12381.rs:330-410`.
* Gas (`parameters.snap:184-201`): p1_sum `16_500_000_000 + 6_000_000_000·n`;
  p2_sum `18_600_000_000 + 15_000_000_000·n`; g1_multiexp `16_500_000_000 + 930_000_000_000·n`;
  g2_multiexp `18_600_000_000 + 1_995_000_000_000·n`; map_fp_to_g1 `1_500_000_000 +
  252_000_000_000·n`; map_fp2_to_g2 `1_500_000_000 + 900_000_000_000·n`;
  pairing `2_130_000_000_000 + 2_130_000_000_000·n`; p1_decompress `15_000_000_000 +
  81_000_000_000·n`; p2_decompress `15_000_000_000 + 165_000_000_000·n`. (These are the PV70
  values from `runtime_configs/70.yaml`; before PV70 every BLS host cost a flat
  300_000_000_000_000, which is why the L0 evidence table shows the "not modelled" cost as
  unreachable in practice at PV86.)
* PV86 quirk: `bls12381_not_in_group_fix = false` (`parameters.snap:289`) selects
  `version = 0`, i.e. the pre-NEP-488 behaviour that rejects the `(0, ±2)` corner case in `sum`
  and `decompress` (`logic/bls12381.rs:17-28`). Any Lean transcription must special-case it.
* Implementation cost in Lean: `Fp`, `Fp2`, `Fp6`, `Fp12`, G1/G2 arithmetic, the SSWU map and a
  pairing. The maps and the pairing are the expensive parts; the `sum`/`multiexp`/`decompress`
  hosts need only G1/G2 arithmetic and square roots (still a few hundred lines each).

## 2. The exclusion guard `L0-W-015`

The guard is two-layered (see `D3/CryptoDomain.lean` for the exact statements):

1. `Exec.runCall` with the mock `External` (`real := none`) rejects a module that merely *imports*
   a curve host: `Exec.lean:462-464`.
2. Under the chunk path (`real := some _`), `Wasm.Host.hostCall` has no arm for the 14 names, so
   `Exec.callHost` yields `.unmodeled "host function … not modelled in D3α"` (`Exec.lean:77-80`),
   and `D3.functionCall` converts that to `out of domain (e.wasm-α)` (`D3/FunctionCall.lean:365-368`).
   Importing one is **in domain** (spec §10.0a P3) — `d3hostx`'s `run` does exactly that, which is
   why the corpus has in-domain cases whose contract imports `ecrecover`.

Kernel checks added: `hostCall_no_arm` (all 14 names, by `decide`), `ed25519_not_excluded`,
`ed25519_has_arm`, and `cryptoHosts_iff_curveHosts` (the successor name list is the guard list).

Replay evidence: all 411 `ood/` cases of the d3c9 corpus were run through `checkD3`; see §4.

## 3. Whole-chunk evidence for the `ed25519_verify` host path

`d3ed` (`oracle/v3-d3/contracts/d3ed.wat`) reads `sig ‖ pk ‖ msg` from the input, calls
`ed25519_verify`, and writes the `u64` result to storage key `v`. Because the chunk's post-state
root commits to that write, a case that `checkD3` accepts proves Lean's returned bit equals
nearcore's for that input — the state root is the oracle, not a hypothesis.

21 d3c9 `d3/` cases execute `d3ed`; the corpus meta records one of the receipts failing with
`FunctionCallError:ExecutionError:ED25519_signature_verification_error` in several of them, i.e.
the host **error** branch (signature length ≠ 64, `Host.lean:1029`) is exercised through a real
chunk, and the remaining calls exercise the `0` return (the generator feeds random bytes,
`d3gen.rs:580-585`, so a *valid* signature is not among them). This is why the row is
`implemented`, not `validated`: the error and the invalid-signature paths are whole-chunk
covered, the valid-signature path is covered only by the `oracle/fixtures/v3/ed25519` vectors
(`nearspec-v3-test-ed25519`), not by a chunk.

## 4. Replay of the OOD corpus (guard regression)

`nearspec-v3-check-d3 ood/*` over `/data/illia/nearproof-deps/corpora/d3c9/ood` (411 cases):
verdict counts and the per-case comparison against `meta.json`'s `expected_rel_d3` are in the
handoff log. Every case is `out_of_domain` or `reject`, none is `accept`, matching
`expected_rel_d3 = false` for all 411 — the guard still rejects exactly the excluded set.

## 5. Judged infeasible in this lane's budget

* Wiring `ecrecover` into `Wasm.runCall` (so a whole chunk can execute it) requires a second host
  table threaded through `Exec.callFunc`/`exec`/`step` and a matching `Logged` mirror
  (`Logged/WasmRun.lean:122-160`, `Logged/WasmStepE.lean:174-205`, `Logged/WasmCRHostCall.lean`),
  whose commutation proof `CR` for the new arms I could not close (the `cr` tactic leaves the
  arithmetic goal; a 2-minute attempt is recorded in the log). Since `checkD3`'s definitional
  closure must stay unchanged, this was left out rather than half-landed.
* The alt_bn128 and BLS12-381 families need curve arithmetic plus (for `pairing_check`) an
  `Fq12` Miller loop and final exponentiation. Both are implementable in the same style as
  `Secp256k1.lean`, but not within this lane's remaining budget, and a rushed pairing would be a
  correctness risk with no vector coverage.
* ML-DSA-65 key/signature variants (mentioned in the plan's L3 paragraph) are not among the 15
  rows L0 assigned to L3; `d3hostx mlkey` cases are `out of domain (w.shape)/(e.mldsa_key)`
  (L4 boundary), so they were only noted, not touched.
