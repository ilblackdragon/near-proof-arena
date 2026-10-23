# L3 — cryptographic and key coverage (handoff)

Date: 2026-10-23. Plan lane: `docs/requirements/LEAN_CHUNK_TRANSITION_PLAN.md` §4 L3, §5.

| field | value |
|---|---|
| owner | L3 (crypto and key coverage) |
| worktree | `/data/illia/nearproof-wt/lean-chunk-L3` |
| branch | `lane/lean-chunk-L3` |
| base commit | `a5ef42e0c` (L1's protocol-derived gas bound; L0 inventory `d261f1f07` merged below it) |
| committed tip | recorded in the reply (lane commits: `2d323b334`, `b41ae3897`, `d68a6c113`, `fcf6a9a41`, `6fee516a4`, `e6f895540`, `32311d125`, plus the drift-gate regeneration) |
| target | nearcore `44f7ae6cd7ef08bab604e20a473bf77e35d4c993`, PV 86 |
| scope | the 15 `owner == "L3"` rows of `docs/research/lean-chunk-coverage.json` (14 curve hosts + `L0-W-015`) |

## 1. Result summary

**Two real implementations landed: `ecrecover` and `p256_verify`**, each with both the arithmetic
and the host-function semantics in nearcore's exact charge order. `ecrecover` is validated against nearcore's own 161-vector suite (byte
equality of the recovered public key, not a validity bit) plus 20 directed edge cases and 23
host-level cases that check burnt/used gas per branch, the register contents, and the error text;
`p256_verify` against the 8 Wycheproof vectors in nearcore's test file, 9 directed gates and 13
host-level gas/return/error cases.

Both are `partial`, not `implemented`/`validated`. The plan's L3 acceptance requires
"at least one valid and invalid whole-chunk case per supported entry path". No chunk in any corpus
executes either host inside a domain that the current checker accepts (`p256_verify` is not called
by any corpus contract at all; the 83 `ecrecover` cases are all `out of domain (e.wasm-α)` by
construction), and enabling a host inside `Wasm.runCall` is not additive (see §6). The arithmetic and the host layer are real for both hosts; the
whole-chunk rung is missing for both, so both rows say so.

`ed25519_verify` (L4's row, asked to be verified) **is** real and is exercised through whole
chunks; the evidence is recorded in §4. The remaining 12 curve hosts stay `missing`.

| inventory id | final status | one-line basis |
|---|---|---|
| `L0-host-ecrecover` | **partial** | `Secp256k1.recover` + `CryptoHost.hostEcrecover`; 161/161 vectors, 20 edge, 23 host cases; no whole-chunk |
| `L0-host-p256_verify` | **partial** | `P256.verify` + `CryptoHost.hostP256Verify`; 8 Wycheproof + 9 gates + 13 host cases; no whole-chunk |
| `L0-host-alt_bn128_g1_multiexp` | missing | needs Fq/Fr + G1 arithmetic |
| `L0-host-alt_bn128_g1_sum` | missing | same |
| `L0-host-alt_bn128_pairing_check` | missing | needs Fq2 + Miller loop + final exponentiation |
| `L0-host-bls12381_g1_multiexp` | missing | needs Fp + G1 |
| `L0-host-bls12381_g2_multiexp` | missing | needs Fp2 + G2 |
| `L0-host-bls12381_map_fp_to_g1` | missing | needs SSWU map |
| `L0-host-bls12381_map_fp2_to_g2` | missing | needs SSWU map over Fp2 |
| `L0-host-bls12381_p1_sum` | missing | needs Fp + G1 + the PV86 `not_in_group_fix = false` quirk |
| `L0-host-bls12381_p2_sum` | missing | needs Fp2 + G2 + the same quirk |
| `L0-host-bls12381_p1_decompress` | missing | needs Fp sqrt + sign convention |
| `L0-host-bls12381_p2_decompress` | missing | needs Fp2 sqrt + the same quirk |
| `L0-host-bls12381_pairing_check` | missing | needs Fp12 + pairing; 0/1/2 return codes |
| `L0-W-015` (guard) | missing (guard is as designed) | kernel-checked `hostCall_no_arm` for all 14; 411-case OOD replay, 0 diffs |

`tools/d3/lean_chunk_coverage.py --check` **passes** after teaching it about the successor table
(§5). Inventory totals: `implemented 91, impossible-at-boundary 3, missing 18, partial 2`
(114 rows). The changed rows versus the L0 baseline are `L0-host-ecrecover: missing → partial` and
`L0-host-p256_verify: missing → partial`.

## 2. Implemented behaviour

### 2.1 `NearSpecV3/Secp256k1.lean` (new, 272 lines)

* `p`, `n`, `nHalfOne`, `Gx`, `Gy` as literals; `F.{add,sub,mul,neg,pow,inv,sqrt}` over `F_p`;
  `N.{add,mul,neg,pow,inv}` over `F_n`.
* `J` (Jacobian, `Z = 0` = infinity), `J.dbl` (`dbl-2009-l`), `J.add` (`add-2007-bl`),
  `J.smul` (MSB-first 256-bit double-and-add), `J.affine`, `onCurve`, `decompress`.
* `checkSigValues sig rejectUpper` — nearcore `signature.rs:959-977`, `r < n ∧ s < (rejectUpper ?
  (n+1)/2 : n)`.
* `recover sig v hash : Option Bytes` — `signature.rs:979-1004` +
  `libsecp256k1 recovery/main_impl.h:87-113`: `r,s ≠ 0`; `x = r` or `r + n` for `v ≥ 2`
  (requiring `r < p − n`); parity `v % 2`; `Q = r⁻¹(sR − mG)` with `m = hash mod n`; `Q = ∞`
  fails; output `X ‖ Y` as 64 big-endian bytes.

Theorem statements (all proved, no `sorry`, no new axioms):

```lean
theorem p_eq : p = 115792089237316195423570985008687907853269984665640564039457584007908834671663
theorem n_eq : n = 115792089237316195423570985008687907852837564279074904382605163141518161494337  -- rfl
theorem nHalfOne_eq : nHalfOne = (n + 1) / 2
theorem p_mod_four : p % 4 = 3
theorem G_on_curve : onCurve Gx Gy = true
theorem G_not_inf : J.isInf (J.ofAffine Gx Gy) = false
theorem recover_none_of_sig_length  {sig v hash} (h : sig.length ≠ 64)  : recover sig v hash = none
theorem recover_none_of_hash_length {sig v hash} (h : hash.length ≠ 32) : recover sig v hash = none
theorem recover_none_of_v           {sig v hash} (h : ¬ v < 4)         : recover sig v hash = none
theorem checkSigValues_false_of_length {sig rejectUpper} (h : sig.length ≠ 64) :
  checkSigValues sig rejectUpper = false
theorem checkSigValues_mono {sig} (h : checkSigValues sig true = true) :
  checkSigValues sig false = true
```

Residual premises: none of these depend on a cryptographic assumption. What is **not** proved:
that `recover` equals libsecp256k1 (that is tested, §3), and that `p`/`n` are prime (used only by
the correctness argument, not by any statement above).

### 2.2 `NearSpecV3/Wasm/CryptoHost.lean` (new)

* `ecrecoverBase = 278_821_988_457` (`parameters.snap:137`), `p256VerifyBase`/`p256VerifyByte`
  declared for the next step (`parameters.snap:140-141`).
* `cryptoHosts` — the 14 guard names, same order and spelling as `Exec.curveHosts`.
* `hostEcrecover (a : Vector Nat 7) : HM Unit` — `logic.rs:1668-1770` in nearcore's order:
  `pay_base ecrecover_base`; read `sig` (memory or register); `sig.size ≠ 64` →
  `HostError(ECRecoverError { msg: "The length of the signature: …, exceeds the limit of 64
  bytes" })`; `v ≥ 4` → `ECRecoverError` (`"V recovery byte 0 through 3 are valid but was provided
  …"`); read `hash`; `hash.size ≠ 32` → `ECRecoverError`; `flag ∉ {0,1}` → `ECRecoverError`
  (`"Malleability flag needs to be 0 or 1, but is instead …"`); `!checkSigValues` → `pushRet 0`
  (no register write); `recover = some pk` → `regSetH reg pk` + `pushRet 1`; `none` → `pushRet 0`.
* `cryptoHostCall name : Option (HM Unit)` — the successor table; `ecrecover` only, everything
  else `none` (so the successor call loop would still report those as out of domain rather than
  guess).

### 2.3 `NearSpecV3/P256.lean` (new, 233 lines)

* `p`, `n`, `b`, `Gx`, `Gy`; `F`/`N` (add/sub/mul/neg/pow/inv, `sqrt` via `p ≡ 3 mod 4`).
* `J` Jacobian for `a = −3` (`dbl-2001-b`: `M = 3(X−Z²)(X+Z²)`), `J.add`, `J.smul`, `J.affineX`.
* `onCurve` (`y² = x³ − 3x + b`), `decompress` (SEC1 `0x02`/`0x03 ‖ X`).
* `bits2field` (`ecdsa-0.16.9/src/hazmat.rs:185-206`): `< 16` bytes is an error; `≤ 32` is
  left-padded; longer is truncated to 32 bytes; then reduced mod `n`.
* `sigOk` (`Signature::from_scalars`, `lib.rs:250-259`): `0 < r < n ∧ 0 < s < n`.
* `verify sig msg pk : Bool` — `x(u1·G + u2·Q) mod n = r` with `u1 = z·s⁻¹`, `u2 = r·s⁻¹`
  (`hazmat.rs:270-292`). No low-s rule, matching nearcore.

Theorem statements (proved, no `sorry`):

```lean
theorem p_eq : p = 115792089210356248762697446949407573530086143415290314195533631308867097853951
theorem n_eq : n = 115792089210356248762697446949407573529996955224135760342422259061068512044369  -- rfl
theorem p_mod_four : p % 4 = 3
theorem G_on_curve : onCurve Gx Gy = true
theorem verify_false_of_sig_length {sig msg pk} (h : sig.length ≠ 64) : verify sig msg pk = false
theorem verify_false_of_pk_length  {sig msg pk} (h : pk.length ≠ 33)  : verify sig msg pk = false
theorem bits2field_none {msg} (h : msg.length < 16) : bits2field msg = none
theorem verify_false_of_sig_not_ok {sig msg pk} (h : sigOk sig = false) : verify sig msg pk = false
```

### 2.4 `NearSpecV3/D3/CryptoDomain.lean` (new)

The guard facts, kernel-checked, plus the statement of what a successor relation must discharge:

```lean
theorem cryptoHosts_iff_curveHosts (n : String) : cryptoHosts.contains n = curveHosts.contains n
theorem hostCall_no_arm :
  hostCall "alt_bn128_g1_multiexp" = none ∧ … ∧ hostCall "ecrecover" = none ∧
  hostCall "p256_verify" = none                                   -- by decide, all 14
theorem ed25519_not_excluded : curveHosts.contains "ed25519_verify" = false
theorem ed25519_has_arm : (hostCall "ed25519_verify").isSome = true
```

Residual premises: none. These are facts about the existing `D3α` tables; **no** statement in this
module changes `checkD3`, `RelD3`, `ChallengeV3` or the signed statement.

## 3. Tests run and results

### 3.1 `ecrecover` vectors (nearcore's own suite)

`oracle/wasm-d3/lean/CryptoTest.lean`, mode `vectors`: the 161 entries of
`runtime/near-vm-runner/src/logic/tests/ecrecover-tests.json` (pinned nearcore), each evaluated as
`checkSigValues (flag) && recover` and compared byte-for-byte with the recorded `res`.

```
ecrecover vectors: 161 total, 35 recovered, 126 rejected, 0 mismatches
```

35 positive vectors compare the **64 recovered key bytes**, so the group law, the decompression,
the `v ≥ 2` path and the scalar inversion are all exercised by real outputs. The 126 negatives
cover out-of-range `r`/`s`, high-s rejection at `mc = true`, and unrecoverable signatures.

### 3.2 `ecrecover` edge cases

Mode `edge`, 20 directed cases, 0 failures: sig lengths 63/65, hash lengths 31/33, `v = 4`,
`r = 0`, `s = 0`, `r = n`, `s = n`, `r = 2^256−1`, the valid vector, an independent on-curve
check of the returned bytes, `recid 2/3` at `r = p − n` (must fail) , the high-s form accepted at
flag 0 / rejected at flag 1, `checkSigValues` accepting `r = 0`/`s = 0` (recovery is what rejects
them), and `r = s = 0` rejected by recovery.

### 3.3 `ecrecover` host cases (gas, return, register, errors)

Mode `host`, 23 cases, 0 failures. Expected gas is the nearcore formula, computed independently
from the parameter table:

`ecrecover_base + 2·read_memory_base + 96·read_memory_byte (+ write_register_base +
64·write_register_byte on success)`.

Covered: the valid vector (ret 1, register 3 = the key bytes, exact burnt **and** used gas);
`r = n` and high-s-at-flag-1 (ret 0, gas **without** the register write); `r = 0` (ret 0);
`sig_len = 63` (error, gas = base + one read of 63); `hash_len = 31` (error, gas = base + read 64 +
read 31); `v = 4` (error, gas = base + read 64 — the `v` gate is before the hash read); flag = 2
(error, gas = base + both reads); out-of-bounds `sig_len` (`MemoryAccessViolation` after base +
read base + len·byte).

### 3.3b `p256_verify` vectors and host cases

Mode `p256`: the 8 vectors of `logic/tests/p256_verify_wycheproof.rs` — nearcore's helper hashes
the message with SHA-256 and passes the digest as the prehash (NEP-635), so the Lean check does
the same — plus 9 directed gates (sig lengths 63/65, SEC1 tags `0x04`/`0x05`, 32-byte key,
`x = p` uncompressed-as-compressed, 15-byte message, the valid vector, a 16-byte message).

```
p256 vectors: 17 total, 0 failures
```

Mode `p256host`: 13 cases over `hostP256Verify` with expected gas computed from the parameter
table (`p256VerifyBase + read 64 + read 32 + 13_000_000·32 + read 33` on the valid path):

```
p256 host cases: 13 total, 0 failures
```

Covered: valid (ret 1, exact burnt/used); `r = s = 0` (ret 0, gas stops after the signature read —
`Signature::from_slice` fails before the message is read); `sig_len = 63` and `pk_len = 32`
(errors, with the message read and per-byte charged in between for the pk case); a `0x05` tag
(ret 0); an empty message (ret 0, no per-byte charge); `bits2field` padding.

### 3.4 Whole chunk

* `ed25519_verify` (L4 row, verified): 21 `d3/` cases of d3c9 execute `d3ed`, which writes the
  host's `u64` result to storage — so the chunk's post-state root commits to the bit Lean returned.
  All are accepted by `checkD3`; several have a receipt failing with
  `FunctionCallError:ExecutionError:ED25519_signature_verification_error`, i.e. the host **error**
  branch runs inside a real chunk; the rest exercise the `0` return (the generator feeds random
  bytes, `d3gen.rs:580-585`). A *valid* signature is not in the corpus; that path is covered by
  `nearspec-v3-test-ed25519` over `oracle/fixtures/v3/ed25519`, not by a chunk. This is exactly why
  the row stays `implemented` and is not claimed as `validated` here.
* `ecrecover`, `p256_verify`: **no** whole-chunk case. The corpus has 83 cases that call it (36 to `ecrecover`
  itself via `d3curve`/`d3hostx.curve`), all `out_of_domain` by design. They are recorded in the
  replay below and would be the natural positive whole-chunk suite once the host is wired into
  `runCall` (each is nearcore-`ok`, so acceptance is a real differential signal).

### 3.5 Guard replay (`L0-W-015`)

`nearspec-v3-check-d3 ood/*` over the 411 `ood/` cases of `/data/illia/nearproof-deps/corpora/d3c9`:

```
verdicts: out_of_domain 311, accept 100, reject 0
vs recorded baseline var/d3-runs/full-d3c9/lean.jsonl (ood subset): 0 differences
the 100 accepts are exactly the cases whose only d3 violation is c.no_resharding
   (a D2/claim-domain guard, not a curve guard); every case with e.ood_host is out_of_domain
cases that call a curve host: 83 -> 83 out_of_domain
cases whose executed contract imports ecrecover: 86 -> 85 out_of_domain, 1 accept
   (the accept is an import-only d3hostx `run`, import ≠ call; spec §10.0a P3)
```

Sample regression on the in-domain corpus: 150 random `d3/`+`mutants/` cases re-run against the
recorded baseline, **0** verdict differences, so adding `CryptoHost.lean`/`CryptoDomain.lean` did
not perturb `checkD3`.

## 4. Build / test commands and results

```
# spec package (the signed closure)
cd /data/illia/nearproof-wt/lean-chunk-L3/spec/lean/v3 && lake build
  -> Build completed successfully (162 jobs)

# checker + crypto test drivers (separate package, so the pinned lakefile is untouched)
cd .../oracle/wasm-d3/lean && lake build nearspec-v3-check-d3 nearspec-v3-test-crypto
  -> Build completed successfully (126 jobs)
  (the spec package builds 162 jobs, including the `Logged` layer and the signed
   `ChallengeChunkV3`/`ChallengeChunkV3Gas` modules, unchanged by this lane)
./.lake/build/bin/nearspec-v3-test-crypto          # vectors
./.lake/build/bin/nearspec-v3-test-crypto edge     # directed edges
./.lake/build/bin/nearspec-v3-test-crypto host
./.lake/build/bin/nearspec-v3-test-crypto p256
./.lake/build/bin/nearspec-v3-test-crypto p256host     # gas/return/error

# drift gate for the inventory (must pass)
cd /data/illia/nearproof-wt/lean-chunk-L3
python3 tools/d3/lean_chunk_coverage.py --repo . --nearcore /data/illia/nearproof-deps/nearcore \
        --check docs/research/lean-chunk-coverage.json
  -> "Lean chunk coverage matches pinned sources (research evidence only)"

# signed-surface pin check
make pin-check
  -> every oracle/v3 and oracle/v3-d1 pin OK (near-chunk-v3.draft.json classes d2-epoch,
     d3-calls, d3-callbacks, d3-nonwasm, d3-maxgas all `ok`)
```

Artifact hashes:

| artifact | sha256 |
|---|---|
| `oracle/wasm-d3/lean/.lake/build/bin/nearspec-v3-check-d3` | `528992988e0c72769fe909494b3e99a2dd3d4c78ad47ecf7acf7524603ecb42f` |
| baseline checker (plan worktree, for comparison) | `b4154b212fc482af99fafd4a1c4d5cf6b1157f4e26c154fc1a66e907312ce5d8` |
| `docs/research/lean-chunk-coverage.json` | regenerate with the command above (drift-gated) |

Axiom audit (`lake env lean` over `#print axioms` on the new theorems):
`checkSigValues_mono`, `recover_none_of_v`, `verify_false_of_sig_not_ok`,
`cryptoHosts_iff_curveHosts` → `[propext]`; `hostCall_no_arm` →
`[propext, Classical.choice, Quot.sound]`; `G_on_curve` (both curves) → none.
No `sorryAx`, no new axioms, no `native_decide`, no `partial def` in the four new modules.

The checker digest differs from the recorded baseline only because `Secp256k1.lean`,
`CryptoHost.lean` and `CryptoDomain.lean` are now in the package; on the corpora the verdicts are
identical (§3.5). `checkD3`'s definition and the `near-chunk-v3` statement were not edited.

## 5. Inventory changes

`tools/d3/lean_chunk_coverage.py` gained `lean_crypto_host_arms()`: it reads the successor host
table (`Wasm/CryptoHost.lean`, `def cryptoHostCall` → `| "name" => some`) and marks those rows
`partial` with evidence pointing at both tables. `Wasm/CryptoHost.lean` was added to
`LEAN_FILES` so its hash is in the inventory's `source_sha256`. The generated JSON has
`lean_crypto_host_arms: 1` in `totals`.

Why `partial` and not `implemented`: the tool's `implemented` means "Lean has a dispatch arm on
the D3α path", which is false here (`hostCall_no_arm`). Why not `validated`: no whole-chunk case.
The row's `remaining_work` says both.

## 6. Judged infeasible / deliberately not landed

1. **Wiring `ecrecover` into the chunk path (whole-chunk rung).** The host dispatch is
   `Exec.callFunc → callHost → hostCall` (`Exec.lean:71-85,333-350`), reached from
   `exec`/`step`/`run`/`callEntry`/`runCall`. Enabling a second table means either (a) a flag on
   `NearCfg` branched on in `callFunc`, or (b) a `Bool` on `St` branched on in `callHost`. Both
   change the definitions used by the `Logged` commutation development
   (`Logged/WasmRun.lean:122-205`, `Logged/WasmStepE.lean:148-215`,
   `Logged/WasmCRHostCall.lean:14-78`, `Logged/D3LSpec.lean:196-207`), which is exactly the
   closure `checkD3L_eq` and `checkD3Reads_eq` rest on. I attempted the `St`-flag shape and
   tried to close the required `CR σ (hostEcrecover a) (hostEcrecover a)` with the existing `cr`
   tactic; it left the arithmetic sub-goal unsolved after ~2 minutes, and closing it by hand for
   each arm is not a small change. Since the constraint is additive-only on the signed surface, I
   backed the attempt out (nothing from it is committed) rather than land a broken `Logged` layer.
   **Next executable step**: add `crypto : Bool := false` to `NearCfg`, branch in `callFunc`,
   prove `CR_cryptoHostCall` by `by_cases` on the name (mirroring `CR_hostCall`'s generated
   shape) and thread `cfg.crypto = false` through `E_callFunc`/`E_exec`/`E_step`/`E_run` for
   `pv86`, then define `checkD3γ := checkD2Core (d3HooksCrypto …) …` and run the 83 OOD
   ecrecover cases as positives.
2. **`p256_verify` whole-chunk rung** — same blocker as (1): the host is implemented and tested at
   the host level but not reachable from `runCall`. Its 15 unit cases in
   `logic/tests/p256_verify.rs` additionally cover register inputs and a 256-byte prehash; those
   are gates of the host arm, not of the arithmetic, so the 8 Wycheproof vectors carry the
   semantics check.
3. **alt_bn128 and BLS12-381.** All 12 need curve arithmetic; the three alt_bn128 hosts and the
   `sum`/`multiexp`/`decompress` BLS hosts are a day's work in the `Secp256k1.lean` style, but
   `alt_bn128_pairing_check` and `bls12381_pairing_check` need a Miller loop and final
   exponentiation (`Fq12`/`Fp12`). A rushed pairing with no vector coverage would be a
   correctness risk, and a false `implemented` is worse than an honest `missing`.
4. **ML-DSA-65 key/signature variants** (named in the plan's L3 paragraph) are not among the 15
   rows L0 assigned to L3: `d3hostx mlkey` cases are excluded as `w.shape`/`e.mldsa_key` and are
   L4's boundary. Noted, not touched.
5. **PV86 BLS quirk** recorded for whoever implements the BLS hosts: `bls12381_not_in_group_fix =
   false` (`parameters.snap:289`) selects `version = 0`, which rejects the `(0, ±2)` corner case
   that NEP-488 accepts (`logic/bls12381.rs:17-28`). `alt_bn128` has no subgroup check for G1 (safe,
   prime order); scalars must be `< Fr`.

## 7. Files safe to edit / not to edit

* New, owned by this lane: `spec/lean/v3/NearSpecV3/Secp256k1.lean`,
  `spec/lean/v3/NearSpecV3/P256.lean`,
  `spec/lean/v3/NearSpecV3/Wasm/CryptoHost.lean`,
  `spec/lean/v3/NearSpecV3/D3/CryptoDomain.lean`,
  `oracle/wasm-d3/lean/CryptoTest.lean`, `docs/research/lean-chunk-crypto-L3.md`, this log.
* Shared but edited additively: `tools/d3/lean_chunk_coverage.py` (new helper + one branch in the
  host loop; the L3 rows are the only output change), `docs/research/lean-chunk-coverage.json`
  (regenerated, drift-gated), `oracle/wasm-d3/lean/lakefile.toml` (one new `lean_exe`).
* **Do not edit** (signed/other lanes): `Wasm/Exec.lean`'s `curveHosts`, `Wasm/Host.lean`'s
  `hostCall` (adding arms there would silently change `D3α`), `D3/FunctionCall.lean`'s `gAlpha`,
  `Challenge*.lean`, the challenge draft generator, or any `Logged/*` file for a crypto feature
  without re-running the full `lake build` and the `checkD3L_eq` consumer.

## 8. Exact reproduce commands

```bash
cd /data/illia/nearproof-wt/lean-chunk-L3/spec/lean/v3 && lake build
cd ../../../oracle/wasm-d3/lean && lake build nearspec-v3-check-d3 nearspec-v3-test-crypto
./.lake/build/bin/nearspec-v3-test-crypto
./.lake/build/bin/nearspec-v3-test-crypto edge
./.lake/build/bin/nearspec-v3-test-crypto host
./.lake/build/bin/nearspec-v3-test-crypto p256
./.lake/build/bin/nearspec-v3-test-crypto p256host
cd /data/illia/nearproof-deps/corpora/d3c9 && \
  /data/illia/nearproof-wt/lean-chunk-L3/oracle/wasm-d3/lean/.lake/build/bin/nearspec-v3-check-d3 ood/*
cd /data/illia/nearproof-wt/lean-chunk-L3 && \
  python3 tools/d3/lean_chunk_coverage.py --repo . --nearcore /data/illia/nearproof-deps/nearcore \
    --check docs/research/lean-chunk-coverage.json && make pin-check
```

The vector list in `CryptoTest.lean` was generated from the pinned JSON with:

```bash
python3 - <<'PY'
import json
d=json.load(open('/data/illia/nearproof-deps/nearcore/runtime/near-vm-runner/src/logic/tests/ecrecover-tests.json'))
for x in d:
    res='none' if x['res'] is None else f'some "{x["res"]}"'
    print(f'  ("{x["m"]}", {x["v"]}, "{x["sig"]}", {"true" if x["mc"] else "false"}, {res}),')
PY
```
