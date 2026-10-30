# Open UQs (workplan item 8), versioned claim/witness schema, environment assumptions (item 12)

2026-10-29. Target: nearcore 2.13.4 (`44f7ae6cd7ef08bab604e20a473bf77e35d4c993`), PV86, mainnet
parameters. Paths in nearcore are relative to that tree. Lean: `nearspec-v3-check-successor`, tier
`allFeatures` unless stated; "before" is the checker built from this branch's base (`4f07a7fdf`,
sha256 prefix `a1627ea3285cb919`), "after" the one built with this lane's changes. Every number
below is **measured in this lane** unless it is marked *carried over*, in which case the source is
linked. UQ-001 is owned by another lane and is not touched here.

## Summary

| UQ | disposition | evidence |
|---|---|---|
| UQ-002 | **answered (yes, and narrower):** on `allFeatures` the cache dependence is only the preparation-pipeline thread race; committed *and* rolled-back same-code deploys serve the code deterministically | 279/279 `e.code_cache` corpus cases: 169 accept/accept, 15 reject/reject, 95 out of domain (race; nearcore cold rejects all 95); 0 disagreements. Control *carried over*: without the pipeline rule 89 nearcore-rejected chunks were accepted |
| UQ-003 | **answered:** NaNs are canonicalised to the positive quiet NaN after every canonicalising operator; the Lean kernel equals x86_64/Winch and aarch64/Cranelift bit for bit | 5,920 operator calls: 0 differences x86_64 vs aarch64 (emulated) vs Lean, 0 rule violations; control with canonicalisation off: 2,496 violations, 194 cross-arch differences |
| UQ-004 | **answered:** PV86 uses the config stored under key 85 (no `86.yaml`, next key 129 is nightly); every crypto-host cost and flag in Lean equals it | 32/32 values (29 costs × gas+compute, 3 flags) agree between Lean, an independent rebuild from the YAML diffs, and `parameters.snap`; control (one Lean value +1) fails. Whole-chunk *carried over*: curve hosts 111/111 |
| UQ-007 | **answered (proof + pins):** `LegacyEthWallet` is unreachable at PV86; all four magic hashes redirect to the chain's global wallet | Lean `legacyWallet_unreachable_pv86`, `ethWallet_kind_unreachable` (existing); 7/7 wallet hashes recomputed from nearcore's embedded wasm equal Lean's; control fails |
| UQ-013 | **decision needed (proposal below, not adopted).** Measured which trusted facts the relation pins and which only an admission contract can bind | 2,348 single-fact mutants of 240 honest chunks over 4 seeds: `chain_id` 239/240, `minimum_stake` 240/240, `epoch_height` 231/240, validator stake 237/240 still **accepted**; `epoch_id`, `protocol_version`, RS parameters, `epoch_start_after` 240/240 rejected or excluded |
| UQ-015 | **answered:** the bound is sound given that every recorded item is a `base_state` value, which is a source fact; implicit transitions execute no receipts; `allFeatures` does not use the bound at all | source citations below; signed tier on the 88 storage-limit fixtures: 0 accepts of a nearcore reject, 18 `w.size` exclusions. Exact recorder *carried over*: one-byte flips incl. the 2,000 B removal charge |
| UQ-016 | **answered:** on every whole-state successor tier no action-log entry can reach the "unmodeled action log entry" exclusion | static check over all 30 `pushAction` sites in `Host.lean` against the manager's arms; control (an injected tag) fails; 0 such reasons in 1,020 fixture verdicts. Semantic agreement *carried over* (yield 202/202, promise and gas-key hosts) |
| UQ-017 | **answered:** the genesis main transition uses exactly the non-genesis comparison set against the stored genesis chunk extra; `tx_valid` all-1 only reachable empty | source map below; 266/266 genesis-main corpus chunks accept/accept. Negatives *carried over*: cross-family `genesis-tx`, 60 genesis-B2 chunks with full mutant sets |
| schema | **implemented:** explicit `schema_version` envelope; legacy files are version 3 by rule; CI gate | Lean `checkVersioned_legacy`/`_versioned` (allowed axioms); 235,940/235,940 corpus case dirs and 593/593 committed fixtures pass the schema check; envelope vs legacy verdicts: 0 differences on 2,220 cases; 0 before/after differences on 5,358 |
| item 12 | **stated** in `spec/environment-v3.md` + `spec/environment-v3.json`; **aarch64 excluded by statement**, with layout and float behaviour measured equal under emulation | instance-layout boundaries 65,501 / 65,344 / 65,505 on aarch64 = x86_64 = pinned harness; control (+64 B pool) moves each by exactly 4 |

No Lean semantic change was made to any relation. The only Lean change is the versioned envelope
reader (a transport rewrite in front of `checkSuccessor`, proved not to move any legacy verdict).

## UQ-002 — can `e.code_cache` narrow to rolled-back deploys?

Source. The cold validator looks code up in the compiled cache first
(`runtime/near-vm-runner/src/wasmtime_runner/mod.rs:705-723`), then in the deploy tracker:
uncommitted deploys, then committed deploys, then hash-addressed storage
(`core/store/src/contract.rs:42-69, 104-131`). `action_deploy_contract` writes the code and
precompiles it synchronously into the compiled cache (`runtime/runtime/src/actions.rs:297-339`), and
a rollback clears the uncommitted map but not the cache. So a same-code deploy earlier in the chunk,
**committed or rolled back**, serves the code — deterministically — *unless* the call's preparation
was submitted to the pipeline before that deploy ran (`runtime/runtime/src/pipelining.rs:141-315`,
scheduled from `lib.rs:3256-3325`). That case is a thread race inside nearcore.

So the answer is stronger than the question: the generator's `e.code_cache` label narrows to
**pipeline races only**. `allFeatures` already implements that (`Successor/CodeResolution.lean`
`resolveColdCode`, `Successor/Pipeline.lean`), with the race a named out-of-domain reason.

Test (`code-cache-279.json`), every d3c7–d3c10 case whose meta carries `e.code_cache`, against the
cold nearcore verdict:

| `allFeatures` / nearcore (cold) | cases |
|---|---|
| accept / accept | 169 |
| reject / reject (`MissingTrieValue (contract code)`) | 15 |
| out of domain (`contract preparation pipelined before the in-chunk deploy`) / reject | 95 |
| disagreement | **0** |

Deliberate-breakage control (*carried over*,
[corpus-blind-and-pipeline §1](../corpus-blind-and-pipeline/README.md)): before the pipeline rule
the same checker accepted 89 of those 95 nearcore-rejected chunks.

## UQ-003 — NaN payload and sign, and stability across architectures

Source. `cranelift_nan_canonicalization(true)` (`wasmtime_runner/mod.rs:531-534`), which Winch
honours at codegen; canonical NaN `0x7FC00000` / `0x7FF8000000000000`. nearcore's own test masks
the sign bit (`mod.rs:1243-1290`), which is why the sign on non-x86 was hazard H3.

Test (`nan-floats.json`, `tools/instance-layout/nan_probe.py`, `LeanFloat.lean`). One module
exports add, sub, mul, div, min, max, copysign, sqrt, ceil, floor, trunc, nearest, abs, neg (f32 and
f64), promote and demote, each over raw bit patterns; 20 specials per width (± quiet NaN with and
without payload, ± signalling NaN, ±∞, ±0, ± smallest subnormal, max finite, ±1, ±0.5, ±2.5); every
pair for binary operators. 5,920 calls, 3,214 NaN results.

| comparison | differences |
|---|---|
| x86_64 / Winch (native) vs aarch64 / Cranelift (QEMU 8.2.2 user mode) | **0** |
| x86_64 / Winch vs Lean float kernel (`NearSpecV3/Wasm/Float.lean`) | **0** |
| NaN result of a canonicalising operator ≠ `+qNaN` (x86_64 / aarch64) | **0 / 0** |
| *control:* canonicalisation off — rule violations x86_64 / aarch64 | 2,496 / 2,482 |
| *control:* canonicalisation off — x86_64 vs aarch64 differences | 194 |

The engine in both cases is nearcore's configuration (`tools/instance-layout/src/main.rs`, see
item 12). Whole-chunk float agreement on x86_64 is *carried over* (float-contracts 2,050 cases ×
70 operators; float-input-chunks 1,284; float-input-mutants 350). Caveat: aarch64 is emulated, not
silicon.

## UQ-004 — curve host gas pins at PV86

Source. `RuntimeConfigStore::get_config(pv)` returns the entry with the largest key ≤ `pv`
(`core/parameters/src/config_store.rs:240-248`); the keys are 0 and the `CONFIG_DIFFS` versions
(`:26-66`): …, 83, 84, 85, then 129 and 155 (nightly). So PV86 runs the table "base + all diffs up to
85". `parameters.snap` is that table at `PROTOCOL_VERSION` = 86 (`config_store.rs:402-418`).

Test (`pv86-param-pins.txt`, `tools/d3/check_pv86_param_pins.py`): the script parses
`CONFIG_DIFFS`, rebuilds the table from `parameters.yaml` and every diff ≤ 86 (checking each diff's
`old` value), compares with `parameters.snap`, and compares every crypto-host `Cost` in Lean
(`Wasm/CryptoHost.lean`, `Wasm/Machine.lean`: ecrecover, p256, ed25519, 18 BLS12-381, 6 alt_bn128)
plus the flags `p256_verify_host_fn = true`, `bls12381_not_in_group_fix = false`,
`eth_implicit_global_contract = true` as Lean fixes them. **32/32 agree.** Control
(`controls.txt`): +1 on one Lean constant → 31/32, exit 1. Whole-chunk curve-host agreement is
*carried over* ([curve-host-fixtures](../curve-host-fixtures/README.md), 111/111).

## UQ-007 — `LegacyEthWallet` at PV86

Source. `RuntimeContractIdentifier::resolve` (`runtime/runtime/src/contract_code.rs:56-76`): an
ETH-implicit account whose local hash is a wallet **magic** hash
(`runtime/near-wallet-contract/src/lib.rs:37-52`, `check_magic_bytes` `:143-155`) becomes
`Global { eth_wallet_global_contract_hash(chain_id) }` when `eth_implicit_global_contract` is on —
which it is from PV83 (`core/parameters/res/runtime_configs/83.yaml:4`); otherwise the account's
local hash is used. `LegacyEthWallet` is constructed only in the `else` branch.

Proof (existing): `D3/GlobalContract.lean` `legacyWallet_unreachable_pv86`,
`ethImplicit_resolves_global`; `Successor/Resolution.lean` `ethWallet_kind_unreachable`. On
`allFeatures` the resolution is `Successor/StorageExecution.lean:65-76` (`resolveCode`), whose
`.legacyEthWallet` arm is therefore dead.

Which hashes: all four magic hashes (mainnet, testnet, old testnet pv70, localnet) redirect,
whatever the chain; the target is the chain's global wallet hash. Test (`eth-wallet-pins.txt`,
`tools/d3/check_eth_wallet_pins.py`) recomputes `sha256("near" ‖ base58(sha256(wasm)))` from the four
wasm blobs nearcore embeds and the three global hashes (`lib.rs:87-104`; localnet =
`sha256(wallet_contract_localnet.wasm)`): **7/7 equal Lean**, the magic hashes are pairwise distinct
and disjoint from the global ones (so `resolve`'s order is immaterial). Control: one flipped byte → 6/7.

Not done: a whole-chunk fixture of an ETH-implicit account carrying a legacy magic-hash contract.
Such accounts can only exist from before PV83, so a PV86 test chain needs them in genesis; the
generator has no such scenario. The behaviour is covered by the proof and the pins, not by a chunk.

## UQ-013 — admission contract for the trusted facts (DECISION NEEDED)

claim-v3 §2.4 classifies T1–T14 as trusted. Measured on 240 honest chunks (60 from each of
d3c7–d3c10, seeds 7000021 / 8000024 / 9000027 / 10000030), one fact rewritten per mutant
(`trusted-fact-mutants.json`, `tools/d3/trusted_fact_mutants.py`):

| fact | mutation | `allFeatures` | pinned by the relation? |
|---|---|---|---|
| T1 `epoch_id` | flip a byte | 240 reject (`epoch id`) | yes |
| T2 `protocol_version` | 87 | 240 out of domain (`c.pv86`) | yes (only 86 decided) |
| T5 epoch `protocol_version` | 87 | 240 reject (epoch table) | yes |
| T4 RS parts | total + 3, data recomputed | 240 reject (`InvalidChunkEncodedMerkleRoot`) | yes, through the header |
| T9 `epoch_start_after[0]` | flip | 240 reject | yes |
| T13 `tx_valid[0]` | flip | 179 reject, **9 accept** | mostly |
| T3 `chain_id` | `arena-uq013` | **239 accept**, 1 reject | **no** |
| T7 `epoch_height` | + 1 | **231 accept**, 9 reject | **no** |
| T8 validator stake | + 1 | **237 accept**, 3 reject | **no** |
| T11 `minimum_stake` | + 1 | **240 accept** | **no** |

(T6 layout, T10 validator update, T12 split gate and T14 genesis extra were not mutated.)

So a proof is evidence about `chain_id`, `epoch_height`, validator stakes and `minimum_stake` only if
the verifier knows those values are its own. **Adopted 2026-10-30 (user decision):**

> *Admission contract A1.* A proof for `claim.bin` is admitted only by a verifier that rebuilds
> section C of the claim (and `epoch_id`, `protocol_version`, `chain_id`) from its own chain state
> for `chunk_inner.prev_block_hash` and finds it byte-identical. Concretely: the verifier runs the
> claim builder (`tools/mainnet-replay/native/w13_claim.rs` is one) on its node and compares the
> whole claim bytes; a proof over any other claim is not "validated".

This makes claim-v3 §2.4's existing requirement an executable admission check and adds no field.
The alternative, authenticating facts inside the relation (e.g. against the epoch-sync or
block-producer hashes in headers), is a spec change and is not proposed. Either way this is a
statement about who may rely on a proof, so it is left to the user.

## UQ-015 — is `Σ|values| + 2000·R ≤ 4,000,000` sound with contract-storage removals?

Already proved (`NearSpecV3/StorageBound.lean`, `guard_sufficient`) **given** the hypothesis that
every recorded item is one of the witness's `base_state` values. That hypothesis is a source fact:

* the validator's trie is `Trie::from_recorded_storage(base_state)`, whose storage is a map from
  `hash(value)` to `value` over exactly the `base_state` values (`core/store/src/trie/mod.rs:715-735`);
* `TrieMemoryPartialStorage::retrieve_raw_bytes` returns only from that map and otherwise fails with
  `MissingTrieValue` (`core/store/src/trie/trie_storage.rs:323-336`);
* the recorder adds a hash's bytes once, on first insert (`trie_recording.rs:115-132`), `+2000` per
  `ContractData` removal (`:140-146`), and `record_code_len` has no caller at the pin.

So the recorded sum is a sum over distinct `base_state` values, ≤ `Σ|values|`. The module's third
caveat (implicit transitions are not bounded) is vacuous: a missing-chunk application returns before
any receipt or transaction is processed (`runtime/runtime/src/lib.rs:1774-1780`), so no recorded
storage can reach a limit there. The bound is used only by the signed tier, and only as an
out-of-domain guard (`w.size`). `allFeatures` does not use it (`recorderDriver.sizeOk = true`) and
models the recorder and both limits exactly.

Tests. Signed tier on the 88 storage-limit fixtures (`storage-limit-signed.json`): 12 accept (all
nearcore accept), 18 out of domain `w.size`, 8 `e.g_alpha`, 50 reject; **0 accepts of a nearcore
reject**. The exact recorder is *carried over* ([storage-limit-fixtures](../storage-limit-fixtures/README.md)):
one-byte flips at 4,000,000 B for both limits, including the removal flip 2,150 B earlier (2,000 B
`record_key_removal` + the key).

## UQ-016 — is the action log equivalent to `ReceiptManager`?

The log is Lean-internal: Lean's host functions write it and `D3.manager` / `Successor.managerGlobal`
read it. The gap the UQ names is an entry the reader cannot parse, which becomes
`out of domain (e.wasm-α): unmodeled action log entry`. `tools/d3/check_action_log_tags.py` closes it
statically (`action-log-tags.txt`): it enumerates all **30** `pushAction` sites in `Wasm/Host.lean`,
derives the reader's arms from `D3/FunctionCall.lean` (`AC/5 AF/2 CA/0 DA/1 DC/1 DK/1 FC/5 RT/1 ST/2
TR/1`, plus `yieldCreate`, `YR:`, `CR(`), and checks each site: 12 tagged templates with the exact
arity, 4 `CR`, 4 `YR`, 2 `yieldCreate`, 6 `OTHER` entries carrying a `rawAction` (consumed by
`managerGlobal`), and 2 `OTHER` entries without one that sit in the `else` branch of
`if (← get).globalActions` (signed tier only, where those hosts are outside the signed domain by
design). Every interpolated field renders separator-free (hex, decimal, account id). Control: an
injected `ZZ@{r}` site fails the check.

Measured: 0 "unmodeled action log" reasons in the 1,020 fixture verdicts (§schema). Semantic
agreement of the translation with `ReceiptManager` (receipt ids, data ids, gas distribution, refunds)
is *carried over* from the yield (202/202), global-promise, key-family (gas-key promise hosts) and
cross-family families, where whole outcome roots match nearcore.

## UQ-017 — genesis main transition

Source. For a genesis last-chunk block the main transition is `MainTransition::Genesis` with the
stored genesis chunk extra and **no outgoing receipts** (`chain/chain/src/stateless_validation/
chunk_validation.rs:403-413, 602`); `tx_valid` is all-1 (`:382-386`) but the genesis chunk has no
transactions (`core/primitives/src/genesis/chunk.rs:64-95`, root checked at `:368-376`). Implicit
transitions then update only the state root and congestion info (`:736-737`), and the header is
compared by the same `validate_chunk_with_chunk_extra_and_receipts_root` (`chain/chain/src/validate.rs:133-188`:
state root, outcome root, proposals, gas limit, gas used, balance burnt, outgoing-receipts root,
congestion, bandwidth requests, proposed split) plus the tx root and encoded merkle root/length
(`chunk_validation.rs:751-777`). `Successor/RuntimeCore.lean:610-631` checks exactly these against
the genesis chunk extra and the empty outgoing-receipts root.

Tests: the 266 genesis-main corpus chunks: **266/266 accept/accept** (`genesis-266.json`; they are
not blind-gradable because their outputs are the stored chunk extra, a claim input). Negatives are
*carried over* from [cross-family §3](../cross-family-fixtures/README.md) (60 genesis-B2 chunks, full
mutant sets, `g.*` mutants; control C3).

## Versioned claim/witness schema

Spec: [`spec/claim-v3-versioning.md`](../../../../spec/claim-v3-versioning.md) (`claim-v3.md` itself is
pinned by digest in the signed challenge and is not edited).

```
claim.bin   = bytes "near-arena-claim"   ‖ u32 schema_version ‖ body
witness.bin = bytes "near-arena-witness" ‖ u32 schema_version ‖ u8 encoding ‖ body
```

Version 3 is the only one defined (body = the v3 file after its tag; witness encoding 0 = clear,
1 = zstd). **Legacy rule:** an unversioned `near-arena-claim-v3` / `near-arena-witness-v3` /
`near-arena-cwitness-v3` file is schema version 3.

* Lean `Successor/SchemaVersion.lean`: `normalizeClaim`, `normalizeWitness`, `checkVersioned`;
  theorems `checkVersioned_legacy` (no verdict movement on any input not starting with an envelope
  tag, which includes every legacy file), `checkVersioned_legacy_files`, `checkVersioned_versioned`
  (a version-3 envelope is decided as its canonical file), `normalizeClaim_unsupported`,
  `normalizeWitness_bad_encoding`. `#print axioms`: `propext`, `Classical.choice`, `Quot.sound`.
  `MainSuccessor.lean` uses it on every tier except `signed`.
* Python `tools/d3/claim_schema.py`: header + full structural check of the v3 body; converter;
  self-test; environment-manifest check. CI: `difftest-gates` runs the self-test, every committed
  fixture, the environment manifest and a negative control; `oracle/tools/test_claim_schema.py`
  (auto-discovered by the harness self-tests) checks 593 committed fixtures legacy and as envelopes,
  round trip, and six malformed variants.
* Whole corpora (`corpus-schema.json`): 235,940 case dirs, 235,940 claims and 235,940 witnesses
  pass, all under the legacy rule.

Before/after verdict table (`schema-runs.json`; before = `a1627ea3285cb919`, after = `f40158a4bb724155`,
tier `allFeatures`, nearcore = the cold verdict in each case's meta):

| population | before | after, legacy files | after, version-3 envelopes | differences |
|---|---|---|---|---|
| 1,020 fixtures (593 committed dirs + cross-family, runtime-errors, gate-b-caps, storage-limit tarballs) | 639 accept/accept, 381 reject/reject | same | same | **0 / 0** |
| corpus sample, 300 cases from each of d3c7–d3c10 (seeds 7000021, 8000024, 9000027, 10000030; honest, mutants, ood) | 457 accept/accept, 743 reject/reject | same | same | **0 / 0** |
| 3,138-case gap census | 3,138 accept | 3,138 accept | — | **0** |

Lean accepts of a nearcore reject: 0 in every population. Controls on the 1,200-case sample: claim
schema version 4 → 1,200 reject (`unsupported claim schema version 4`); witness encoding 2 → 1,200
reject (`unsupported witness encoding 2`); the before checker (no envelope rule) on the envelopes →
1,200 reject (`wrong claim format`), so the envelope comparison is sensitive; `--tier signed` on the
envelopes → 1,200 reject (the signed tier keeps the signed byte format). Process: 8 workers until the
coordinator's request on 2026-10-30, 4 after.

## Item 12 — environment assumptions

Stated in [`spec/environment-v3.md`](../../../../spec/environment-v3.md) and machine-readable in
[`spec/environment-v3.json`](../../../../spec/environment-v3.json) (checked by
`claim_schema.py --check-env` in CI): ENV-1 reference validator (x86_64, Wasmtime 45.0.0, Winch),
ENV-2 healthy host state (slot exhaustion, host-resource instantiation failures, cache I/O and foreign
cache entries assumed absent, with the argument that they can only cost an endorsement), ENV-3
architectures, ENV-4 cold cache and the environment-derived out-of-domain reasons.

**aarch64.** nearcore compiles with Cranelift there (`wasmtime_runner/mod.rs:512-521`, "Cranelift
elsewhere (e.g. aarch64 development environment)"). No aarch64 host exists here, so
`tools/instance-layout/` replays nearcore's engine construction (`mod.rs:455-545`, the same
`wasmtime = 45.0.0` with nearcore's features and lock file) and its compile/deserialize path
(`compile_uncached` `:567-597`, `Module::deserialize` `:744-745`) on modules prepared by the pinned
harness (`near-wasm-d3-harness prepare`, nearcore's own `prepare_contract`), natively and as a static
`aarch64-unknown-linux-musl` binary under QEMU 8.2.2 user mode. `boundary.py` binary-searches the
largest fitting global count of the three `runtime-errors` shapes over [60,000, 70,000]:

| shape | pinned harness, x86_64 (*carried over*, `runtime-errors/boundary.json`) | probe, x86_64 / Winch | probe, aarch64 / Cranelift | control: aarch64, pool + 64 B |
|---|---|---|---|---|
| a | 65,501 | 65,501 | **65,501** | 65,505 |
| b | 65,344 | 65,344 | **65,344** | 65,348 |
| c | 65,505 | 65,505 | **65,505** | 65,509 |

The x86_64 row reproduces the pinned harness exactly, so the probe computes the real numbers; the
control moves every boundary by exactly 64 B / 16 B per global = 4. Over-limit error on both
architectures: "instance allocation for this module requires 1048592 bytes which exceeds the
configured maximum of 1048576 bytes".

Disposition: **aarch64 is excluded from the reference by statement** (ENV-3). The instance layout
and float/NaN behaviour were measured equal, but trap classification, native stack use,
compile-time limits, real silicon and whole-chunk replay were not, so the package claims agreement
for x86_64 only. This does not change the claim/witness domain.

## Files

* `README.md` (this file); `code-cache-279.json`, `nan-floats.json`, `pv86-param-pins.txt`,
  `eth-wallet-pins.txt`, `trusted-fact-mutants.json`, `storage-limit-signed.json`,
  `action-log-tags.txt`, `genesis-266.json`, `controls.txt`, `corpus-schema.json`,
  `layout-*.json`, `schema-runs.json`.
* Tools: `tools/d3/check_pv86_param_pins.py`, `check_eth_wallet_pins.py`, `check_action_log_tags.py`,
  `trusted_fact_mutants.py`, `claim_schema.py`; `tools/instance-layout/` (probe crate, `boundary.py`,
  `nan_probe.py`, `LeanFloat.lean`); `oracle/tools/test_claim_schema.py`.
* Lean: `spec/lean/v3/NearSpecV3/Successor/SchemaVersion.lean`, imported by `NearSpecV3/Successor.lean`
  and `MainSuccessor.lean`.
* Spec: `spec/claim-v3-versioning.md`, `spec/environment-v3.md`, `spec/environment-v3.json`.

## Reproduce

```
python3 tools/d3/check_pv86_param_pins.py            # UQ-004
python3 tools/d3/check_eth_wallet_pins.py            # UQ-007
python3 tools/d3/check_action_log_tags.py            # UQ-016
python3 tools/d3/claim_schema.py --self-test && python3 -m unittest oracle/tools/test_claim_schema.py
# item 12 / UQ-003 (needs rustup target aarch64-unknown-linux-musl, clang, qemu-aarch64-static):
cd tools/instance-layout && cargo build --release                     # x86_64
CC_aarch64_unknown_linux_musl=clang \
CFLAGS_aarch64_unknown_linux_musl="--target=aarch64-linux-musl -ffreestanding -nostdinc -isystem $(clang -print-resource-dir)/include -I<dir with stdlib.h = #include <stddef.h>>" \
CARGO_TARGET_AARCH64_UNKNOWN_LINUX_MUSL_LINKER=rust-lld cargo build --release --target aarch64-unknown-linux-musl
python3 boundary.py --harness near-wasm-d3-harness --probe <aarch64 probe> --runner qemu-aarch64-static
python3 nan_probe.py --probe <x86 probe> --other-probe <aarch64 probe> --other-runner qemu-aarch64-static \
  --lean-results <(cd ../../spec/lean/v3 && lake env lean --run ../../../tools/instance-layout/LeanFloat.lean CALLS)
```

(`helpers.c` of wasmtime needs only `NULL` from `<stdlib.h>`, hence the one-line stub header; the
QEMU binary is the Ubuntu `qemu-user-static` 8.2.2 package, extracted without installing.)
