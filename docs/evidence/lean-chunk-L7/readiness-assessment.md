# L7 readiness assessment — plan §5 validation items

Date: 2026-10-23. Lane L7, worktree `/data/illia/nearproof-wt/lean-chunk-L7`, branch
`lane/lean-chunk-L7`, base `a5ef42e0c`. Target nearcore `44f7ae6cd7ef08bab604e20a473bf77e35d4c993`, PV86.

Every number below was measured in this worktree on this date unless marked otherwise. Where an item
cannot be satisfied, the reason is stated and no count is claimed. This document is evidence *about*
the repository, not a certification: nothing here closes Gate A, B or C.

## Summary table

| §5 item | status | what exists | path |
|---|---|---|---|
| 1 target identity | **partial** | corpus-level commit + PV86 in each `summary.json`; oracle pin file; no manifest binding compiler/toolchain/param hashes/executable digests in one place | `oracle/NEARCORE_PIN`, `<corpus>/summary.json`, this lane's `corpus-manifest.json` |
| 2 directed tests | **partial** | per-family directed suites exist and execute (L2 float, L3 crypto, D1/D2/D3 corpora); only L2 demonstrates a removal/breakage regression | `oracle/wasm-d3/tests/*`, `oracle/wasm-d3/lean/CryptoTest.lean` |
| 3 generated ≥1000/family × 4 seeds | **partial** | L2 float: measured 149,462 cases × 4 seeds, 0 diffs; D3 corpora: 8/12/4/4 chains; no generated suite for crypto/actions/hosts | `oracle/wasm-d3/tests/difftest_float.py` |
| 4 chunk integration | **partial** | whole-chunk verdict + ~10 header fields compared (state root, outcome root, gas, burnt, receipts root, congestion, bandwidth); emitted receipts/logs/return data NOT compared against nearcore per case | `spec/lean/v3/NearSpecV3/ChunkValidationD2.lean:238-271` |
| 5 regression corpora | **satisfied with caveat** | D1 53,048 / D2 67,384 / D3 115,284 all replayed, **0 disagreements on all three legs** (Lean, Python, nearcore), content hashes recorded; *not* proven byte-identical to the original generation (recipes not re-runnable here) | `docs/evidence/lean-chunk-L7/corpus-manifest.json`, results in the lane log |
| 6 replay ≥1000 consecutive blocks | **absent** | a 1,378-height metadata census (not execution); 4 real mainnet fixtures for an *older* statement (`receipt-transfer-batch/v0`), not chunk-transition v3 | `docs/e2e-results/mainnet-replay-2026-10/samples.jsonl`, `oracle/fixtures/historical/cases/` |
| 7 formal checks | **partial** | `lake build` 162 jobs exit 0; axiom audits within allowed set; no `sorry`/`native_decide`/new axioms in the v3 tree; no clean-checkout rebuild, no runtime-path restriction audit | `spec/lean/v3`, this document §7 |

---

## 1. Target identity — partial

What is recorded:

* `oracle/NEARCORE_PIN` — `repo`, `tag=2.13.4`, `commit=44f7ae6c…`, `protocol_version=86`.
* Every corpus `summary.json` carries `nearcore_commit: 44f7ae6cd7ef08bab604e20a473bf77e35d4c993`
  and `protocol_version: 86` (checked in d1run, d2corpus.v2, d3c7, d3c9; d3c8/d3c10 same shape).
* Lean toolchain is pinned per project (`spec/lean/v3/lean-toolchain`); `lake --version` here is
  5.0.0-src+5045d00 / Lean 4.34.1.
* Executable digests measured this session:

| artifact | sha256 |
|---|---|
| `oracle/wasm-d3/lean/.lake/build/bin/nearspec-v3-check-d3` | `528992988e0c72769fe909494b3e99a2dd3d4c78ad47ecf7acf7524603ecb42f` |
| `/data/illia/nearproof-deps/target-wasm-d3/release/near-wasm-d3-harness` | `08b9c36e67a8ad03d4c129…` (see lane log for the full digest) |

What is **missing** for the item as written ("record source commits, compiler/toolchain versions,
runtime parameters, oracle build recipe, executable hashes and commands in a manifest"):

* No single manifest binds all six. The runtime *parameters* are only partly pinned: there is no
  `86.yaml` in `core/parameters/res/runtime_configs/` (79/82/83/84/85 + `parameters.snap`), so the
  Lean `NearCfg` defaults cite the 85 snapshot. This is UQ-004's subject and is unresolved.
* The per-case `meta.json` records the nearcore *verdict* but not the nearcore commit; the commit is
  only in the corpus-level `summary.json`. A case copied out of its corpus loses its provenance.
* The oracle build recipe is `oracle/scripts/link-nearcore.sh` + a per-crate `cargo build`; nothing
  records the resulting binary's digest automatically. `make pin-check` verifies *source* pins
  (`spec/tools/check_oracle_pins.py`), not binary identity.
* `oracle/vendor/nearcore` is **not linked in this worktree** (`readlink -f` empty), so the oracle
  crates (`oracle/v3`, `oracle/v3-d3`, `oracle/d3-ttn`) cannot be rebuilt here. The corpora they
  produced are present and were replayed; the generators were not re-run. This is why item 5 below
  is "replayed, not regenerated".

## 2. Directed tests — partial

Executing directed suites that I ran and that compare against something real:

| suite | command | measured result |
|---|---|---|
| L2 float operator/gas/size | `oracle/wasm-d3/tests/float_nearcore.py --limit 12` | values 1,260 cases / gas 210 modules / size 140 modules, 0 disagreements |
| L3 ecrecover vectors | `nearspec-v3-test-crypto` | 161 total, 35 recovered, 126 rejected, 0 mismatches |
| L3 ecrecover edge | `nearspec-v3-test-crypto edge` | 20 total, 0 failures |
| L3 ecrecover host | `nearspec-v3-test-crypto host` | 23 total, 0 failures |
| L3 p256 vectors | `nearspec-v3-test-crypto p256` | 17 total, 0 failures |
| L3 p256 host | `nearspec-v3-test-crypto p256host` | 13 total, 0 failures |

Independent check of L3's transcription: I re-read all 161 rows out of
`runtime/near-vm-runner/src/logic/tests/ecrecover-tests.json` in the pinned nearcore and compared
them field-by-field with the hardcoded table in `CryptoTest.lean` — **161/161 present, 0 mismatched**.
That matters because a transcription error would be invisible to the test that consumes the table.

**The item's harder half — "at least one regression experiment showing removal/breakage of the new
behaviour makes a targeted test fail" — exists for exactly one family.** L2's log records ablation
switches (`--instruction-level-metering`, `D3_TTN_ABLATE=--ablate-cache/--ablate-overlay`). I ran my
own ablations and they do fail as required:

| ablation | result |
|---|---|
| D3 difftest with a wrong verdict oracle (`D3_CHECK=…always accept`) | exit 1, 38/60 disagreements |
| D1 difftest with a wrong checker for both legs | exit 1, 83,918 disagreements |
| UQ-014 reproducer at 1,000 globals instead of 66,000 | exit 1, "nearcore did not report LoadingError" |

No lane provides a *mutation* regression for the crypto hosts or the storage bound. L3's 161/20/23
and 17/13 counts are directed vectors against nearcore's own JSON/Wycheproof data, not generated.

## 3. Generated tests ≥1,000 per family across 4 seeds — partial

Measured, and only for floats:

```
cd oracle/wasm-d3/tests && python3 difftest_float.py --cases 1000 --seed S   # S = 1,2,3,4
family=float cases=149462 opcodes=70 disagreements=0     (identical for all four seeds)
```

Reading the generator directly, `gen(cases, seed)` emits `cases` random pairs *per opcode* plus the
directed edge pairs. With `--cases 1000` that is 1,000 generated pairs × 70 opcodes = **70,000
generated comparisons per seed**, i.e. the ≥1,000 bar is exceeded ~70× per seed, and four distinct
seeds were run. Note the total 149,462 includes directed pairs; the generated-only count is 70,000.

For whole-chunk float coverage I measured the corpora rather than trusting the lane's figure: counting
`executed_contracts[*].float == true` over all 115,284 D3 cases gives **160** entries, all on the single
contract `d3float`. (A grep for "float" in `meta.json` returns 15,663 hits, but those are the
`'float': False` flag on non-float contracts.) So L2's "26 recorded chunks" understates the count by ~6×
while its real limitation — one contract — is accurate.

Families with **no** generated comparison at ≥1,000×4 seeds:

* crypto hosts — directed vectors only;
* actions/receipts/hosts in D2 — the corpora have distinct chain seeds per corpus: D1 **12**, D2 **14**,
  D3c7 **8**, D3c8 **12**, D3c9 **4**, D3c10 **4** (measured from each `summary.json`'s `seed:` fields),
  so the "at least four recorded seeds" *count* is met several times over for every corpus. But these
  are seeds of a whole-corpus generator, not "generated comparisons per family" in the plan's sense, and
  they are not re-runnable here (`oracle/vendor/nearcore` unlinked) — so the seeds exist as recorded
  provenance, not as a reproducible generation recipe.
* storage accounting — L5 added zero tests (see §"lane-claim audit").

## 4. Chunk integration — partial

What the whole-chunk comparison really asserts. `checkD2Core` (`ChunkValidationD2.lean:114-271`)
compares the *endorsed header's* fields against Lean's recomputation:

* `prevStateRoot == root` (:242, :251), `prevOutcomeRoot == outcomeRootD1 out.outcomes` (:255),
  `prevGasUsed == out.gasUsed` (:258), `prevBalanceBurnt == out.balanceBurnt` (:259),
  `prevOutgoingReceiptsRoot == outgoingReceiptsRootD2 …` (:260), `congestion` (:261),
  `bwRequests` (:262), `txRoot` (:265), `encodedMerkleRoot`/`encodedLength` (:269-270),
  `proposals` (:256), `gasLimit` (:257), plus `proposedSplit.isNone` (:263).

So an `accept` is **not** a bare verdict: the chunk's claimed state root, outcome root, gas used,
burnt balance, receipts root, congestion info and bandwidth requests all had to match. That is
stronger than "verdict only", and I correct my own earlier reading on this point.

What is **not** compared per case against nearcore:

* emitted receipts' *bodies* and logs/return data beyond what the outcome/receipts roots commit to;
* refund amounts as separate columns;
* the receipt-level gas split.
  The D3 difftest compares the `accept`/`reject`/`out_of_domain` verdict; the roots/gas are compared
  *inside* Lean against the header, and the header's authenticity comes from nearcore having produced
  it. That is a genuine differential signal but it is **one-sided**: Lean must reproduce nearcore's
  header, but the harness does not additionally diff a per-case table of gas/refunds/logs against a
  nearcore-emitted table. The D3α op-level harness (`oracle/wasm-d3/tests/difftest.py`) *does*
  compare full outcome lines (status, burnt, used, return bytes, error) and the trie harness
  (`oracle/d3-ttn/difftest_ttn.py`) compares 11 per-key storage slots + wasm gas + ext gas — those
  are the two harnesses where observables are compared field-by-field. Neither runs on the D3
  corpora as a whole-chunk sweep.

Also absent: "tampered claims/witnesses" comparison per new family. The corpora contain
`mutants/` (byte-level tampering) and they are replayed, but the mutants are generated per corpus,
not per newly-added semantic family.

## 5. Regression corpora — satisfied, with an explicit caveat

All three corpora exist on this host and **were replayed**, not merely counted:

| corpus | cases | d3/d2/d1 | mutants | ood | verdict |
|---|---|---|---|---|---|
| D1 `d1run` | 53,048 | 3,394 | 46,009 | 3,645 | **0 disagreements** |
| D2 `d2corpus.v2` | 67,384 | 10,537 | 56,457 | 390 | **0 disagreements** |
| D3 `d3c7` | 33,248 | 5,381 | 27,030 | 837 | **0 disagreements** |
| D3 `d3c8` | 49,490 | 8,192 | 39,997 | 1,301 | **0 disagreements** |
| D3 `d3c9` | 15,995 | 2,656 | 12,928 | 411 | **0 disagreements** |
| D3 `d3c10` | 16,551 | 2,778 | 13,353 | 420 | **0 disagreements** |
| **D3 total** | **115,284** | 19,007 | 93,308 | 2,969 | **0 disagreements** |

All six runs completed and every one was independently recounted from its saved per-case `lean.jsonl`
against the on-disk case directories: d3c7 33,248/33,248 present, d3c8 49,490/49,490, d3c10
16,551/16,551, each recomputing 0 disagreements. One nuance worth stating: each D3 corpus has a handful
of `ood` cases Lean accepts while the oracle's classifier calls them out-of-domain (200/300/100/100 =
**700 total**, all `nearcore_ok`). The difftest reports them as `ood_decided_by_lean` rather than as
disagreements, because the oracle's `in_d3` is false. That is the documented error-kind quotient, not a
relaxed comparison, but "0 disagreements" means "0 under the oracle's in-D3α classification".

Content hashes: `docs/evidence/lean-chunk-L7/corpus-manifest.json` (18 families; per-family case
count, byte total and an order-stable SHA-256 over `claim.bin`/`witness.bin`/`meta.json`). The drift
gate `tools/d3/corpus_manifest.py --verify <manifest>` re-walks and fails on any drift; I showed it
fails on a tampered manifest.

**Caveat, stated plainly:** these are *replays of corpora that exist on this host*, and their counts
and content match the figures the plan records. They are **not** proven to be byte-identical to the
corpora as originally generated in the historical runs, because the generators could not be re-run
here (`oracle/vendor/nearcore` is unlinked, so `near-arena-oracle-v3-d1 gen --domain d1|d2|d3` cannot
be rebuilt). So this is an *exact replay of a surviving copy*, not a regenerated reproduction. The
manifest makes that checkable: if someone regenerates a corpus and its digest differs, the difference
is now visible.

The plan's "No previously accepted unchanged-domain case may silently regress" is satisfied for these
copies: every honest case that nearcore accepts is accepted by Lean and by the Python reference.

## 6. Representative replay ≥1,000 consecutive blocks — absent

What exists and what it actually is:

* `docs/e2e-results/mainnet-replay-2026-10/samples.jsonl`: **13,770 chunks over 1,378 distinct
  heights**, span 220,185,437–220,186,815 (1 missing height inside the span), all four shards,
  classified by workload (`d2-actions` 23, `d2-queues` 2, `d3-callbacks` 1306, `d3-calls` 2653,
  `d3-maxgas` 4256, `d3-nonwasm` 58, plus the rest). This is a **metadata census**, not execution —
  the plan explicitly says "Metadata-only workload classification does not satisfy this gate".
* `oracle/fixtures/historical/cases/`: **4** cases with authentic mainnet trie nodes and witnesses
  (shards 4/7/12/12 at heights 218,303,545–218,303,595). But their statement is
  `near/pv86/receipt-transfer-batch/v0` (`near/pv86/receipt-transition/v1`), **not** the
  chunk-transition relation, so they exercise `checkD1`-family semantics, not `checkD3`. Also
  `provenance.json` records `anchors` for one case with `all ok: False`, and `not_anchored` names the
  unauthenticated facts. So even these 4 do not satisfy item 6 for the chunk transition.

No tool in the repo fetches mainnet chunk *state witnesses* and runs `checkD3` on them. The corpora
are synthetic chains from a deterministic generator. **Item 6 is absent.** The nearest honest
statement is: "4 authentic mainnet fixtures exist for an earlier statement; 13,770 chunks were
classified but not executed."

## 7. Formal checks — partial

Measured here:

* `cd spec/lean/v3 && lake build` → **Build completed successfully (162 jobs)**, exit 0.
* `#print axioms` over the chunk-transition surface:
  * `NearSpecV3.D3.relD3_iff_acceptsD3` → `[propext, Classical.choice, Quot.sound]`
  * `NearSpecV3.rel_mono`, `inLang_mono`, `sound_lift` → same three.
  * L5's `StorageBound.Rec.guard_sufficient`, `Rec.size_le_recorded` → `[propext, Quot.sound]`;
    `removal_charge_can_exceed_limit`, `per_receipt_limit_does_not_bound_chunk` → no axioms.
* No `sorry`, `admit`, `native_decide` or new `axiom` declarations in the v3 tree — the only matches
  are two comments that *mention* those words
  (`Examples/Ed25519Kernel.lean:7`, `ChallengeChunkV3Gas.lean:34`).

Not done: a from-clean-checkout rebuild (the worktree `.lake` caches are warm and were reused), an
audit of "runtime-path restrictions", and `#print axioms` on *every* new theorem of *every* lane. The
CI workflow does not build `spec/lean/v3` at all (see the lane log's gating finding).

---

## Lane-claim audit (adversarial reading of the other lanes' logs)

| claim | verified? | finding |
|---|---|---|
| L2: floats complete, 1,260 + 210 + 140 against nearcore, 0 diffs | **yes** | reproduced exactly. Note the *operator* comparison is against a Python IEEE reference; only the nearcore anchor (1,260 values) is against nearcore's engine. |
| L2: 4 seeds × generated | **yes, and stronger than claimed** | `--cases 1000` gives 70,000 generated/seed, not "1,120 over 4 seeds" |
| L3: 161 ecrecover vectors, 0 mismatches | **yes, plus transcription audited** | table matches the pinned JSON 161/161 |
| L3: hosts are *not* reachable through `checkD3` | **yes** | `hostCall` in `Wasm/Host.lean` has no `ecrecover`/`p256_verify` arm; L3's `hostCall_no_arm` is honest |
| L3: "no whole-chunk case for ecrecover/p256" | **yes, and correctly reported as a gap** | the 83 ecrecover cases are all out-of-domain by construction |
| L5: `record_code_len` has no caller; bound is sound but not a protocol limit | **yes** | `record_code_len` (`core/store/src/trie/trie_recording.rs:148`) has zero call sites; `codes_to_record.insert` appears nowhere |
| L5: axiom claims | **yes, exactly** | reproduced all four |
| L5: "boundary cases below/at/above every limit" | **no evidence** | L5's diff added **no tests**; its 4 changed files are one `.lean` module, the root import, a spec doc and the log |
| D3 corpora "zero disagreements in the three-way comparison" | **yes, all three legs** | Lean↔nearcore 0, Python↔nearcore 0, Lean↔Python 0 on each of d3c7/d3c8/d3c9/d3c10 (115,284 cases). D1/D2 also ran the Python leg (0 diffs). |

## What this lane did NOT verify

Stated so nobody over-reads the table above:

* ~~The Python third leg on D3.~~ **Done after the first draft**: `difftest_d3.py --python` was run on
  all four D3 corpora against the saved Lean verdicts — Lean↔nearcore 0, Python↔nearcore 0, Lean↔Python
  0 on each (115,284 cases total). See the lane log §4.1b.
* The **generator provenance** of the corpora. They exist and their counts match the plan; the oracle
  crates that generated them cannot be rebuilt in this worktree (`oracle/vendor/nearcore` unlinked), so
  I replayed a surviving copy rather than regenerating from the pinned recipe.
* The **`--python` leg's own non-vacuity**. I demonstrated it for the Lean leg (wrong checker → 38
  disagreements), not for the Python checker. The Python leg's 0/115,284 agreement is therefore
  evidence that two independent implementations agree, but I did not prove the Python harness would
  catch a wrong Python checker.
* **Runtime-path restrictions** in item 7's sense: I read axioms for a handful of headline theorems, not
  for every new theorem with its path hypothesis.
* Anything about **succinct proof bytes, verification cost or proving resources** — outside this lane.

## Answers to UQ-014

**No — H2/H9/H10 are not absent. The Wasmtime `LoadingError` is reachable at PV86 and the Lean spec
does not model it.**

Mechanism and citation:

* `runtime/near-vm-runner/src/wasmtime_runner/mod.rs:734-745` — `Module::deserialize` result is
  mapped to `VMRunnerError::LoadingError(err.to_string())`.
* `wasmtime-45.0.0/src/runtime/module.rs:549-552` — `Module::from_parts` runs the allocator's
  `validate_module`, whose message is "module instance size does not fit in pooling allocator
  requirements" (`wasmtime-45.0.0/src/runtime/vm/instance/allocator/pooling.rs:578-579`).
* The configured limit is `core_instance_size = 1 << 20` (1 MiB, `pooling.rs:179`); the instance
  layout grows with the module's defined globals (`VMGlobalDefinition` array).
* `runtime/near-vm-runner/src/logic/types.rs` (nop path) + `function_call.rs:326-330` turn a
  `LoadingError` into a **0-gas** `nop_outcome` carrying `FunctionCallError::LoadingError` — i.e. a
  consensus-observable failed function call, not a chunk rejection. nearcore's own test asserts this
  path (`runtime/near-vm-runner/src/tests/runtime_errors.rs:19-44`, using
  `near_test_contracts::contract_with_num_globals(100_000)`).

Measured boundary on this host, with `oracle/wasm-d3`'s harness against pinned nearcore:

| defined globals | nearcore | Lean `nearspec-v3-wasm` |
|---|---|---|
| 65,505 | `ok 490588602541 490588602541 - …` | `ok 490588602541 …` (agree) |
| 65,506 | `LoadingError("module instance size does not fit in pooling allocator requirements")` | — |
| 66,000 | same `LoadingError` | `ok 494363009716 …` (**diverges**) |

And the module **passes NEAR preparation**: instrumented size 454,039 bytes at 66,000 globals, far
under the 16 MiB `maxInstrumentedCodeSize`. So this is exactly "a contract that passes preparation"
whose execution nearcore refuses to load.

Reproducer: `oracle/wasm-d3/tests/uq014_instance_size.py` (asserts prepare-accept + LoadingError +
Lean-accepts; exit 0 only when the divergence reproduces, exit 1 when any leg changes). Negative
controls verified: 1,000 globals → "nearcore did not report LoadingError" → exit 1; a non-Lean binary
→ "the Lean spec did not return `ok`" → exit 1.

This is **not confined to a bare call**. `runtime/runtime/src/function_call.rs:95-142` converts the
aborted outcome into the receipt's action result: a `LoadingError` becomes an
`ActionErrorKind::FunctionCallError(...)` in `result.result`, and `gas_burnt` is incremented by
`outcome.burnt_gas` — which is zero. So inside a chunk, a FunctionCall receipt to such a contract
**fails with a LoadingError action result and burns 0 gas**, and the chunk is accepted. Lean, reaching
the same call, would succeed and charge the full operator gas. That changes the receipt's outcome, its
gas, and therefore the chunk's outcome root — a consensus-visible divergence, not merely an error-kind
difference. (Not demonstrated end-to-end through a chunk here, because building such a chunk requires
the oracle generator, which cannot be rebuilt in this worktree; the source chain above is the argument,
and it is a chain, not a measurement. Labelling it as testing would overstate it.)

Consequences for the plan's Gate B ("Every reachable supported-protocol row is implemented and
validated"; "Impossible cases have an explicit pinned-source justification"):

1. This is a reachable branch with a **consensus-visible outcome** (failed function call, 0 gas burnt)
   that `checkD3` cannot produce. Either `Prepare`/`Exec` must model the instance-size limit (which
   requires modelling Wasmtime's `Instance::alloc_layout`, i.e. a Wasmtime layout detail as a
   protocol condition), or L0 must mark this branch `impossible-at-boundary` **with a justification
   that survives this measurement** — and "H9/H10 assume absent" does not.
2. The precise globals threshold is a wasmtime-version detail (65,506 here), so a Lean predicate
   would be pinned to `wasmtime 45.0.0`'s layout. That is a legitimate "authenticated runtime
   environment assumption" the plan asks to enumerate, but it must be enumerated, not assumed away.
3. `WasmUnknownError` and the resource `LinkError` are a different matter: I found no reachable
   construction for either within a chunk witness. The pooling semaphore (`try_acquire`, mod.rs:230)
   only blocks; it does not fail a call. So UQ-014's answer is **branch-specific**: `LoadingError`
   reachable (measured), `WasmUnknownError`/resource `LinkError` still not demonstrated reachable —
   but "not demonstrated" is weaker than "absent", and the honest status for those two is
   *unresolved, with no reachable construction found*.

## Gate B mapping (§3), for the record

The plan's Gate B bullets, each against what this lane actually measured. None is closed by this work;
this only says which bullets now have measured evidence behind them and which are still assertion-only.

| Gate B bullet | this lane's evidence |
|---|---|
| inventory accounts for every branch/variant/instruction family/host/resource boundary/guard | not verified here; the 219-row inventory is L0's. This lane only audited one row (UQ-014). |
| every reachable row implemented and validated; zero unresolved exclusions | **UQ-014 contradicts the assumption** for `LoadingError`: a reachable, consensus-visible branch with no Lean model. |
| impossible cases have pinned-source justification + checked predicate | **UQ-014's "absent" framing is not justified**; `LoadingError` is measured reachable. `WasmUnknownError`/resource `LinkError`: no construction found, so "impossible" is still unproven rather than justified. |
| no prover-derived bound on the canonical relation | not this lane's; L1's `gAlpha` question is UQ-012. |
| protocol resource limits implemented, failure/rollback behaviour real | **partially**: L5's storage bound is proved sound but explicitly not a protocol limit (L5's own log), and the instance-size limit is unimplemented (UQ-014). |
| per-lane tests + combined regression/replay gates pass with zero unexplained disagreements | **regressions yes** (115,284 + 53,048 + 67,384, 0 disagreements, measured); **replay no** (§5 item 6 absent); per-lane tests partially audited (§6). |
| all trusted assumptions enumerated, incl. runtime environment assumptions | **no**: the Wasmtime pooling-allocator limit and its 1 MiB constant are a runtime environment assumption that is neither modelled nor enumerated. |

## Gating findings

* `make lean` builds only `formal-core spec/lean` (`Makefile:32,158-165`); **`spec/lean/v3` is not
  built by the Makefile or by CI**. The signed-surface Lean package therefore has no automated build
  gate outside its own lane. Any regression in `spec/lean/v3` reaches `main` without CI noticing.
* `make pin-check` passes (`spec/tools/check_oracle_pins.py`, 6 challenge classes `ok`), but it checks
  *source* digests only; it does not build or run the difftests.
* No difftest is wired into CI or the Makefile. Every differential result in this repository is a
  manual run. That is the structural reason "a harness that prints ok without comparing" is a live
  risk; I checked each of the nine difftest scripts and each exits nonzero on disagreement, and I
  demonstrated failure on wrong input for D1, D3 and UQ-014.
