# L7 — differential validation and integration (handoff)

Date: 2026-10-23. Plan lane: `docs/requirements/LEAN_CHUNK_TRANSITION_PLAN.md` §4 L7, §5 items 1–7.

| field | value |
|---|---|
| owner | L7 (differential validation and integration) |
| worktree | `/data/illia/nearproof-wt/lean-chunk-L7` |
| branch | `lane/lean-chunk-L7` |
| base commit | `a5ef42e0c61ed4769fa5a9236f99b115b153ea33` |
| committed tip | recorded in the reply; not merged, not pushed |
| target | nearcore `44f7ae6cd7ef08bab604e20a473bf77e35d4c993`, PV86 |
| inventory row owned | `UQ-014` (the only row L7 owns; the 219-row inventory has zero `owner == "L7"` rows) |

## 1. Result summary

Three things came out of this lane, in order of how much they should change someone's plan:

1. **UQ-014 is answered NO for `LoadingError`, with a measurement.** The Wasmtime pooling-allocator
   `LoadingError` **is reachable at PV86** for a contract that *passes NEAR preparation*, and the Lean
   spec accepts that contract where nearcore burns 0 gas and fails the call. New reproducer:
   `oracle/wasm-d3/tests/uq014_instance_size.py`. Boundary measured at 65,505/65,506 defined globals.
   `WasmUnknownError` and the resource `LinkError` have **no reachable construction found**; for those
   the honest status is "unresolved, no reachable construction", not "absent".
2. **The regression corpora replay clean, and I measured every case.** D1 53,048 and D2 67,384 and
   D3 33,248 + 49,490 + 15,995 + 16,551 = 115,284, **all with 0 Lean↔nearcore disagreements**, plus
   content hashes so a later run can prove it replayed the same bytes. The corpora are a surviving
   copy on this host, not a regeneration — stated as such, not called an exact replay.
3. **Nothing here is gated.** `spec/lean/v3` is not built by the Makefile or by CI, and no difftest is
   wired into either. Every differential result in this repository is a manual run. That is the
   structural reason the "harness prints ok without comparing" failure mode is a live risk; I checked
   all nine difftest scripts and each exits nonzero on disagreement, and demonstrated failure on
   deliberately wrong input for D1 and D3.

Also: I audited the other lanes' claims rather than trusting the logs. L2's float numbers, L3's crypto
numbers and L5's axiom/factual claims all reproduce. L5's *acceptance criteria* do not: it added no
tests. Details in §6.

Readiness per §5 item: **1 partial, 2 partial, 3 partial, 4 partial, 5 satisfied-with-caveat,
6 absent, 7 partial.** The full table with paths is
`docs/evidence/lean-chunk-L7/readiness-assessment.md`.

## 2. Harness inventory (item 1's audit)

### 2.1 What genuinely executes and compares against a real reference

| harness | compares against | gated by | executes? |
|---|---|---|---|
| `oracle/v3-d3/tools/difftest_d3.py` | pinned nearcore's `expected_rel` (per-case `meta.json`) | nothing; manual | **yes** — I ran it on all six corpora |
| `oracle/tools/difftest_v3_d1.py` | nearcore `expected_rel_d1` + independent Python | nothing; manual | **yes** — ran the full 53,048 |
| `oracle/tools/difftest_v3_d2.py` | nearcore `expected_rel_d2` + independent Python | nothing; manual | **yes** — ran the full 67,384 |
| `oracle/wasm-d3/tests/difftest.py` | nearcore harness, **full outcome lines** (status, burnt, used, return bytes, error) | nothing; manual | yes for opcode families; not run this session |
| `oracle/d3-ttn/difftest_ttn.py` | nearcore per-key storage profile + wasm gas + ext gas | nothing; manual | not run this session |
| `oracle/wasm-d3/tests/difftest_float.py` | **Python** IEEE reference (+ optional nearcore sample) | nothing; manual | **yes** — ran 4 seeds |
| `oracle/wasm-d3/tests/float_nearcore.py` | nearcore's engine (values, gas, size) | nothing; manual | **yes** — ran |
| `nearspec-v3-test-crypto` (L3) | hardcoded transcription of nearcore's JSON + Wycheproof | nothing; manual | **yes** — ran all five modes |
| `oracle/tools/spec_check_v3_d3.py` | independent Python cleanroom (`nearwasm.py`) | nothing; manual | yes, as the third leg; **not run on D3 this session** |
| `oracle/tools/check_logged.py` | logged vs original checker verdicts+reasons | nothing; manual | not run this session |

Harness self-tests: `python3 -m unittest discover -s oracle/tools -p 'test_*.py'` — 7 + 7 + 9 + 5 = **28
tests, all OK**.

### 2.2 What does not execute or does not compare

* `tools/mainnet-replay/replay.py` — harvests **metadata** (chunk height/shard/class) from a mainnet
  source. It does not execute a witness. Its output `docs/e2e-results/mainnet-replay-2026-10/`
  (13,770 chunks over 1,378 heights) is a workload census. The plan explicitly excludes this as
  satisfying §5 item 6.
* `tools/historical-v3/build_chunk.py` + `oracle/fixtures/historical/` — builds authentic mainnet
  fixtures, but for statement `near/pv86/receipt-transfer-batch/v0` (receipt transition), **not** the
  chunk transition. 4 cases only. So they do not exercise `checkD3`.
* The oracle crates (`oracle/v3`, `oracle/v3-d3`, `oracle/d3-ttn`) are **not buildable in this
  worktree**: `oracle/vendor/nearcore` is an unlinked symlink and no compiled oracle binary exists
  anywhere on this host (`ls .../near-arena-oracle*` → nothing). The corpora those crates produced are
  present; the *generators* cannot be re-run here. This is the reason §5 item 5 is "replayed" rather
  than "regenerated".

### 2.3 Gating: none of the above is in CI or the Makefile

* `Makefile:32` — `LEAN_PROJECTS ?= formal-core spec/lean`. **`spec/lean/v3` is absent.**
  `make lean` (target at `Makefile:158`) therefore never builds the signed-surface Lean package.
* `.github/workflows/ci.yml` runs `make pin-check` and `make test-rust`, and a Lean matrix over
  `formal-core, spec/lean, zk-formal` — **not** `spec/lean/v3`.
* `make pin-check` (`spec/tools/check_oracle_pins.py`) verifies **source** digests of `oracle/v3*`
  against the signed challenge's generator specs. It does not build or run anything. It passes.
* Consequence: a regression in `spec/lean/v3` or in any oracle/difftest reaches `main` with no
  automated signal. Every number in this document came from a manual run.

## 3. UQ-014 — answered: `LoadingError` is reachable

**Question** (219-row inventory on `lane/lean-chunk-L0`): are the Wasmtime `LoadingError` /
`WasmUnknownError` / resource `LinkError` branches (H2/H9/H10) truly absent at PV86, or must they be
modelled?

**Answer, branch by branch.**

### 3.1 `LoadingError` — REACHABLE, measured. H9's absence assumption is wrong.

Chain of evidence in the pinned source:

* `runtime/near-vm-runner/src/wasmtime_runner/mod.rs:734-745` —
  `Module::deserialize(..).map_err(|err| VMRunnerError::LoadingError(err.to_string()))?`.
* `wasmtime-45.0.0/src/runtime/module.rs:549-552` — `Module::from_parts` runs the allocator's
  `validate_module`; the failure text is "module instance size does not fit in pooling allocator
  requirements" (`wasmtime-45.0.0/src/runtime/vm/instance/allocator/pooling.rs:578-579`, called from
  `validate_module` at `:73-81`).
* The limit is `core_instance_size = 1 << 20` (1 MiB, `pooling.rs:179`), and the instance layout grows
  with the module's defined globals (`VMGlobalDefinition` array; `wasmtime-environ-45.0.0/src/vmoffsets.rs:31`).
* `runtime/runtime/src/function_call.rs:328-330` converts it to
  `VMOutcome::nop_outcome(FunctionCallError::LoadingError { msg })`, and `nop_outcome`
  (`runtime/near-vm-runner/src/logic/logic.rs:4511-4524`) sets `burnt_gas: Gas::ZERO`,
  `used_gas: Gas::ZERO`, `aborted: Some(error)`. **So the consensus outcome is a failed function call
  with zero gas burnt**, not a chunk rejection.
* nearcore's own test asserts this path:
  `runtime/near-vm-runner/src/tests/runtime_errors.rs:19-44` with
  `near_test_contracts::contract_with_num_globals(100_000)`
  (`runtime/near-test-contracts/src/lib.rs:251`).

Measured on this host with `oracle/wasm-d3`'s harness against pinned nearcore 2.13.4 (module =
memory export + `main` + N immutable i32 globals):

| defined globals | nearcore | Lean `nearspec-v3-wasm` | agree? |
|---|---|---|---|
| 1,000 | `ok 6565815766 6565815766 - …` | `ok 6565815766 …` | yes |
| 55,000 | `ok 410487294716 …` | — | — |
| 65,505 | `ok 490588602541 …` | `ok 490588602541 …` | yes |
| **65,506** | `LoadingError("module instance size does not fit in pooling allocator requirements")` | — | **diverges** |
| **66,000** | same `LoadingError` | `ok 494363009716 …` | **diverges** |

And the 66,000-global module **passes NEAR preparation**: instrumented size 454,039 bytes, against
`maxInstrumentedCodeSize` 16,777,216. Lean's `prepare` returns `.ok` and its driver prints a full
successful outcome line (`ok 494363009716 494363009716 - 1000000000000000000000000`). So this is
precisely "a contract that passes preparation" whose execution nearcore refuses to load, and the Lean
spec says it succeeds.

Why Lean misses it: `Wasm/Prepare.lean:441-455` models the *instrumented-module re-validation* limits
(`MAX_WASM_FUNCTION_LOCALS` 50,000 / `MAX_WASM_FUNCTION_SIZE` 7,654,321 → `.compileErr`) but has no
instance-size check at all; `Wasm/Exec.lean:459-460` maps `.compileErr` to a
`CompilationError(WasmtimeCompileError …)` line. Nothing in the Lean tree knows about
`core_instance_size`.

Reproducer: **`oracle/wasm-d3/tests/uq014_instance_size.py`**. It builds the module from spec (not from
nearcore's fixture), then asserts all three legs and exits 0 only when the divergence reproduces:
`[1] nearcore prepare: accepted (454039 instrumented bytes)` / `[2] nearcore run: LoadingError` /
`[2b] message is the pooling-allocator instance-size branch: True` / `[3] Lean: ok 494363009716 …`.
**Non-vacuity verified**: `--globals 1000` → "nearcore did not report LoadingError" → exit 1;
`--lean /bin/true` → "the Lean spec did not return `ok`" → exit 1.

Gate B consequences. The plan says "Every reachable supported-protocol row is implemented and
validated" and "Impossible cases have an explicit pinned-source justification". This is a reachable
branch with a consensus-visible outcome that `checkD3` cannot produce. Either:

* model the limit in `Prepare` — which means modelling Wasmtime's `Instance::alloc_layout` as a protocol
  condition, pinned to wasmtime 45.0.0's layout. That is an *authenticated runtime environment
  assumption* the plan asks to enumerate, and it must be enumerated rather than assumed away; or
* mark the row `impossible-at-boundary` with a justification that survives this measurement. "H9/H10
  assume them absent" does not.

A third honest option is to scope it: the outcome is a failed call with **0 gas**, so it cannot change
gas accounting, and its only consensus effect is the failure and its error kind. If the relation is
allowed to quotient error kinds (which the plan already permits: "Respect the existing error-kind
quotient; exact error strings are not an acceptance requirement"), then accepting-where-nearcore-fails
is still a *verdict* divergence and cannot be quotiented away. It needs a decision, not a rename.

Corpora cannot reach it: the largest witness in any D3 corpus is 346,717 bytes (`d3c8/ood/02-h10122-s1`)
versus this module's 453,799 bytes, so **no regression case exercises the branch**. That is why 0
disagreements on 115,284 cases says nothing about it.

### 3.2 `WasmUnknownError` — no reachable construction found; not proved absent

Produced at two places in `wasmtime_runner/mod.rs`:

* `:403-407` — `C::Unknown { trap }`, i.e. a trap code the match does not enumerate.
* `:409-412` — "nondeterministic trap" from the `'nondet` break.

I could not construct either at PV86. The trap enum arms at `:379-401` cover the reachable set
(`HeapMisaligned` requires atomics, and `THREADS = false` at `features.rs:9`; `Interrupt` requires
`epoch_interruption`, and **nothing in nearcore enables it** — grep for `epoch_interruption` over
`runtime/` and `core/` returns nothing, as does `consume_fuel`). So H9's *conclusion* holds for this
arm, but by an argument that has to be written down: "PV86 enables neither epoch interruption nor fuel,
and atomics are disabled, so no trap outside the enumerated arms is reachable."

That argument has one soft spot I did not close: a trap that is reachable but misclassified would land
in `C::Unknown`. Proving "no such trap" needs the wasmtime trap set enumerated against PV86's feature
set, which I did not do. So: **unresolved; no reachable construction found**, not "absent".

### 3.3 Resource `LinkError` (H2) — same status: no reachable construction found

The link path is `:414-420` → `FunctionCallError::LinkError`, whose text is either "unknown or invalid
import" or wasmtime's message. The two reachable shapes are an unknown import and an incompatible
import type; both are prepared-module conditions that Lean models (`Prepare.lean`'s `linkError`), and
the D3α difftest compares them modulo the message text. The *resource* variant — the pooling
semaphore's `try_acquire` failing — does not fail a call: `try_acquire`
(`wasmtime_runner/mod.rs:230-269`) blocks on `release_notify.wait(&mut guard)` and only returns `None`
on a checked-add overflow, so contention cannot turn into a `LinkError`. I found no construction.
Again **unresolved, no reachable construction**, and the "absent" framing in the boundary doc is not
justified for H2/H9/H10 as a group — only the *measured* `LoadingError` case is settled (and settled
the other way).

### 3.4 What UQ-014 needs from its owner (L7 → whoever picks this up)

1. Decide the modelling question in §3.1 and record the decision in the inventory row.
2. If modelled: add the instance-size predicate to `Prepare` and a directed test that fails without it.
   The threshold is a wasmtime-layout function, so the predicate needs the layout constants and a
   stated pin.
3. If excluded: write the pinned-source justification in the row, with this document's measurement as
   the counter-evidence it must address. An exclusion that ignores a measured reachable branch is a
   rename, which the plan explicitly disallows.

## 4. Regression results — actual numbers

All runs are Lean checker vs nearcore's recorded verdicts in each case's `meta.json`
(`expected_rel`), using the repo's own difftest scripts. **No comparison logic was relaxed.**

| corpus | cases | by family (d3/d1/d2 · mutants · ood) | disagreements | script |
|---|---|---|---|---|
| D1 `d1run` | **53,048** | 3,394 · 46,009 · 3,645 | **0** | `oracle/tools/difftest_v3_d1.py` |
| D2 `d2corpus.v2` | **67,384** | 10,537 · 56,457 · 390 | **0** | `oracle/tools/difftest_v3_d2.py` |
| D3 `d3c7` | **33,248** | 5,381 · 27,030 · 837 | **0** | `oracle/v3-d3/tools/difftest_d3.py` |
| D3 `d3c8` | **49,490** | 8,192 · 39,997 · 1,301 | **0** | same |
| D3 `d3c9` | **15,995** | 2,656 · 12,928 · 411 | **0** | same |
| D3 `d3c10` | **16,551** | 2,778 · 13,353 · 420 | **0** | same (see §4.3) |
| **D3 total** | **115,284** | 19,007 · 93,308 · 2,969 | **0** | |

D1/D2 also ran the independent Python checker as a third leg: D1 Python 884.9 s, D2 Python 65.2 s,
both **0 disagreements** against Lean and nearcore. Lean wall times under load: D1 548.0 s, D2 1,663.9 s.

### 4.1 Per-corpus verdict distribution (measured, from the saved `lean.jsonl`)

* `d3c7`: `accept` 11,834 · `reject` 20,685 · `out_of_domain` 729 (by family: d3 5,381 accept;
  mutants 6,253 accept / 20,685 reject / 92 out_of_domain; ood 200 accept / 637 out_of_domain).
  Independently recomputed the comparison from the 33,248 saved verdicts against 33,248 on-disk cases:
  0 missing, 0 disagreements.
* `d3c8`: `accept` 17,662 · `reject` 30,702 · `out_of_domain` 1,126. Same recount: 49,490/49,490
  present, 0 disagreements.
* `d3c9`: `accept` 5,715 · `reject` 9,938 · `out_of_domain` 342 — 2,656 d3 all `accept` (nearcore ok);
  mutants 2,959 accept / 9,938 reject / 31 out_of_domain; ood 100 accept / 311 out_of_domain. Note the
  100 `ood` accepts: these are cases the oracle classifies
  as outside D3α but nearcore accepts — the difftest counts them as `ood_decided_by_lean` and they are
  *not* counted as disagreements, because the oracle's `in_d3` is false. That is the documented
  behaviour, not a relaxed comparison; it is called out here so nobody mistakes "0 disagreements" for
  "0 cases where Lean accepts what the oracle calls out-of-domain".

### 4.1b Three-way verification (the third leg, now measured)

The historical claim is a *three-way* comparison. The first pass of this lane ran only the
Lean↔nearcore leg. I went back and ran the Python leg as well, reusing the saved Lean verdicts:

| corpus | Lean ↔ nearcore | Python ↔ nearcore | Lean ↔ Python |
|---|---|---|---|
| `d3c7` | 0 / 33,248 | 0 / 33,248 | 0 / 33,248 |
| `d3c8` | 0 / 49,490 | 0 / 49,490 | 0 / 49,490 |
| `d3c9` | 0 / 15,995 | 0 / 15,995 | 0 / 15,995 |
| `d3c10` | 0 / 16,551 | 0 / 16,551 | 0 / 16,551 |

Command: `python3 oracle/v3-d3/tools/difftest_d3.py <corpus> --shards 8 --python --lean-from <saved
lean.jsonl> --save <out>`, exit 0 on all four. For `d3c9` the Lean↔Python verdict pairs are
`accept/accept` 5,715, `reject/reject` 9,938, `out_of_domain/out_of_domain` 342 — i.e. the two
independent implementations agree on the verdict for **every** case, not just on the aggregate. So
"zero disagreements in the three-way comparison" is now a measured statement for all 115,284 D3 cases.

### 4.2 Content hashes (item 5's "record content hashes, not just counts")

`tools/d3/corpus_manifest.py` walks each family in sorted case order and hashes
`claim.bin`/`witness.bin`/`meta.json` per case; output in
`docs/evidence/lean-chunk-L7/corpus-manifest.json` (18 families, per-family case count, byte total,
SHA-256, plus `missing_count`). Example: `d3c9/d3` → 2,656 cases, 94,081,363 bytes,
`sha256:b089682…`. Drift gate: `corpus_manifest.py --verify <manifest>` re-walks and exits 1 on any
change; **non-vacuity verified** by tampering one digest in a copy → exit 1.

All six corpora match the plan's recorded counts exactly, and the script asserts that and fails if not.

### 4.3 d3c10 — completed, measured

```
==== lean vs nearcore
('d3', 'accept', 'nearcore_ok') 2778
('mutants', 'accept', 'nearcore_ok') 3042
('mutants', 'reject', 'nearcore_rej') 10280
('mutants', 'out_of_domain', 'nearcore_ok') 15
('mutants', 'out_of_domain', 'nearcore_rej') 16
('ood', 'accept', 'nearcore_ok') 100
('ood', 'out_of_domain', 'nearcore_ok') 320
('g_alpha', 'oracle', 'lean') 112
('g_alpha', 'oracle', 'out_of_domain') 19
('code_cache', 'oracle', 'lean', 'nearcore_ok') 15
('code_cache', 'oracle', 'lean', 'nearcore_rej') 16
('ood_decided_by_lean', 'accept', 'True') 100
lean: cases=16551 disagreements_with_nearcore=0
```

Independently recounted from the saved `lean.jsonl` against the 16,551 on-disk case directories:
16,551 verdicts present, 0 missing; verdicts `accept` 5,920 · `reject` 10,280 · `out_of_domain` 351;
recomputed disagreements **0**. So all four D3 corpora are measured, not inferred, and D3 totals
33,248 + 49,490 + 15,995 + 16,551 = **115,284 with 0 disagreements**.

### 4.4 The d3c7/d3c8/d3c9/d3c10 `ood` accept nuance, in full

Every D3 corpus reports a handful of `ood` cases that Lean **accepts** while the oracle classifies them
outside D3α: d3c7 200, d3c8 300, d3c9 100, d3c10 100 — always exactly `nearcore_ok` true. The difftest
records them as `ood_decided_by_lean` and does **not** count them as disagreements, because the
oracle's `in_d3` is false for them (their only violation is a D2/claim-domain guard, and nearcore
itself accepts them). This is the documented quotient, not a relaxed comparison — but it means "0
disagreements" should be read as "0 disagreements under the oracle's in-D3α classification". A reader
who wants the strictest statement should note that 700 cases across the four corpora are accepted by
Lean where the oracle's classifier says out-of-domain.

## 5. §5 item 6 — absent, and what "absent" means here

* `docs/e2e-results/mainnet-replay-2026-10/samples.jsonl`: **13,770 chunks, 1,378 distinct heights**,
  span 220,185,437–220,186,815 (1 height missing inside the span), all shards, class mix
  `d3-maxgas` 4,256 / `d3-calls` 2,653 / `d3-callbacks` 1,306 / `d3-nonwasm` 58 / `d2-actions` 23 /
  `d2-queues` 2 and the remainder. It is metadata. **Not execution.**
* `oracle/fixtures/historical/cases/`: **4** authentic mainnet fixtures with real trie nodes, at
  heights 218,303,545 / 218,303,553 / 218,303,557 / 218,303,595, shards 4/7/12/12. Statement
  `near/pv86/receipt-transfer-batch/v0`. One case's `provenance.json` has `anchors` with
  `all ok: False` and an explicit `not_anchored` list. These do not exercise the chunk transition.
* No tool in the repository fetches mainnet chunk **state witnesses** and runs `checkD3` on them.

So: 1,000 consecutive *executed* blocks across all shards does not exist. The nearest honest sentence
is "4 authentic mainnet fixtures exist for an earlier statement; 13,770 chunks were classified but not
executed."

## 6. Audit of the other lanes' claims (adversarial)

| lane claim | verdict | evidence |
|---|---|---|
| L2 floats: 1,260 values + 210 gas + 140 size against nearcore, 0 diffs | **reproduced** | `float_nearcore.py --limit 12` → `values 1260 / gas 210 / size 140, 0 disagreements` |
| L2: generated tests over ≥4 seeds | **reproduced, stronger than claimed** | `difftest_float.py --cases 1000 --seed {1,2,3,4}` → 149,462 cases each, 0 diffs; the generator emits 1,000 random pairs × 70 opcodes = **70,000 generated per seed** |
| L2: whole-chunk float coverage = 26 recorded chunks, one contract | **understated; measured 160, still one contract** | counting `executed_contracts[*].float == true` across all 115,284 D3 cases gives **160** entries, all contract `d3float`. So the *count* is better than L2 claimed, but the "one contract" limitation is exactly right — `oracle/v3-d3/contracts/d3float.wat` is the only float contract in the oracle workload. (A naive grep for "float" in `meta.json` gives 15,663 hits; those are the `'float': False` flag on other contracts, not float executions — worth knowing before anyone re-derives this.) |
| L3 crypto: 161 ecrecover vectors, 0 mismatches | **reproduced** | `nearspec-v3-test-crypto` → 161 total, 35 recovered, 126 rejected, 0 mismatches |
| L3: the 161-row table faithfully transcribes nearcore's JSON | **audited independently** | I re-read all 161 rows from `logic/tests/ecrecover-tests.json` and matched `(msg, v, sig, mc, res)` field-by-field: **161/161 present, 0 mismatched** |
| L3: edge 20 / host 23 / p256 17 / p256host 13, 0 failures | **reproduced** | all four modes ran clean |
| L3: `ecrecover`/`p256_verify` are not reachable through `checkD3` | **confirmed** | `Wasm/Host.lean` `hostCall` has no arm for either name; L3's `hostCall_no_arm` is an honest gap report |
| L3: 83 corpus cases call a curve host, all out-of-domain | **consistent** | those cases are in the `ood`/`mutants` families the difftest reports as `out_of_domain` |
| L5: `record_code_len` has no caller | **confirmed** | `core/store/src/trie/trie_recording.rs:148` — one definition, **zero** call sites in the pinned tree; `codes_to_record.insert` appears nowhere |
| L5: axiom claims | **reproduced exactly** | `Rec.guard_sufficient` → `[propext, Quot.sound]`; `Rec.size_le_recorded` → same; `removal_charge_can_exceed_limit` and `per_receipt_limit_does_not_bound_chunk` → no axioms |
| L5: "boundary cases below/at/above every applicable limit" | **no evidence** | L5's diff vs base touches 4 files (one `.lean` module, the root import, a spec doc, the log) and **adds no test file and no test case** |
| "D3 115,284 cases, zero disagreements in the recorded three-way comparison" | **reproduced three-way, all four corpora** | `difftest_d3.py --python --lean-from <saved lean.jsonl>` on d3c7/d3c8/d3c9/d3c10: **Lean↔nearcore 0, Python↔nearcore 0, Lean↔Python 0** on each. Totals 33,248 + 49,490 + 15,995 + 16,551 = 115,284. The three-way claim now has this session's measurement behind it. |

## 7. Harness non-vacuity — demonstrated, not asserted

The repo's failure mode is a harness that prints "ok" without comparing. Evidence it does compare:

| harness | deliberate wrong input | result |
|---|---|---|
| `difftest_d3.py` | `D3_CHECK=…/wrongchecker.py` (always "accept") | **exit 1**, 38/60 disagreements |
| `difftest_v3_d1.py` | wrong checker for both legs | **exit 1**, 83,918 disagreements |
| `uq014_instance_size.py` | `--globals 1000` | **exit 1**, "nearcore did not report LoadingError" |
| `uq014_instance_size.py` | `--lean /bin/true` | **exit 1**, "the Lean spec did not return `ok`" |
| `corpus_manifest.py --verify` | tampered digest in a manifest copy | **exit 1** |

Every difftest script exits nonzero on disagreement: `difftest_v3_d1.py:155`,
`difftest_v3_d2.py:298`, `difftest_v3.py:103` → `main()`'s return, `difftest_d3.py:main()`'s
`sys.exit(1 if total_bad else 0)`, `difftest.py:2`, `difftest_ttn.py:1`.

One subtlety worth recording: `difftest_d3.py`'s comparison is **verdict-level**
(`accept`/`reject`/`out_of_domain`), plus the two domain-boundary checks (`g_alpha`, `code_cache`). The
observables (state root, outcome root, gas, burnt, receipts root, congestion, bandwidth) are compared
**inside Lean** against the endorsed header (`ChunkValidationD2.lean:238-271`), so an `accept` does mean
Lean reproduced nearcore's header — but the difftest does not additionally tabulate gas/refunds/logs
per case. The two harnesses that do compare observables field-by-field are
`oracle/wasm-d3/tests/difftest.py` (full outcome lines) and `oracle/d3-ttn/difftest_ttn.py` (11 storage
slots + wasm gas + ext gas); neither runs on the whole D3 corpora. That is the honest scope of "0
disagreements" on 115,284 cases, and it is item 4's gap.

## 8. Build / formal state measured here

```
cd spec/lean/v3 && lake build
  -> Build completed successfully (162 jobs), exit 0

lake env lean  #print axioms
  NearSpecV3.D3.relD3_iff_acceptsD3   -> [propext, Classical.choice, Quot.sound]
  NearSpecV3.rel_mono / inLang_mono / sound_lift -> same three
  StorageBound.Rec.guard_sufficient, Rec.size_le_recorded -> [propext, Quot.sound]
  StorageBound.removal_charge_can_exceed_limit,
           per_receipt_limit_does_not_bound_chunk     -> no axioms

grep -rn 'sorry|admit|native_decide|^axiom' spec/lean/v3/NearSpecV3
  -> 2 matches, both comments (Examples/Ed25519Kernel.lean:7, ChallengeChunkV3Gas.lean:34)

make pin-check -> 6 challenge classes ok, exit 0
python3 -m unittest discover -s oracle/tools -p 'test_*.py' -> 28 tests OK
```

Not done: a from-clean-checkout rebuild (warm `.lake` reused), an audit of runtime-path restrictions,
and `#print axioms` over *every* new theorem in *every* lane. The v3 tree has no `sorry`, so the
"missing semantic result as a premise" failure mode cannot be hidden in the tree as committed — but a
theorem *about a restricted path* still needs its path restriction read, which I did not do for all of
them.

Executable digests:

| artifact | sha256 |
|---|---|
| `oracle/wasm-d3/lean/.lake/build/bin/nearspec-v3-check-d3` | `528992988e0c72769fe909494b3e99a2dd3d4c78ad47ecf7acf7524603ecb42f` |
| `oracle/wasm-d3/lean/.lake/build/bin/nearspec-v3-wasm` | `4ce100d191a4400da605b626192ecd9aadc820dcbb359fc91c62234d33cc3f12` |
| `spec/lean/v3/.lake/build/bin/nearspec-v3-check-d2` | `8df208c55a74a87349e671ea22a5b403c4367e05a76a0f9331dae8e434a49c34` |
| `/data/illia/nearproof-deps/target-wasm-d3/release/near-wasm-d3-harness` | `2e8184320ccb05cc524b16415c10e20f473edb157a08b9c36e67a8ad03d4c129` (23,738,808 bytes) |

The two Lean binaries were rebuilt this session from the tree at `a5ef42e0c`, so these digests identify
the exact code that produced the numbers in §4. Note `nearspec-v3-check-d3`'s digest equals the one L3
recorded (`528992988…`), which is the consistency check that the checker binary is the same one L3's
guard replay used.

## 9. Files added / changed by this lane

Added (all new, nothing shared edited):

* `oracle/wasm-d3/tests/uq014_instance_size.py` — the UQ-014 reproducer/regression test.
* `oracle/wasm-d3/tests/l7_verify_all.sh` — the whole sweep as one command (self-tests, UQ-014,
  manifest, D1, D2, four D3 corpora, `make pin-check`), stopping at the first failure. `--quick`
  shortens only the D3 step; the D1/D2 scripts have no sampling switch, so those always run whole.
* `tools/d3/corpus_manifest.py` — corpus content manifest + drift gate.
* `docs/evidence/lean-chunk-L7/corpus-manifest.json` — generated manifest (18 families).
* `docs/evidence/lean-chunk-L7/readiness-assessment.md` — the §5 item-by-item assessment.
* `docs/logs/lean-chunk-L7-2026-10-23.md` — this log.

No Lean, no oracle Rust, no signed surface, no other lane's file was modified. The pre-existing
`D research/near-compression/native/wasm-base/target/…` deletions in the worktree were already present
at base and are not this lane's; I did not commit them.

## 9b. One-command reproduction

```bash
# full sweep: 28 harness self-tests, UQ-014, 18-family manifest, D1 53,048, D2 67,384,
# D3 115,284, make pin-check. Exit 0 only if every comparison agrees.
bash oracle/wasm-d3/tests/l7_verify_all.sh --out /tmp/l7-sweep

# smoke only (samples the four D3 corpora; D1/D2 still run whole — no switch exists)
bash oracle/wasm-d3/tests/l7_verify_all.sh --quick
```

The script's exit status is meaningful precisely because each step's own script exits nonzero on
disagreement — verified by feeding deliberate wrong input to the D1 and D3 difftests and to the UQ-014
reproducer (§7 table).

## 10. Next executable steps

1. **Decide UQ-014's modelling question** (§3.4). Until it is decided the inventory row cannot honestly
   read `impossible-at-boundary`, and Gate B cannot pass with an unresolved row.
2. **Wire the gates.** Add `spec/lean/v3` to `LEAN_PROJECTS` (or a separate target) and add at least one
   difftest invocation to CI. Right now nothing catches a `spec/lean/v3` regression. The cheapest first
   step is a small `d3c9`-slice difftest in the Lean CI job, since `d3c9` replays in ~2 minutes under
   load.
3. **Close item 4's observable gap** if the plan's wording is to be met literally: extend
   `difftest_d3.py` to tabulate per-case gas/refunds/logs against a nearcore-emitted table, not only
   the verdict and the header-internal comparisons. The D3α op-level harness already has the shape.
4. **Item 6 needs a witness fetcher**, not a metadata census. `tools/historical-v3/build_chunk.py` is the
   closest existing thing and targets an older statement; extending it to chunk-transition v3 and
   running ≥1,000 consecutive heights is the only way to satisfy the item.
5. Re-run `corpus_manifest.py --verify docs/evidence/lean-chunk-L7/corpus-manifest.json` after any
   corpus move, and `make pin-check` on integration.
