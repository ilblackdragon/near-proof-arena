# L0 — boundary and coverage inventory (handoff)

## Identity

* **Owner**: L0 (boundary and coverage inventory), subagent of the `lean-chunk-transition-plan` lead.
* **Worktree**: `/data/illia/nearproof-wt/lean-chunk-L0`
* **Branch**: `lane/lean-chunk-L0`
* **Base commit**: `833f3311c26baa3144a1aece84f0c9d0f25d4f08` (`docs: plan full Lean chunk transition and arena acceptance gates`)
* **Committed tip**: `ec5f5a361` + the follow-up docs commit on this branch (see `git log --oneline -3`)
* **Merged**: no. Pending lead review/integration.
* **Nearcore**: `/data/illia/nearproof-deps/nearcore` @ `44f7ae6cd7ef08bab604e20a473bf77e35d4c993` (2.13.4), PV 86.
* **Documentation only**: no Lean source, Rust source, corpus, oracle or plan file was modified.

## Deliverables

| file | sha256 | notes |
|---|---|---|
| `docs/research/lean-chunk-coverage.json` | `2d058b576fb4a0fdf4609ccef389a87d617d8aa3125c0f00b8444291b648ecfe` | 117 rows + `_meta` + oracle marks + exclusions + UQs |
| `docs/research/lean-chunk-coverage.md` | `98d5d95aaaa11e66d8d8dd1ab59fe5921a7b97821e776f1f5aa0f44e89465dd3` | readable summary, regenerated from the JSON |
| `docs/research/lean-chunk-coverage-gen.py` | in the same commit | generator; the JSON is reproducible from it |

Hashes are of the committed objects; re-run `sha256sum` after any edit.

## Actual counts

* 117 rows, 8 families: `d2-core` 58, `d3-hook` 17, `wasm-prepare` 8, `wasm-exec` 7,
  `wasm-domain` 3, `layer-boundary` 12, `claim-fact` 8, `evidence` 4.
* Statuses: `implemented` 53, `validated` 35, `partial` 7, `missing` 14, `impossible-at-boundary` 8.
* 11 distinct oracle `d3_violations` strings (10 in d3c9); 1 mismapped (`c.no_resharding`).
* 17 unresolved boundary questions (UQ-001…UQ-017), each with an owning lane.
* Guard census (comment-stripped source): 1,014 decision sites across 30 modules; 148 `out of domain`
  string sites; 96 `unmodeled` sites (see `_meta.guards_per_module` for the per-module table).
* Corpus evidence (carried forward, **not re-run**): 115,284 D3 cases / 0 disagreements
  (33,248 / 49,490 / 15,995 / 16,551); verdicts 41,131 accept / 71,605 reject / 2,548 out of domain;
  D2 67,384/67,384; D1 53,048. Checker sha256 `b4154b212fc482af99fafd4a1c4d5cf6b1157f4e26c154fc1a66e907312ce5d8`.

## Inventory IDs owned

All `L0-*` rows in the JSON. By family:

* `L0-D2-001…058` — every rejection/domain guard in `checkD2Core` plus the D2 decode guards.
* `L0-D3-001…017` — the `FunctionCall` hook: called-vs-imported hosts, `contractOOD`, ETH-implicit,
  balance overflow, global identifier, cold-cache code rule, `MissingTrieValue`, action log, yields,
  gas distribution, `checkD3` wiring.
* `L0-W-001…018` — preparation (floats, `PrepareError` variants, link, resolve), execution
  (loading gas, host dispatch, invariants, curve hosts), and the two disconnected `DomainD3` predicates.
* `L0-LANE-001…012` — D1/D0/D1a layer boundaries and the D2 lifts.
* `L0-CLAIM-001…008` — the trusted facts that no relation over claim+witness can authenticate.
* `L0-EVID-001…004` — the regression evidence and the claim-scan negative evidence.

## Implemented behaviour (what the checker actually decides)

1. Full D2 transition: every non-WASM action, receipts, delayed/outgoing queues, congestion,
   bandwidth scheduler, validator updates, implicit transitions, multi-epoch segments with one layout,
   and the complete trie semantics. 64 decision sites, all with discriminating corpus mutants.
2. D3 `FunctionCall` on `None`/`Local` contracts with cold-cache code loading, `VMContext`, execution,
   receipt manager, yields, gas distribution, return data, account write-back, subsidised amount.
3. WASM preparation and execution for the integer subset: wasmparser-equivalent validation,
   finite-wasm stack/gas analysis, instrumentation limits, linking (89 PV86 signatures), method
   resolution, and a fuel-bounded interpreter.
4. Domain exclusions are *reported*, never silently accepted: `out of domain` is not `accept`.

## Remaining gaps + dependencies

| gap | rows | lane | why it is a gap (not a boundary impossibility) |
|---|---|---|---|
| floats | `L0-W-001,002,003,012,018` | L2 | floats are enabled at PV86 (`features.rs:47-59`); 160 corpus chunks |
| secp256k1, ML-DSA-65, curve hosts | `L0-LANE-002,003,005`, `L0-W-015`, `L0-D3-001` | L3 | live key types / host functions at PV86 |
| global contracts, state-init, gas keys, ETH-implicit legacy wallet, action log | `L0-D3-006,008,012`, `L0-LANE-004` | L4 | live action tags 9–11 at PV83/85 |
| resharding / split gate | `L0-D2-012,019`, `L0-W-016` | L6 | validator has a resharding branch; **corpus has zero cases** |
| genesis main transition | `L0-D2-027`, `L0-W-*` n/a | L9 | `MainTransition::Genesis` is a first-class branch; 137 cases |
| `G_α`, `n_blocks ≤ 32`, witness/claim size | `L0-D2-015,041`, `L0-W-017` | L1 | capacity/format choices; 1,010 + 3 protocol-valid cases |
| narrowed `e.code_cache` | `L0-D3-009` | L1 + L7 | committed deploys are deterministic; 169 cold-accept cases |
| `w.size` storage-proof bound | `L0-D2-040` | L5 | inequality marked unverified; PV86 enforces the per-receipt limit |
| trusted facts | `L0-CLAIM-001…008` | L8 | outside `Rel` by construction |

## Failing cases

None. L0 re-ran no corpus and made no semantic change. The one checker invocation performed was a
spot check, all as recorded:

```
nearspec-v3-check-d3 d3c7/ood/03-h10042-s1        -> accept
nearspec-v3-check-d3 d3c7/ood/05-h10102-s0        -> out_of_domain (c.segment)
nearspec-v3-check-d3 d3c9/ood/00-h10006-s2        -> out_of_domain (e.g_alpha: 9,433,218,286,510 > G_α)
nearspec-v3-check-d3 d3c7/d3/00-h10027-s2         -> accept
```

`oracle/tools/spec_check_v3_d3.py` on the same cases agrees (`ok`, `c.segment`, `e.g_alpha`, `ok`).

## Findings the lead must act on

1. **`c.no_resharding` is a false-positive oracle mark.** All 1,127 tagged claims have one
   byte-identical shard layout and no split gate; 700 are accepted by Lean, Python *and* nearcore.
   Consequence: **no resharding case exists in the corpus**, so `c.same_layout`/`c.no_split_gate` have
   zero coverage. Fix the oracle classifier before L6 measures progress.
2. **The called-vs-imported trap is already correct.** `realOodHosts`/curve gates live in `callHost`
   (`Exec.lean:72,78`); the import gate at `Exec.lean:462-464` is harness-only (`real.isNone`).
   `oodHosts` in `FunctionCall.lean:51` is dead code duplicating `Wasm.realOodHosts`.
3. **`Wasm.DomainD3.noResharding` / `contractInD3α` are disconnected.** Not in the import closure of
   `checkD3` (verified), and `contractInD3α` is *stricter* than the checker (it rejects curve imports
   that P3 allows). The statement of record must be chosen (UQ-010).
4. **Every semantic exclusion is a live PV86 path.** D3α is sound but not complete; Gate B needs
   L2/L3/L4/L6/L9 plus the two L1 capacity decisions.
5. **`e.code_cache` is too broad.** A committed in-chunk deploy is served deterministically by
   `ContractsTracker` (`contract.rs:42-131`); 169 of the 279 excluded cases are cold-validator accepts.

## Changed declarations / theorems

None. L0 changed no Lean declaration and added no theorem. Residual premises: **none** (no Lean change).

## Build/test commands

```sh
# regenerate the inventory (documentation only)
python3 docs/research/lean-chunk-coverage-gen.py > docs/research/lean-chunk-coverage.json

# validate JSON and the row schema
python3 - <<'PY'
import json
d=json.load(open('docs/research/lean-chunk-coverage.json'))
assert {tuple(sorted(r)) for r in d['rows']} == {('acceptance_tests','dependencies','domain_guard',
  'evidence','family','id','lean_path_symbol','nearcore_commit','nearcore_path_symbol','owner',
  'remaining_work','status')}
assert all(r['status'] in {'implemented','partial','missing','impossible-at-boundary','validated'} for r in d['rows'])
print(len(d['rows']))
PY

# one cheap checker invocation (allowed by the brief)
BIN=/data/illia/nearproof-wt/lean-chunk-transition-plan/oracle/wasm-d3/lean/.lake/build/bin/nearspec-v3-check-d3
$BIN /data/illia/nearproof-deps/corpora/d3c7/ood/03-h10042-s1
```

No long build was run. No network access was used.

## Evidence paths

* `var/d3-runs/report-d3-full.json` and `var/d3-runs/full-d3c{7,8,9,10}/lean.jsonl`
  (in `/data/illia/nearproof-wt/lean-chunk-transition-plan`, read-only).
* `/data/illia/nearproof-deps/corpora/d3c{7,8,9,10}` — 115,284 `meta.json`; `summary.json` hashes
  recorded in `_meta.case_count_provenance.oracle_summary_sha256`.
* Lean sources cited per row (`ChunkValidationD2.lean`, `D3/FunctionCall.lean`, `Wasm/*`, `D2/*`,
  `ChunkValidationD1/D1a/V0/V0a`, `Layout.lean`, `Wire.lean`, `PrepD0.lean`).
* nearcore sources cited per row (`chain_validation.rs`, `contract_code.rs`, `contract.rs`,
  `function_call.rs`, `pipelining.rs`, `imports.rs`, `features.rs`, `version.rs`, `action/mod.rs`,
  `signature.rs`, `prepare_v3.rs`, `wasmtime_runner/mod.rs`, `mainnet_genesis.json`,
  `runtime_configs/*.yaml`).

## Next executable step

1. Lead: review `_meta` + the 14 `missing` rows; decide UQ-001 (cache-independent statement) and
   UQ-010 (`checkD3` vs `DomainD3` as the statement of record) — these block L1.
2. Fix the oracle `c.no_resharding` classifier (oracle/v3-d3/src/d3.rs:152-158) and regenerate a real
   resharding corpus before L6 starts; otherwise L6 has no measurement.
3. L2 can start immediately from `L0-W-001..003,012` (float sites) with the directed `d3float` contract.
4. L3 can start from `L0-LANE-002/003/005` + `L0-W-015`.
5. L9 (genesis) is small and unblocks 137 cases: `L0-D2-027` + claim-v3 T14.

## Files safe for the next agent to edit

* `docs/research/lean-chunk-coverage-gen.py` (regenerate the JSON after edits).
* `docs/research/lean-chunk-coverage.json` and `.md` (regenerated, not hand-edited).
* `docs/logs/lean-chunk-L0-2026-10-23.md` (append-only).
* Nothing under `spec/lean/`, `oracle/`, `rust/` was touched by L0; those are free for the owning lanes.
