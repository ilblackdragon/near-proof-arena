# L0 — boundary and coverage inventory (handoff)

## Identity

* **Owner**: L0 (boundary and coverage inventory), subagent of the `lean-chunk-transition-plan` lead.
* **Worktree**: `/data/illia/nearproof-wt/lean-chunk-L0`
* **Branch**: `lane/lean-chunk-L0`
* **Base commit**: `833f3311c26baa3144a1aece84f0c9d0f25d4f08`
* **Committed tip**: see `git log --oneline -1`; this log and the artifacts are in the same commit.
* **Merged**: no. Pending lead review/integration.
* **Nearcore**: `/data/illia/nearproof-deps/nearcore` @ `44f7ae6cd7ef08bab604e20a473bf77e35d4c993` (2.13.4), PV 86.
* **Documentation/research tooling only**: no Lean source, Rust source, corpus, oracle or plan file changed.

## Deliverables

| file | sha256 | notes |
|---|---|---|
| `docs/research/lean-chunk-coverage.json` | `3f9059b5712f4d84470477f0e091632cb8b5d29348949427e1ff08e07965af1b` | 219 rows + `_meta` sections |
| `docs/research/lean-chunk-coverage.md` | `cc20a12d88e0fdc66babc31c7277d92d17446e075bdcf9bae66e51687b14201a` | readable summary |
| `tools/d3/lean_chunk_coverage.py` | `dc43a4a7f4596ed44716b7cbf50ae592c1beaa5e3da08228c492f935454b9b9f` | drift gate, extended to cover all rows |
| `tools/d3/lean_chunk_coverage_l0.py` | `eb5bd3cfb9fcd36f72e1830874fab01d19b69aa8f76285d125d7880dea946773` | execution/boundary row generator |

Hashes are of the committed objects; re-run `sha256sum` after any edit.

## Reconciliation note (read this first)

Main (`d261f1f07`) already carried an L0 static dispatch inventory (114 rows: 92 hosts, 15 actions,
2 instruction families, 4 domain guards, 1 resharding boundary) and the drift-gated generator
`tools/d3/lean_chunk_coverage.py`. My first pass wrote a separate 117-row file with a different
`_meta` shape, which would have **replaced** that artifact and broken `--check`. The merged result:

* main's 114 rows are preserved byte-for-byte (same ids, same generator);
* my execution/boundary rows are added as 105 more rows in the same schema, so **219 rows**;
* `tools/d3/lean_chunk_coverage.py` now merges both and its `--check` covers both, including the Lean
  source hashes of the additional modules;
* schema is `near-lean-chunk-coverage-v2` (v1 was main's 114-row file).

The 105 added rows are `d2-core` (58), `d3-hook` (17), `wasm-prepare` (8), `wasm-exec` (7),
`wasm-domain` (3), `claim-fact` (8), `evidence` (4). I dropped my 12 `layer-boundary` rows because
main's action/host/domain rows already cover that ground at finer granularity.

## Actual counts

* 219 rows, 12 families: action 15, host 92, instruction 2, domain_guard 4, boundary 1,
  d2-core 58, d3-hook 17, wasm-prepare 8, wasm-exec 7, wasm-domain 3, claim-fact 8, evidence 4.
* Statuses: `implemented` 137, `validated` 35, `partial` 6, `missing` 30,
  `impossible-at-boundary` 11.
* `impossible-at-boundary` = 3 test-feature hosts (`burn_gas`, `sandbox_debug_log`, `sleep_nanos`)
  + 8 trusted claim facts. **No semantic exclusion is classified impossible.**
* Missing by lane: L3 15, L4 5, L2 5, L6 3, L0 1, L9 1. Partial: L1 4, L5 1, L0 1.
* 11 distinct oracle `d3_violations` strings (10 in d3c9); 1 mismapped (`c.no_resharding`).
* 17 unresolved boundary questions (UQ-001…UQ-017), each with an owning lane.
* Guard census: 30 modules, 1,014 decision sites, 148 `out of domain` string sites, 96 `unmodeled`.
* Corpus evidence (carried forward, **not re-run**): 115,284 D3 cases / 0 disagreements
  (33,248 / 49,490 / 15,995 / 16,551); 41,131 accept / 71,605 reject / 2,548 out of domain;
  D2 67,384/67,384; D1 53,048. Checker sha256 `b4154b2…2ce5d8`.

## Inventory IDs owned

* main's `L0-action-00…14`, `L0-host-*` (92), `L0-instr-*`, `L0-guard-*`, `L0-resharding`.
* mine: `L0-D2-001…058`, `L0-D3-001…017`, `L0-W-001…018`, `L0-CLAIM-001…008`, `L0-EVID-001…004`.

## Implemented behaviour (what the checker decides)

1. Full D2 transition: every non-WASM action, receipts, delayed/outgoing queues, congestion,
   bandwidth scheduler, validator updates, implicit transitions, multi-epoch segments with one layout,
   full trie semantics. Its guards carry 85–14,246 discriminating corpus rejects each.
2. D3 `FunctionCall` on `None`/`Local` contracts: cold-cache code loading, `VMContext`, execution,
   receipt manager, yields, gas distribution, return data, account write-back, subsidised amount.
3. WASM preparation/execution for the integer subset: wasmparser-equivalent validation, finite-wasm
   stack/gas analysis, instrumentation limits, linking (89 PV86 signatures), method resolution,
   fuel-bounded interpreter.
4. Domain exclusions are reported (`out of domain`), never silently accepted.

## Remaining gaps + dependencies

| gap | rows | lane | why it is a gap, not a boundary impossibility |
|---|---|---|---|
| floats | `L0-instr-float`, `L0-guard-floatOutOfDomain`, `L0-W-001/002/003` | L2 | floats enabled at PV86 (`features.rs:47-59`); 160 corpus chunks |
| curve hosts | `L0-host-*` ×14, `L0-W-015` | L3 | all 14 production-enabled at PV86 |
| secp256k1 / ML-DSA-65 | `L0-D3-*`, `L0-CLAIM-*` n/a | L3 | live key types (`signature.rs:250-257`); ML-DSA at PV85 |
| global contracts / state-init / gas keys | `L0-action-09/10/11`, `L0-D3-008`, `L0-D3-012` | L4 | tags 9–11 live at PV83/85 |
| ETH-implicit legacy wallet | `L0-D3-006` | L4 | deterministic from `chain_id` (`contract_code.rs:56-76`) |
| resharding / split gate | `L0-resharding`, `L0-D2-012/019`, `L0-W-016` | L6 | validator has the branch; **corpus has zero cases** |
| genesis main transition | `L0-D2-027` | L9 | `MainTransition::Genesis`; 137 cases |
| `G_α`, `n_blocks ≤ 32`, claim/witness size | `L0-D2-015/041` | L1 | capacity/format; 1,010 + 3 protocol-valid cases |
| narrowed `e.code_cache` | `L0-D3-009` | L1 + L7 | committed deploys are deterministic; 169 cold-accepts |
| `w.size` storage-proof bound | `L0-D2-040` | L5 | marked unverified; PV86 per-receipt limit |
| trusted facts | `L0-CLAIM-001…008` | L8 | outside `Rel` by construction |

## Failing cases

None. L0 re-ran no corpus and changed no semantics. One cheap checker invocation was made as a spot
check; all matched the record:

```
nearspec-v3-check-d3 d3c7/ood/03-h10042-s1   -> accept
nearspec-v3-check-d3 d3c7/ood/05-h10102-s0   -> out_of_domain (c.segment)
nearspec-v3-check-d3 d3c9/ood/00-h10006-s2   -> out_of_domain (e.g_alpha: 9,433,218,286,510 > G_α)
nearspec-v3-check-d3 d3c7/d3/00-h10027-s2    -> accept
```

`oracle/tools/spec_check_v3_d3.py` agreed on the same cases (`ok`, `c.segment`, `e.g_alpha`, `ok`).

## Findings the lead must act on

1. **`c.no_resharding` is a false-positive oracle mark.** All 1,127 tagged claims have one
   byte-identical shard layout and no split gate; 700 are accepted by Lean, Python *and* nearcore.
   Consequence: **no resharding case exists in the corpus**, so `c.same_layout`/`c.no_split_gate` have
   zero coverage. Fix `oracle/v3-d3/src/d3.rs:152-158` before L6 measures progress.
2. **The called-vs-imported trap is already correct.** `realOodHosts`/curve gates live in `callHost`
   (`Exec.lean:72,78`); the import gate at `Exec.lean:462-464` is harness-only (`real.isNone`).
   `oodHosts` (`FunctionCall.lean:51`) is dead code duplicating `Wasm.realOodHosts`.
3. **`Wasm.DomainD3.noResharding` / `contractInD3α` are disconnected.** Verified not in the import
   closure of `checkD3`; `contractInD3α` is *stricter* than the checker (rejects curve imports that P3
   allows). Choose the statement of record (UQ-010).
4. **Every semantic exclusion is a live PV86 path.** D3α is sound but not complete; Gate B needs
   L2/L3/L4/L6/L9 plus the L1 capacity decisions.
5. **`e.code_cache` is too broad.** A committed in-chunk deploy is served deterministically by
   `ContractsTracker` (`contract.rs:42-131`); 169 of the 279 excluded cases are cold-validator accepts.

## Changed declarations / theorems

None. No Lean declaration changed; no theorem added. Residual premises: **none**.

## Build/test commands

```sh
# regenerate the inventory (research tooling only)
python3 tools/d3/lean_chunk_coverage.py --repo . \
    --nearcore /data/illia/nearproof-deps/nearcore \
    --output docs/research/lean-chunk-coverage.json

# drift gate (exit 1 on drift)
python3 tools/d3/lean_chunk_coverage.py --repo . \
    --nearcore /data/illia/nearproof-deps/nearcore \
    --check docs/research/lean-chunk-coverage.json

# schema assertions
python3 - <<'PY'
import json
d=json.load(open('docs/research/lean-chunk-coverage.json'))
req={'id','family','nearcore_commit','lean_path_symbol','nearcore_path_symbol','status',
     'domain_guard','evidence','owner','dependencies','acceptance_tests','remaining_work'}
assert all(set(r)==req for r in d['rows'])
assert all(r['status'] in {'implemented','partial','missing','impossible-at-boundary','validated'}
           for r in d['rows'])
assert len({r['id'] for r in d['rows']})==len(d['rows'])
print(len(d['rows']))
PY

# one cheap checker invocation
BIN=/data/illia/nearproof-wt/lean-chunk-transition-plan/oracle/wasm-d3/lean/.lake/build/bin/nearspec-v3-check-d3
$BIN /data/illia/nearproof-deps/corpora/d3c7/ood/03-h10042-s1
```

No long build was run. No network access was used.

## Evidence paths

* `var/d3-runs/report-d3-full.json`, `var/d3-runs/full-d3c{7,8,9,10}/lean.jsonl` (read-only, plan worktree).
* `/data/illia/nearproof-deps/corpora/d3c{7,8,9,10}` — 115,284 `meta.json`; `summary.json` sha256
  recorded in the JSON `_meta`.
* Lean sources cited per row; nearcore sources cited per row.

## Next executable step

1. Lead: review the 30 `missing` rows; decide UQ-001 (cache-independent statement) and UQ-010
   (`checkD3` vs `DomainD3`) — these block L1.
2. Fix the oracle `c.no_resharding` classifier and generate a real resharding corpus before L6 starts.
3. L2 starts from `L0-instr-float`, `L0-guard-floatOutOfDomain`, `L0-W-001..003`.
4. L3 starts from `L0-host-*` (14 curve) + `L0-D3-*` secp/ML-DSA rows.
5. L9 (genesis) is small and unblocks 137 cases: `L0-D2-027` + claim-v3 T14.

## Files safe for the next agent to edit

* `tools/d3/lean_chunk_coverage.py` and `tools/d3/lean_chunk_coverage_l0.py` (then regenerate the JSON).
* `docs/research/lean-chunk-coverage.json` (generated — do not hand-edit; regenerate).
* `docs/research/lean-chunk-coverage.md` (regenerated summary).
* `docs/logs/lean-chunk-L0-2026-10-23.md` (append-only).
* Nothing under `spec/lean/`, `oracle/`, or `rust/` was touched by L0.
