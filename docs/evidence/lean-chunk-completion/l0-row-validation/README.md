# L0 row validation: per-row exercise map and breakage controls (2026-10-31)

This package promotes coverage rows from `implemented` to `validated` one row at a time. Each
promoted row has:

- whole-chunk cases that exercise that row, judged by cold pinned nearcore 2.13.4 (claim mutants:
  by the claim-v3 discipline);
- a breakage control that perturbs only that row and is caught by the comparison.

The per-row record is [`rows.json`](rows.json). `tools/d3/lean_chunk_coverage.py`
(`promote_row`) reads it and applies the promotion rule stated there.

## Method

**1. Control build (never on the default path).** `tools/d3/l0_ctl_patch.py` edits a copy of
`spec/lean` (from `git archive HEAD`) and adds the executable `nearspec-v3-ctl-successor`. Every
hook is an `@[implemented_by]` on an existing definition, so the kernel term of every Lean
definition is unchanged. Only the compiled code of the copy differs. The hooks are:

| definition | trace (`NEARSPEC_TRACE=1`) | ablation (`NEARSPEC_ABLATE=…`) |
|---|---|---|
| `Wasm.Exec.callHost` | `H <name>` when an arm runs | `host:<name>`: the arm burns 1 extra gas before it runs |
| `Successor.StorageExecution.applyAction` (the `allFeatures` action dispatch) | `A <tag>` (`D8`/`D14` for delegates) | `act:<tag>`: the action reports 1 extra gas burnt and used |
| `ChunkValidationV0.check` | (the verdict reason) | `guard:<msg>`: a failing check with that message passes |

Re-running the generator on a fresh `git archive` reproduces the built tree byte for byte. The
incremental build of the copy took 50 s.

**2. Verdict identity.** With the trace on and no ablation, the control build returns the same
verdict and reason as the default checker on every case:
- the 51,164-case sample;
- the 2,218-case supplement;
- the 132 guard mutants.

The default checker is the Gate-B freeze binary `gateb-freeze-2368b8713/checker`
(sha256 `9b583e3a…`; control build `16238557…`, both in `rows.json`). Its `spec/lean` is identical to this commit's.

**3. Populations, all replayed through `tools/d3/replay_successor.py` (allFeatures).**

| population | cases | default-checker replay |
|---|---|---|
| all non-mutant corpus cases (d1run, d2corpus.v2, d3c7–d3c10, honest + ood) + census + fixture families + 5 % of corpus mutants (seed 20261031) | 51,164 | 0 verdict disagreements; 0 Lean-accept/nearcore-reject. The comparator's 16 "disagreements" are all the named `e.code_prep_race` exclusion on pipeline-race fixtures (never an accept) |
| 20 % of the nearcore-rejected mutants of state-init-emit, dist-identity and the y4242 yield regen (seed 31) | 2,218 | pass, 0 disagreements |
| guard mutants (`guard-mutants/`, `tools/d3/l0_guard_mutants.py`) | 132 | pass, 0 disagreements |

**4. Exercise map** (`l0_exercise.py map`). A row's exercising cases are the cases where the
trace shows its arm or tag firing and the default verdict is accept or reject (never out of
domain). Each case is split by `meta.json` `expected_rel`: cold nearcore, or claim-v3 for claim
mutants.

**5. Controls** (`l0_exercise.py ablate`). For each row, the tool picks up to 12 nearcore-accepted
and 4 nearcore-rejected exercising cases, spread over the corpus and fixture families. It then
replays them twice with the repository comparator: once unablated, which must pass, and once with
the row's ablation. The control *detects* the row iff the ablated replay disagrees with nearcore
on at least one case.

**Promotion rule** (`lean_chunk_coverage.py`, `ROW_MIN_*`):
- host and action rows need ≥ 1 nearcore-accepted and ≥ 1 nearcore-rejected exercising case;
- d2-core guards need ≥ 1 deciding reject, meaning that guard's message is the first failure;
- every row also needs an unablated pass and ≥ 1 ablated disagreement.

## Results

- **Hosts.** 68 of the 75 non-curve host rows fire in the populations. All 68 controls detect
  (1–12 flipped cases per row).
  - 59 rows are promoted.
  - 9 rows have only nearcore-accepted exercising chunks, and their controls still detect. They
    stay `implemented`, as listed below.
  - 7 rows never fire.
- **Actions.** All 12 implemented tags are exercised, including Delegate (8) and DelegateV2 (14).
  Each has 76–4,771 nearcore-rejected exercising chunks, and every control flips 12 of 16 cases.
  All 12 are promoted.
- **d2-core guards.** The directed claim mutants make 11 guards the first failure (12 mutants
  each, 132/132 reject). For 7 of them, removing the guard changes the verdict:
  - D2-016, 017, 028, 030, 031 and 037 accept the false claim;
  - D2-010 ends out of domain (`c.pv86`).

  Those 7 are promoted. For the other 4 (D2-006, 007, 021, 022), a later guard rejects the same
  mutant, so removing the guard leaves the verdict unchanged. They stay `implemented` (see below).

## Rows left `implemented`, with reasons

| rows | reason | next step |
|---|---|---|
| hosts `promise_batch_action_{add_gas_key_with_full_access, add_gas_key_with_function_call, deploy_global_contract, deploy_global_contract_by_account_id, state_init, state_init_by_account_id, transfer_to_gas_key, use_global_contract_by_account_id}`, `set_state_init_data_entry` | positive chunks plus a detecting control, but no nearcore-rejected chunk exercises them. Their fixtures (key-family, global-promise, corpus ood) have no mutant sets on disk. A `t.tx_valid` flip is **not** a valid negative: `tx_valid` is a trusted claim input (`verdict_source: nearcore(tx_valid=claim)`), and 4 of 87 such flips are accepted by both nearcore and Lean | generate mutant sets of those fixture chains with `oracle/v3-successor` and re-run `l0_exercise.py` |
| hosts `current_contract_code`, `refund_to_account_id`, `promise_set_refund_to`, `storage_iter_prefix`, `storage_iter_range`, `storage_iter_next`, `gas` | no case in any population calls them. They are importable at PV86: `imports.rs:197,201-202,341`. `storage_iter_*` returns `HostError::Deprecated` (`logic.rs:4353`). `gas` is `VMLogic::gas` (`logic.rs:1956`) | add `oracle/v3-successor` scenario contracts calling each, judged cold; then trace and ablate |
| L0-D2-006, 007, 021, 022 | a deciding fixture exists (12 mutants each, rejected with the guard's reason), but the guard is verdict-redundant: without it, the empty segment, duplicate epoch, reversed or gapped segment is rejected by a later guard. No verdict-level control can detect its removal | a theorem that the later guard implies it would make the redundancy explicit |
| other d2-core guards (D2-001…005, 009, 011–014, 019, 020, 023–026, 033, 038, 039, 057) | not targeted in this pass. Some are unreachable as a first failure: D2-009 is implied by D2-008, D2-023 is pre-empted by the `chunk_headers_root` check, D2-014's mutants fail at the encoded-root comparison. Some are throws, not `check` calls (D2-024, 026, 057). D2-005/011 are statement-scope (`c.pv86`) out-of-domain guards, and the comparator counts their exclusion of a PV85 claim as a disagreement | per guard: a directed mutant plus a `throw`-level hook in `l0_ctl_patch.py` |
| d3-hook rows, wasm-prepare/-exec rows, `L0-instr-*`, domain guards, `L0-AF-fuel-certificate`, retired W rows | not addressed by this pass (their hooks are elsewhere in the successor path) | — |

## Reproduce

```
git archive HEAD spec/lean formal-core | tar -x -C $T; cp -a <existing .lake dirs> …
python3 tools/d3/l0_ctl_patch.py $T && (cd $T/spec/lean/v3 && lake build nearspec-v3-ctl-successor)
python3 tools/d3/l0_exercise.py trace    --binary CTL --cases-file sample.txt --out trace.jsonl --jobs 5
python3 tools/d3/l0_exercise.py identity --trace trace.jsonl --reference default-replay/results.jsonl
python3 tools/d3/l0_exercise.py map      --trace trace.jsonl trace-supp.jsonl --out map.json
python3 tools/d3/l0_exercise.py ablate   --binary CTL --map map.json --out ablate.json --workdir abl --targets …
python3 tools/d3/l0_guard_mutants.py --bases bases.txt --out guard-mutants --per-kind 12
python3 tools/d3/l0_exercise.py evidence --map map.json guard-map.json --ablate ablate.json guard-ablate.json --out rows.json
```

The working files are under `/data/illia/nearproof-deps/l0-validate/runs/` on the lane host:
sample lists, traces, maps, and every replay report (baseline and ablated).

## Second pass: status and exact next steps (handover, 2026-10-31)

The coordinator asked for the 72 remaining rows to be continued on this branch. Main has been merged
in (`773bc4133`). This handover records what is established and gives the exact order of the
remaining work. No new row has been promoted yet.

**Established from pinned source (nearcore `44f7ae6c`), for the uncalled hosts:**
- `storage_iter_prefix`, `storage_iter_range` and `storage_iter_next` are ordinary `env` imports
  (`runtime/near-vm-runner/src/imports.rs:341-343`).
  - Importing them is **not** a link error: a module that imports them prepares and instantiates.
  - Calling one is a **trap**. The body returns `Err(HostError::Deprecated { method_name })`
    (`logic/logic.rs:4353-4357` and the two following functions), so the function call fails with
    `FunctionCallError::HostError(Deprecated)`.
  - Lean matches this: `Wasm/Host.lean:910-915` pops the arguments and aborts with the same
    `Deprecated { method_name: … }` error.
  - Fixture to build: a contract that imports one of them, with one method that calls it (expected:
    receipt failure with `Deprecated`, chunk accepted) and one that does not (expected: success).
    Add a mutant set for each, and use the ablation `host:storage_iter_*`.
- `gas` is `@as gas: gas_seen_from_wasm<[opcodes: u32]>` (`imports.rs:344`), meaning
  `gas_opcodes(opcodes)`: it burns `opcodes × regular_op_cost` (`logic.rs:1960-1977`). A contract
  may import and call `env.gas` directly. Lean has `Wasm/Host.lean:804-806`:
  `burnH (a[0] * 822756)`. Fixture to build: a contract that calls `gas(k)` for small k, plus a k
  that exceeds prepaid gas.
- `current_contract_code`, `refund_to_account_id` and `promise_set_refund_to` are plain imports
  (`imports.rs:197,201-202`). Fixture to build: a contract that calls each one, including on an
  account with no code (`current_contract_code` returns 0) and with an invalid account id
  (`promise_set_refund_to`).

**Next steps, in order:**
1. *7 uncalled hosts.*
   - Add the contracts above to `oracle/v3-successor/contracts` and a scenario in `src/scenarios.rs`.
   - Generate ≥ 4 seeds with mutants. Use the generator's normal path: cold nearcore judges, and the
     mutant set comes from the same tool as the corpus `hdr.*`/`w.*` classes.
   - Add the new cases to a population file and run `l0_exercise.py trace`, then `map`, `ablate`
     and `evidence`.
2. *9 hosts without a negative chunk.* Run the same generator with its mutant classes over the
   key-family, global-promise and corpus-ood chains that already exercise them. Their bases are
   listed in `map2.json` (lane host). Then rerun `trace`, `map` and `evidence`. Their controls
   already detect.
3. *Throw guards* (D2-009, 024, 026, 057 and the genesis-branch throws).
   - Extend `l0_ctl_patch.py`: wrap each targeted `throw "…"` in the successor core with
     `Ctl.thr "<msg>"`. That is a copy-with-edits of `checkD2CoreGWith` / `checkD2CoreWith` under
     `@[implemented_by]`, with the same template as `applyActionOrig`/`applyActionCtl`.
   - Deciding fixtures: D2-057 uses the corpus `w.trailing_byte` mutants (2,530; 13 listed in
     `runs/trailing.txt`). D2-024 needs a claim mutant whose `chunk_inner` names a shard outside the
     layout. D2-026 needs a segment with no new chunk.
4. *Masked guards D2-006/007/021/022.* The ablated replays show which later guard catches each
   mutant:
   - D2-006 (empty segment) → `segment does not start at prev_block_hash` (D2-021);
   - D2-022 → `source_receipt_proofs contains extra proofs` or `segment does not reach the
     last-but-one new chunk`;
   - D2-007 and D2-021 → reject (reasons in `runs/guard-abl-repo/*/ablated/results.jsonl`).

   The source argument for D2-006 is direct. With no blocks, `hashes.headD [] = []`, which is never
   a 32-byte `prevBlockHash`, so D2-021 fails whenever D2-006 would. A small Lean lemma over
   `checkD2CoreGWith` would make this a proof. For 007/021/022, try mutants that keep the later
   check satisfied:
   - 007: duplicate a *referenced* epoch while keeping `epochs == referenced`. This is impossible,
     because `referenced` is deduplicated and sorted, so `strictlyAscending` failing implies the
     equality fails. That makes 007 subsumed by D2-008.
   - 021: a reversed segment of length 2 whose first block's hash equals `prevBlockHash`. This is
     impossible without a hash collision.
   - 022: a gap. The walk checks then fail, as observed.

   Record each as validated-by-subsumption (the deciding mutants plus the subsuming guard's
   validated row), or as `impossible-at-boundary` where it can never be the first failure. This
   needs a new status path in `promote_row`, with the reason text in `rows.json`.
5. *D3 hooks (10), wasm-prepare/exec (10), `L0-instr-*` (2), domain guards (5).* These rows cite
   signed-tier lines (`D3/FunctionCall.lean`). Map each to its `allFeatures` site in
   `Successor/StorageExecution.lean` (`functionCallRecorded`), `Wasm/Prepare.lean` and
   `Wasm/Exec.lean` first. Then add hooks the same way:
   - an `@[implemented_by]` copy with a `Ctl.tr` event and an ablation;
   - for instruction families: trace the opcode class in `Wasm.Exec.step`, and ablate by charging
     1 extra gas for one class;
   - rerun the trace over `runs/sample.txt` (≈ 2.5 h at 5 processes);
   - run `ablate` (≈ 10 min).

## Second pass, steps 3–5: results (2026-10-30)

Steps 3–5 of the handover above are done for every non-host row except `L0-D3-006` (handled
separately). Steps 1–2 (the 16 host rows) are handled separately too. Coverage counts move from
139 validated / 14 impossible / 72 implemented to **154 / 36 / 35**.

### Method additions

- **Control build v3** (`ctl-v3`, sha256 `689dbfb4…`, from `tools/d3/l0_ctl_patch.py` on this
  commit). The new hooks are again `@[implemented_by]` copies, so kernel terms are unchanged:
  - `throw:<msg>` on copies of `walkSegment`, `checkReshardCoreObs`, `checkD2CoreWithObs` and
    `checkD2CoreGWith`: a literal `throw "<msg>"` becomes `out of domain (l0-ablated): <msg>`. A throw
    has no continuation value, so the control is "this guard no longer rejects".
  - `guard:decode: Not all bytes read`: the witness decoders skip the trailing-bytes test.
  - `instr:int` / `instr:float` (an `exec` wrapper): each executed instruction of the family
    first charges 1 extra gas. Trace `I int` / `I float`, once per case.
  - `wasm:load`, `wasm:prep`, `wasm:compile` on a copy of `runCallFast`. Compiled code calls
    `runCallFast`, not `runCall`, because of `@[csimp] runCall_eq_fast`; a hook on `runCall` is
    dead code. `wasm:fuelcert` is on a copy of `vmCall`.
- **Where the d2-core guards run on `allFeatures`.** `allFeatures` sets `resharding`, so every
  segment without a genesis block goes to `checkReshardCoreObs` (`Successor/ReshardCore.lean`).
  Only genesis-containing segments go to `checkD2CoreGWith`. Each row's `lean_path_symbol` now
  names those sites, with the signed line kept last.
- **Verdict identity.** With trace on and no ablation, ctl-v3 matches the default checker on all
  4,893 traced population cases: fixture families minus the slow removal-soft, fuel, eval-budget,
  gate-b-caps and storage-limit families, plus 4,000 sampled corpus cases and the runtime-errors
  family. The `t.tx_valid` exec-negs are excluded from every map.
- **New directed claim mutants** (`l0_guard_mutants.py`, now in `guard-mutants/`, 240 in total;
  `index.json`):
  - `l0.c.inner_height_created` (D2-003)
  - `l0.c.epoch_id_next` (D2-004): the chunk is claimed in the prev block's next epoch, with flag 0
    set to 1 and a copied epoch record. Only the witness epoch id disagrees.
  - `l0.c.epoch_id_other` (D2-004, masked)
  - `l0.c.rs_total1` (D2-014)
  - `l0.c.prev_block_merkle_root` (D2-021) and `l0.c.block1_merkle_root` (D2-022): one byte of the
    unused `block_merkle_root` changes a block hash and nothing else.
  - `l0.c.truncate_before_main` (D2-026)
  - `l0.c.other_epoch_pv85` (D2-011)
- **New statuses in `promote_row`** (`lean_chunk_coverage.py`).
  - `validated-by-subsumption` requires all of: ≥ 1 deciding reject, an unablated pass, an ablated
    replay that still rejects every case, every subsuming row validated in the same inventory, and
    a Lean lemma or a source argument.
  - `impossible-at-boundary` needs a reason. Named lemmas must be declared in
    `spec/lean/v3/NearSpecV3/L0GuardSubsumption.lean`.
  - Optional `surface` strings must still occur in the named Lean files, which guards against
    drift.
  - The entries are in `second-pass-statuses.json`; `l0_exercise.py statuses` merges them into
    `rows.json`.
- **Lean** (`L0GuardSubsumption.lean`, in `defaultTargets`; axioms `propext`, `Classical.choice`
  and `Quot.sound` only; no `sorry`):
  - `empty_segment_fails_start`, `pHash_length` (D2-006 ⇒ D2-021 fails)
  - `strictlyAscending_dedupSorted`, `ascending_of_referenced` (D2-008 ⇒ D2-007)
  - `epoch_in_table_of_referenced` (D2-008 ⇒ D2-009)
  - `scheduler_params_pv86` (D2-038 never fails)
  - `base_state_hashes` (D2-039 never fails)

### Rows by new status

**Validated with a detecting per-row control (12):**

| row | deciding / exercising cases | control (flipped / replayed) |
|---|---|---|
| D2-003 | 12 `inner_height_created` | `guard:` → accept, 12/12 |
| D2-004 | 12 `epoch_id_next` | `guard:` → accept, 12/12 |
| D2-021 | 12 `prev_block_merkle_root` | `guard:` → accept, 12/12 |
| D2-022 | 12 `block1_merkle_root` | `guard:` → accept, 12/12 |
| D2-024 | 2 resharding `c.child_layout_is_parent` | `throw:` → excluded, 2/2 |
| D2-026 | 12 `truncate_before_main` | `throw:` → excluded, 12/12 |
| D2-057 | 13 corpus `w.trailing_byte` (cold nearcore) | `guard:` → accept, 13/13 |
| L0-instr-integer | 1,685 accept / 96 reject | `instr:int`, 12/24 |
| L0-W-009 | 1,787 / 102 | `wasm:load`, 12/24 |
| L0-AF-fuel-certificate | 1,788 / 102 | `wasm:fuelcert`, 23/24 |

Note: the first-pass masked mutants for D2-021 and D2-022 (reversed segment, dropped block) are
caught by later guards. The `block_merkle_root` mutants show that both guards are load-bearing.
D2-004's `epoch_id_other` mutants are masked, but its `epoch_id_next` mutants are not.

**Validated through existing evidence entries:**
- D2-002: new `VALIDATION["witness-size"]`, the gate-b-caps wsize fixtures with the pre-lift
  checker as control.
- D3-011: `code-cache`, the same site as D3-009, `CodeResolution.resolveCodeBytes`.

**Validated by subsumption (3):**
- D2-006, subsumed by D2-021 (Lean).
- D2-007, subsumed by D2-008 (Lean).
- D2-014, subsumed by D2-056: the ablated replay rejects all 12 at the encoded-root
  `Reed-Solomon parameters` site.

**impossible-at-boundary (22):**
- Not evaluated on `allFeatures`:
  - D2-001 (`allowCodes = true`)
  - W-001, W-002, W-003, W-018, guard-floatOutOfDomain (`floats`)
  - guard-curveHosts (`curveHosts`)
- Statement scope (`c.pv86`):
  - D2-005: 12 `pv85` mutants, all excluded, none accepted.
  - D2-011: 12 `other_epoch_pv85` mutants, all excluded.
- Never the first failure:
  - D2-009 (Lean)
  - D2-013: the upper bound is lifted, and no nearcore layout has 0 shards.
- Never fails:
  - D2-038, D2-039 (Lean)
  - D2-033: probability below 2^-1024 (assumption recorded).
- Dead code on `allFeatures`:
  - D3-004: the only caller passes a FunctionCall.
  - D3-005: `existenceOk` is checked first.
  - D3-012: UQ-016's static check, `check_action_log_tags.py`, with its `--inject` control.
- Unreachable on any nearcore chain:
  - D3-007: total supply is below 2^128 (assumption recorded).
  - D3-015: 2^64 − 1 yield receipts would be needed.
  - D3-016: bounded by prepaid gas.
- Retired: W-016, W-017.

**Still `implemented`, each with an exact next step in `remaining_work`:**
- **D2-012, D2-019, L0-same-layout, L0-split-gate, guard-noResharding.**
  - Finding: on `allFeatures` these guards are live for genesis-containing segments
    (`checkD2CoreGWith`, `RuntimeCore.lean:436,455`).
  - The earlier text "legacy-core guard only" was wrong for `allFeatures`.
  - None of the 266 genesis-main corpus chunks triggers them. This is an exclusion, never an
    accept.
- **D2-020, D2-023, D2-025.** They need witness mutants judged by cold nearcore:
  - D2-020: an oversized new transaction with the transaction root rehashed.
  - D2-023, D2-025: a fabricated block chain named by both chunk headers.

  No claim-only mutant can make D2-023 or D2-025 the first failure.
- **L0-instr-float, W-012.** 39 accepted cases and a detecting control (12/12). There is no valid
  rejected case once the `t.tx_valid` flips are excluded. Needed: mutant sets of the float chains.
- **W-005.** One accepted case, `PrepareError(Memory)`, and a detecting control. No rejected case.
- **W-006.** No case calls a contract that fails to compile.
- **D3-003, D3-013, D3-014, W-011, W-013, W-014.** These are exclusion paths that fire on 0 of
  235,716 corpus cases. Each `remaining_work` names the proof that would make it dead.

No Lean/nearcore disagreement was found. Every baseline replay passes, and no ablation-free
verdict differs from the default checker. Working files are under
`/data/illia/nearproof-deps/l0-validate/runs/`:
- `trace-g2.jsonl`, `trace-g3.jsonl`, `trace-w2.jsonl`
- `map-g2.json`, `map-w2.json`
- `ablate-g2.json`, `ablate-w2.json`
- `abl-g2/`, `abl-w2/`

The ctl-v3 tree is `l0-validate/tree-g`.
