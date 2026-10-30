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
