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

  **Update (host-rows, [host-rows/README.md](host-rows/README.md)).** The new opt-in
  `oracle/v3-successor` scenario `host-rows` adds 4 seeds (11,437 cases, each judged by cold
  nearcore). It calls the 7 uncalled hosts and the 9 hosts that lacked a negative, with full mutant
  sets. 15 of those 16 rows are now promoted, so 74 of the 75 non-curve host rows are validated.
  `current_contract_code` stays `implemented`: Lean returns 1 on a global-contract account, where
  nearcore returns 2 or 3. That makes Lean reject 205 nearcore-accepted cases (a completeness bug;
  0 Lean accepts of a nearcore reject). `l0_exercise.py map` now excludes disagreeing cases from
  the exercising evidence. `evidence --disagreement-cause` attributes them to their cause row, and
  `promote_row` refuses a row that causes disagreements.

  **Fixed** ([host-rows/ccc-fix](host-rows/ccc-fix/README.md)). `CallCtx` now carries the
  account's contract kind, and the arm returns 1, 2 or 3 as nearcore does. On the new checker
  (`ee00c918…`) the 205 disagreements are 0, and the census, fixtures and a 1-in-8 corpus sample
  do not move. `current_contract_code` is now `validated`: all 75 non-curve host rows are.
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
1. *7 uncalled hosts.* **Done** ([host-rows](host-rows/README.md)): scenario `host-rows` in
   `src/xfam.rs`, contract `contracts/hostrows.wat`, 4 seeds. All 7 are promoted; `current_contract_code`
   only after its Lean completeness fix ([host-rows/ccc-fix](host-rows/ccc-fix/README.md)).
2. *9 hosts without a negative chunk.* **Done** ([host-rows](host-rows/README.md)). The same
   scenario calls `kgashost` and the global-promise `all-hosts-valid-receivers` contract, with full
   mutant sets, instead of regenerating the corpus chains. All 9 are promoted.
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
