# G3: the preparation race is decided per call (2026-10-31)

Gate-B finding G3 ([W12 §10, §18](../tier-refinement-w12/README.md)). Before this change the
successor's pipeline model (`Successor.Pipeline`) marked the whole chunk's preparation timing
`uncertain` as soon as one lookahead receipt could not be scheduled — a call on a global-contract
account, or a stored receipt or account the active codec does not decode. Every later call whose code
only an in-chunk deploy served was then `out of domain (e.code_prep_race)`, also where nearcore is
deterministic. Separately, W08's race arm stopped at the *first* racing call, so chunks whose failure
point races but whose verdict does not (W08 §4, §7) were excluded too.

| artifact | sha256 |
|---|---|
| checker before (main `0b0f01ec…`, with the `current_contract_code` and gas-key fixes) | `0b0f01ec382faf1efb70839954c130677d171198331f44c15d043f38e6fe8833` |
| checker after (this branch) | `d2e2e8b4ebd7d22a8c6e24e67f21d79162312527310422a0584690dbb0a12a3d` |
| generator used for the schedule probe (`oracle/v3-successor`, rustc 1.96.0) | `5033076d03bbf2df22c8a60059b4571bd589c2c422fdca98778e16bbc5c16067` |

Ground truth: pinned nearcore 2.13.4 (`44f7ae6c`), PV86, cold validator; the forced schedules are
nearcore's own (`oracle/v3-successor/src/cachejudge.rs`: *eager* delays the deploy's precompile so a
worker submitted before it misses, *lazy* delays the worker so it looks up after every earlier deploy).

## 1. What is nondeterministic in nearcore, exactly

From `runtime/runtime/src/pipelining.rs` (`submit`, `get_contract`) and `lib.rs`
(`schedule_contract_preparation`, the local/delayed/incoming loops):

1. A task is keyed by `(receipt id, action index)` and is used only by that call
   (`get_contract` takes `map.get(&key)` and checks `expected_hash`). A task of one call never
   serves another call. A worker that ran caches a compilation of bytes it found by hash, which every
   other source would give too; so one call's timing cannot change another call's code.
2. A call's outcome depends on the thread race iff (a) its code is in no witness blob and not in its
   own receipt's deploy, but an earlier in-chunk deploy (committed: deploy tracker; rolled back: the
   deploy's synchronous precompile) holds it, and (b) its task was submitted no later than the start of
   that deploy's receipt. Then there are exactly two outcomes: the worker missed (`MissingTrieValue`,
   the chunk is invalid) or the code was served.
3. `submit` resolves the receiver's contract with `RuntimeContractIdentifier::resolve`
   (`contract_code.rs:38-84`) for **every** contract kind: local hash, ETH-implicit wallet redirect to
   the global wallet hash, global code hash (no read), global account identifier (`get_ref` of
   `GlobalContractCode`, `NO_SIDE_EFFECTS`; its `value_hash`). An unresolvable identifier skips the
   action. Every resolved call makes the receipt "interesting", which staggers the later
   submissions. `block_global_contracts` is never filled from the scheduler: `handle_receipt`
   returns `false` for a distribution receipt without calling `submit` (`lib.rs:3319`).

So the global-contract call is not unschedulable at all; it was a gap in Lean's model.

## 2. The rule now (`Successor/Pipeline.lean`, `Successor/StorageExecution.lean`)

* `submitActions` resolves the receiver's contract exactly as (3) (`D3.L4.Rci.resolve` with the chain
  id in `Pipe.chain`, `Rci.resolveCodeHash` on the overlay and the revealed trie) and submits a task
  for every resolved call. Global calls no longer set `uncertain`.
* Each executed call notes its own race: `Pipe.noteRace rid idx hash served`, with
  `served = CodeSources.deployServed` (exactly the old race arm: `deployServed_iff_race`) and the
  existing per-task `Pipe.deterministic`. The call then runs with the served code.
* `StorageExecution.run` ends with `raceCheck`: a transition that would succeed after a noted race is
  `out of domain (e.code_prep_race)`; a failure is reported as is (it is the verdict on every
  schedule: the missed-code schedule rejects at the racing call, the served one fails later).
* `uncertain` remains only where the active codec cannot decode an account or a stored/delayed
  receipt (on `allFeatures` this does not occur on any population below). It makes later
  deploy-served calls racy, so it can only turn an accept into the exclusion.

Proof status: W12 §18 (O3 `PipeRel`/walk, O4 bridges, `run_eq_orig`, `run_rec_mono`,
`complete_eq_cold`, `checkD3_cases`); full default `lake build` green (425 jobs), no `sorry`, axioms
`propext`/`Classical.choice`/`Quot.sound`; `make pin-check` ok.

## 3. Schedule probe: every remaining race exclusion is a nearcore race

The pipeline-race family (4 seeds 1201–1204, same command as
[pipeline-race-fixtures](../pipeline-race-fixtures/README.md)) was regenerated with
`NEAR_SCHEDULE_PROBE_ALL=1` (new opt-in flag: the forced eager and lazy schedules on every case, not
only on deploy-served code mutants). All 3,853 cases are byte-identical (`claim.bin`, `witness.bin`)
to the committed-run copies (`probe_check.py`).

PROBE_TABLES

## 4. Before/after (checker `0b0f01ec…` → `d2e2e8b4…`, integrated harness)

BEFORE_AFTER_TABLES

## 5. Harness

`race_exclusion_conservative` (the bucket that passed W08's conservative exclusions) is removed from
`oracle/v3-d3/tools/difftest_d3.py`: a race exclusion on an in-domain `e.code_deploy_served` case is
now `domain_exclusion_where_in_domain`, a failure. The before checker is the breakage control: under
the updated harness it fails on exactly the rows this change decides (§4). `python3 -m pytest
oracle/tools`: 137 passed, 1 skipped.

HARNESS_NOTES

## Reproduce

```
B=near-arena-oracle-v3-successor   # this branch, CARGO_TARGET_DIR=... cargo build --release
NEAR_SUCCESSOR_SCENARIO=pipeline-race NEAR_SCHEDULE_PROBE_ALL=1 $B gen --domain d3 --seed S --chains 1 \
  --blocks 110 --mutate-every 0 --code-mutant-p 0.3 --ood-cap 2000 --out raceS      # S = 1201..1204
python3 tools/d3/replay_successor.py --binary CHECKER --tier T --cases-file LIST --out OUT --jobs 5 --timeout 7200
```

Run directories (per-case rows, reports): `/data/illia/nearproof-deps/g3-uncertain/rep/`; the
scripts (`lane.sh`, `summarize.py`, `probe_check.py`, `sched_tab.py`) are in `scripts/` here;
`summary.json` holds every table above with the results' sha256.
