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
| checker before (main with the `current_contract_code`, gas-key and fuel-proof changes) | `461a7cd9718a7af496586ef8f491f2af0baef0e74c4998f7bcd74f8c0f1cef55` |
| checker after (this branch, merged with that main) | `644495ff5e04801f6ba206abb5d3f608bcfe0f10499767a8203464d4b10a9ae3` |
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
  receipt. It makes later deploy-served calls racy, so it can only turn an accept into the
  exclusion; on every probed population below no race exclusion remains that nearcore's schedules do
  not confirm, so it caused none there.

Proof status: W12 §18 (O3 `PipeRel`/walk, O4 bridges, `run_eq_orig`, `run_rec_mono`,
`complete_eq_cold`, `checkD3_cases`); full default `lake build` green on the merged tree (437 jobs),
no `sorry`, axioms `propext`/`Classical.choice`/`Quot.sound`; `make pin-check` ok;
`python3 -m pytest oracle/tools`: 142 passed, 1 skipped.

## 3. Schedule probe: every remaining race exclusion is a nearcore race

The pipeline-race family (4 seeds 1201–1204, same command as
[pipeline-race-fixtures](../pipeline-race-fixtures/README.md)) was regenerated with
`NEAR_SCHEDULE_PROBE_ALL=1` (new opt-in flag: the forced eager and lazy schedules on every case, not
only on deploy-served code mutants). All 3,853 cases are byte-identical (`claim.bin`, `witness.bin`)
to the committed-run copies (`probe_check.py`).

`probe_check.py` (R1: every race exclusion after has eager ≠ lazy; R2: every newly decided case
has eager = lazy = cold and Lean's verdict equals it; R3: no accept of a case any schedule rejects):
**0 / 0 / 0 violations**, 0 cases without a probe.

| Lean after (`allFeatures`) | nearcore schedules | cold | cases |
|---|---|---|---|
| accept | eager ok, lazy ok | ok | 2,588 |
| reject | eager err, lazy err | err | 1,254 |
| `e.code_prep_race` | **eager err, lazy ok** | err | 10 |
| `e.code_prep_race` | **eager err, lazy ok** | ok | 1 |

The 189 cases this change decides are all schedule-independent (148 accept: ok/ok; 41 reject:
err/err). Before, 200 cases were excluded: the 189 plus the same 11. The 11 are code mutants
(`code.drop`/`flip`/`truncate`) of 4 chunks; the regenerated oracle labels them `e.code_prep_race`
(the committed run, from the pre-W08 generator, labels them `e.code_cache`).

Other populations with nearcore's schedules (`sched_tab.py`, code mutants that a deploy serves):

| population | Lean race exclusions after | of which eager ≠ lazy | decided cases with eager ≠ lazy |
|---|---|---|---|
| W08 `code-cache` family (cc801–804, full805; 4,730) | 97 | 97 | 0 |
| eth-wallet (10,650) | 5 | 5 | 0 |
| committed fixtures (1,364) | 4 | 4 | 0 |

So on every population the remaining race exclusions are exactly nearcore's verdict races, and no
case where nearcore's verdict races is decided.

## 4. Before/after (checker `0b0f01ec…` → `d2e2e8b4…`, integrated harness)

The baseline moved twice while this ran (`ee00c918…` → `0b0f01ec…` → `461a7cd9…`); the G3 moves
were identical against all three. The numbers below are against the final baseline `461a7cd9…`
(main with the fuel proof) except where marked. `unsound` = Lean
accepts of a nearcore reject after: **0 in every row**.

| population | tier | cases | before (accept / reject / race / other ood) | after | moves | harness before → after |
|---|---|---|---|---|---|---|
| committed fixtures (incl. cross-family, pipeline-race, W08) | allFeatures | 1,364 | 819 / 527 / 18 / 0 | 827 / 533 / 4 / 0 | race → accept 8 (nearcore ok), race → reject 6 (nearcore err) | fail (2) → pass |
| gap census | allFeatures | 3,138 | 3,138 / 0 / 0 / 0 | same | 0 | pass → pass |
| pipeline-race family (4 seeds) | allFeatures | 3,853 | 2,440 / 1,213 / 200 / 0 | 2,588 / 1,254 / 11 / 0 | race → accept 148 (ok), race → reject 41 (err) | fail (188) → pass |
| W08 `code-cache` family (all seeds) | allFeatures | 4,730 | 2,759 / 1,844 / 127 / 0 | 2,759 / 1,874 / 97 / 0 | race → reject 30 (err) | fail (30) → pass |
| eth-wallet | allFeatures | 10,650 | 2,816 / 7,827 / 7 / 0 | 2,816 / 7,829 / 5 / 0 | race → reject 2 (err) | fail (2) → pass |
| mainnet shard 13 | allFeatures | 1,223 | SHARD13_AF | | | (no `meta.json`) |
| committed fixtures | signed | 1,364 | 434 / 421 / 0 / 509 | same | 0 | pass → pass ¹ |
| gap census | signed | 3,138 | 735 / 0 / 0 / 2,403 | same | 0 | pass → pass ¹ |
| pipeline-race family | signed | 3,853 | 2,039 / 1,103 / 0 / 711 | same | 0 | fail (7) → fail (7) ¹ ² |
| W08 family | signed | 4,730 | 1,778 / 1,666 / 0 / 1,286 | same | 0 | pass → pass ¹ |
| eth-wallet | signed | 10,650 | 1,721 / 5,971 / 0 / 2,958 | same | 0 | pass → pass ¹ |
| mainnet shard 13 | signed | 1,223 | 944 / 0 / 0 / 279 | same | 0 | ¹ |
| full corpus | allFeatures, signed | 235,716 | **pending** (§6) | | | |

¹ Against the intermediate baseline `0b0f01ec…` (same G3 change, built before the fuel-proof
merge); the final-baseline signed runs are in progress (§6). The signed tier has no global-contract
calls in domain and its race arm is the legacy cold-cache rule, so G3 moves nothing there.
² Pre-existing and identical before and after: 2 honest chunks with a distribution receipt and 5
code mutants on a global-contract identifier that the committed (pre-W08) oracle does not label
`w.shape`; the signed checker excludes them as `w.shape`. Not a G3 effect.

Every moved row was a race exclusion; nothing else moved (verdict and reason byte-identical on every
other row).

## 5. Harness

`race_exclusion_conservative` (the bucket that passed W08's conservative exclusions) is removed from
`oracle/v3-d3/tools/difftest_d3.py`: a race exclusion on an in-domain `e.code_deploy_served` case is
now `domain_exclusion_where_in_domain`, a failure.

* **Breakage control.** The before checker under the updated harness fails on exactly the rows this
  change decides: fixtures 2 (cc802/cc803 `code.none`, `e.code_deploy_served`), W08 30, eth-wallet 2
  (`domain_exclusion_where_in_domain`), pipeline-race 188 (no longer independently licensed). The
  after checker passes all of them.
* **No independent licence for the race any more** (`oracle/tools/independent_domain.py`): the
  successor tiers' `TIER_EXCLUSIONS` is empty. It licensed race exclusions by the decoded structural
  precondition (a call served by an earlier in-chunk deploy), which only covered what the chunk-wide
  `uncertain` flag produced; after the change every remaining race row is licensed by the oracle's
  race label (`domain_exclusion_asserted`): fixtures 4, pipeline-race 11, W08 97, eth-wallet 5.

## 6. Pending: the full corpus

The full-corpus runs (235,716 cases, both tiers, before `461a7cd9…` and after `644495ff…`) are running
detached (`scripts/lane.sh`, 5 jobs each; host shared) into `/data/illia/nearproof-deps/g3-uncertain/rep/`,
after the signed small populations. When `rep/status` lists `base ALL` and `after ALL`:

```
cd /data/illia/nearproof-deps/g3-uncertain && python3 summarize.py summary.json   # fills every row
python3 tools/d3/replay_successor.py --rescore rep/<run> --out rep-rescore/<run>   # current harness
```

Expected from construction (only deploy-served executed calls can move): the 95 `allFeatures`
corpus race exclusions (pre-W08 `code.*` mutants, nearcore rejects all 95, W08 §6) either stay
(nearcore race) or become rejects; no signed row moves. Earlier corpus runs against `ee00c918…` /
`0b0f01ec…` were stopped when main moved.

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
