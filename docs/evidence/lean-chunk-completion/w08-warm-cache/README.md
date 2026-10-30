# W08 warm-cache coherence and UQ-001 (cold-cache statement), 2026-10-29

Target: nearcore 2.13.4 (`44f7ae6c`), PV86, run cold as ground truth. Workplan item 7 and UQ-001 of
item 8. No signed source changed (`make pin-check`: all ok). Every nearcore verdict below comes from
nearcore's stateless validator; Lean never reads one.

| artifact | sha256 |
|---|---|
| Lean checker before (`nearspec-v3-check-successor`, main `4f07a7fdf`) | `a1627ea3…` |
| Lean checker after (this branch, final) | `fe992b40…` |
| Lean checker, intermediate draft (§4 note) | `4e209c96…` |
| generator `near-arena-oracle-v3-successor` (this branch, rustc 1.96.0) | `068c7ad6…` |

## Summary

| question | disposition |
|---|---|
| `completeCodeGlobal` rejected 178 nearcore-valid STRAT chunks (+8 on W08) | **fixed.** They were deploy-served code (an earlier in-chunk deploy holds the missing code). The complete policy now resolves code exactly as the cold validator on authenticated witness bytes (proved); a race is the shared `e.code_prep_race` exclusion. STRAT after: all 178 accept, 0 accepts of a nearcore reject, every other STRAT verdict and reason unchanged |
| the 224 `d2corpus.v2` code-less witnesses labelled with the producer's warm verdict | **(ii) fixed by re-capture**: regenerated cold with nearcore's accessed codes (`c8b2aeccd`, carried here as `7777cb831`, evidence [d2corpus-cold](../d2corpus-cold/README.md)). Not (i): their verdict is not cache-dependent once the canonical code is present. After: allFeatures 224 accept |
| generator labels race mutants `e.code_cache` | **fixed.** The generator now labels by cause, established by nearcore itself under two forced preparation schedules: `e.code_prep_race` / `e.code_deploy_served`. Lean's race exclusion is now `out of domain (e.code_prep_race)` (was the generic `e.wasm-α`) |
| UQ-001 | **disposition and test below.** No new out-of-domain reason is introduced |

## 1. What the 178 were, and the fix

A cold validator (empty compiled-contract cache) gets a function call's code from (1) the witness —
nearcore ships exactly the codes whose pre-state contract key holds the called hash
(`record_contract_call`, `runtime/runtime/src/function_call.rs:355-393`; `ContractCodeRequest`/
`Response`, `partial_witness_actor.rs:696-746, 886-985`; merged into the base state,
`partial_witness_tracker.rs:693-696`), (2) the in-chunk deploy tracker (`core/store/src/contract.rs:42-131`),
or (3) the compiled cache filled by an earlier deploy's synchronous precompile, even a rolled-back one
(`runtime/runtime/src/actions.rs:297-339`, `near-vm-runner/src/wasmtime_runner/mod.rs:699-724`). (2)
and (3) are deterministic unless the call's preparation was handed to a pipeline worker before the
deploy ran (`runtime/runtime/src/pipelining.rs:152-424`).

The pre-change complete policy demanded witness bytes for every `present`/`unknown` pre-state probe,
ignoring (2) and (3). STRAT census, pre-change binary (`completeCodeGlobal`, 18,553 cases):
886 `w.code_complete` rejects; 178 of them on chunks cold nearcore accepts —

| population | cases | label |
|---|---|---|
| d3c7–d3c10 code mutants | 169 | `e.code_cache` (old label) |
| d3c7/d3c8 honest, d3c9/d3c10 ood honest, d2corpus.v2 ood honest | 3 + 2 + 3 | none: honest witnesses with every recorded access; the rejected call ran code deployed earlier in the chunk (e.g. `d3c7/d3/07-h10167-s4`: `[CreateAccount, …, DeployContract, FunctionCall]` in one receipt, 0 accesses) and the probe of the never-written key was `unknown` |
| d3c7 header mutant `w.dup_key_last_good` | 1 | none |

New policy (`Successor/CodeResolution.lean`): witness bytes (hash-checked) → the call's own
receipt's deploy → a committed or rolled-back in-chunk deploy when the replayed schedule
(`Pipeline.Pipe.deterministic`) cannot race → `MissingTrieValue`; a racing preparation is
`out of domain (e.code_prep_race)`. This is the cold policy's resolution; the only remaining
difference is the explicit hash check of witness bytes. Proved, axioms within `propext`,
`Classical.choice`, `Quot.sound`:

* `complete_eq_cold` — on authenticated witness bytes, complete = cold on every schedule (same code
  or same error string);
* `complete_unauthenticated` — a witness blob that does not hash to the identifier is rejected;
* `complete_supplied` — authenticated supplied bytes always serve.

`CodeResolutionTests.lean`: 31 `#guard`s. The 2026-10-24 laws that described the old policy
(`complete_attempted_independent`, `complete_*_requires_witness`) were removed with it. The old
policy also served committed deploys without the race check (an accept where nearcore races); the
W12 lane found the same arm independently. Here it is the shared race exclusion.

An intermediate draft (`4e209c96…`, commit `1d1a8ab47`) additionally rejected (`w.code_complete`) a
race on a *recorded* access (pre-state key holds the called hash, which is when nearcore ships the
code). On this family it rejected 16 racing mutants, 4 of which the cold reference judge had sampled
as accepted. It was dropped (`416bc8bd2`) so the race arm is the one exclusion both policies share.

## 2. The 224 `d2corpus.v2` cases

Source evidence: the D2 generator judged with the TestEnv client's warm validator and wrote no
codes (`oracle/v3-d1/src/chaind2.rs` precompiles every D2 contract into each client cache;
`d2.rs write_case` encodes no codes). The pinned validator does not take code from the witness but
from the code response; a cold one given only the stored bytes fails with `MissingTrieValue`
(`function_call.rs:293-305`). This is not the `w.code_response_size` case: the accessed codes are a
few KB and fit any response. The generator can re-capture them cold (the chains replay
byte-identically), so the disposition is (ii): re-captured, `rejudge-d2`
(`oracle/v3-successor/src/d2cold.rs`), 224/224 byte-identical, cold no-codes reject 224, cold
with-codes ok 224; Lean allFeatures 224 accept, signed 206 accept + 18 `w.shape`. That work was
done on the unmerged branch `worktree-agent-a103b9b4017fa3668` (`c8b2aeccd`) and had already replaced
the shared corpus on disk; it is cherry-picked here (without its workplan hunk) so the committed
corpus manifest matches the disk again (`corpus_manifest.py --verify` passes). On this branch the
complete policy also accepts all 224 (none appears among the 886 pre-change `w.code_complete`
rejects).

## 3. Labels that match the cause

`oracle/v3-successor/src/cachejudge.rs` runs nearcore's validator on a compiled cache the generator
owns, so it can force the two extreme preparation schedules without a model of the scheduler:

* **Eager**: the applying thread's `put` (the deploy's precompile) first waits 400 ms, so a pipeline
  worker that was submitted before the deploy looks the code up first and misses;
* **Lazy**: a `contract_compilation` worker's `get` first waits 400 ms, so it looks the code up after
  every earlier deploy ran.

A code mutant whose missing pre-state code an earlier deploy holds is labelled `e.code_prep_race`
when nearcore's verdict differs between the two schedules, else `e.code_deploy_served`. The race
label is thus established by nearcore, not by Lean's `Pipeline` model, and it says what the cause
is (thread timing against an in-chunk deploy, not validator cache history). The successor replay
harness widens `e.code_deploy_served` (compared like any other case) on every whole-state tier and
licenses `out of domain (e.code_prep_race)` only by the race label.

## 4. New family `code-cache` (≥ 1,000 comparisons, 5 seeds)

`NEAR_SUCCESSOR_SCENARIO=code-cache` (`oracle/v3-successor/src/d3gen.rs code_cache_txs`): each
shard has a TINY pre-state contract and two code-less accounts; per round a pattern of height and
shard (no RNG draw) orders up to five transactions: committed deploy, rolled-back deploy, deploy+call
in one receipt, pre-state call, and an incoming pre-state call one chunk later. Code mutants on every
chunk with codes (`--code-mutant-p 1.0`). Each case also records nearcore's verdict with a warm
cache and with a poisoned cache (§5).

```
B=near-arena-oracle-v3-successor   # CARGO_TARGET_DIR=... cargo build --release --manifest-path oracle/v3-successor/Cargo.toml
NEAR_SUCCESSOR_SCENARIO=code-cache $B gen --domain d3 --seed S --chains 1 --blocks 80 \
  --mutate-every 0 --code-mutant-p 1.0 --ood-cap 100000 --out ccS          # S = 801..804
NEAR_SUCCESSOR_SCENARIO=code-cache $B gen --domain d3 --seed 800 --chains 1 --blocks 20 \
  --mutate-every 0 --code-mutant-p 1.0 --ood-cap 100000 --out smoke800
python3 tools/d3/replay_successor.py --tier allFeatures --cases-file LIST --out OUT --jobs 4
python3 tools/d3/check_cache_independence.py --lean OUT/results.jsonl --out uq001.json
python3 tools/d3/select_code_cache_fixtures.py --run cc801 ... --out cases --per-class 1
```

Runs 801–804 were stopped after 758–897 cases each (host oversubscribed; every written case is
complete). 3,934 cases: 439 honest (all cold-accepted), 3,495 code mutants.

Generator classification (nearcore only):

| class | cases | cold nearcore | eager / lazy |
|---|---|---|---|
| honest | 439 | ok 439 | — |
| code mutant, no deploy serves the missing code (or extra blobs) | 2,586 | ok 1,415 / reject 1,171 | — |
| `e.code_deploy_served` | 821 | ok 653 / reject 168 | equal on all 821 |
| `e.code_prep_race` | 88 | ok 18 / reject 70 | eager reject, lazy ok on all 88 |

Lean (final checker `fe992b40…`), verdicts against cold nearcore:

| tier | accept | reject | out of domain | Lean accept of a nearcore reject | Lean reject of a nearcore accept |
|---|---|---|---|---|---|
| allFeatures | 2,507 | 1,312 | 115 | **0** | **0** |
| completeCodeGlobal | 2,506 | 1,312 | 116 | **0** | **0** |

* allFeatures out of domain: 88 = exactly the 88 nearcore races (`e.code_prep_race`, asserted);
  27 more `e.code_prep_race` exclusions on `e.code_deploy_served` cases, all `code.none` mutants
  that drop both TINY and `d3rich`: nearcore's *failure point* depends on the schedule (eager:
  `MissingTrieValue` on TINY, lazy: on `d3rich` later) but its verdict (reject) does not. Lean
  excludes at the first racing call, so these are a conservative completeness gap (a decidable
  reject reported as excluded), not a disagreement. The remaining 15 rows are honest `ood` chunks
  Lean decides and agrees on (`verdict_agree_outside_domain`).
* completeCodeGlobal vs allFeatures, per case: identical verdict and reason on 3,933; the one
  difference is an honest `ood` chunk that calls `ecrecover`, which `completeCodeGlobal` (no curve
  hosts) excludes. (The intermediate draft rejected 16 racing mutants, 4 of them sampled ok by cold
  nearcore; see §1.)
* Breakage control (Lean): the pre-change binary on the same family. `completeCodeGlobal`: 1,804
  accept / 2,129 reject / 1 excluded, **720 rejects of nearcore-accepted chunks** (`w.code_complete`,
  every one deploy-served), so this family detects the old policy. `allFeatures`: the same verdicts as
  after, but its 88 race exclusions were `domain_exclusion_unasserted` (reason `e.wasm-α`, which no
  generator label licenses); after the relabelling they are asserted.
* Breakage control (harness): `check_code_witness_policy.py` with the pre-change binary fails on its
  first deploy-served pair (`00-h10066-s0-code.drop.0`); with the new binary it passes (5 pairs × 3 ×
  2 runs; raw cold incomplete verdicts 3 accept / 2 reject reproduced).

`cases/` keeps 24 cases (one per class per run of 801–804; `index.json` has sources and hashes).

## 5. UQ-001 disposition: the cold-cache statement

**What the relation claims about the compiled-code cache.** `Rel` (every successor tier) is a
function of the claim and witness bytes only; no compiled artifact, cache-membership bit or
preparation result is an input. Its intended reading is nearcore 2.13.4's stateless validator
starting the chunk with an **empty** compiled-contract cache, given the witness as distributed
(state witness plus the `ContractCodeResponse` codes). In-chunk effects on that cache (the
deploy tracker and deploys' precompiles) are modelled; the preparation schedule is replayed
(`Pipeline`) and a schedule-dependent verdict is the named exclusion `e.code_prep_race`.

**Why the verdict is cache-independent inside the domain.** Let a *coherent* cache be one whose
every entry under key `(h, config, vm)` is the compilation result (module or compile error, with
`wasm_bytes`) of bytes whose hash is `h` (`near-vm-runner/src/cache.rs:108-120`,
`wasmtime_runner/mod.rs:699-760`). A cache hit then yields exactly what compiling the bytes would,
including the byte length charged for loading, so a call's result is the same with or without the
hit. The only way a cache changes a verdict is by supplying code that no other source holds:
cold validator `MissingTrieValue` (reject) versus a warm hit (execute). Hence, for every coherent
starting cache `C`:

1. Lean accept ⇒ nearcore accepts under `C` (every executed call had its code in the witness or an
   in-chunk deploy without a race; a hit can only reproduce it);
2. Lean reject for a reason other than missing contract code ⇒ nearcore rejects under `C` (every
   call before the failure had its code, the run is identical up to it);
3. Lean reject `MissingTrieValue (contract code)` (the same string in both policies) is the one
   cache-dependent class: cold rejects, a cache holding the code accepts. The statement assigns
   it to the cold cache. It only arises for a witness without a code nearcore distributes (a lost or
   over-cap code response, i.e. the already-approved `w.code_response_size` situation, or a code
   mutant); the canonical cold witness carries every recorded access.

No new out-of-domain reason is needed: (3) is a reject under the cold statement, never an accept.
Incoherent ("poisoned") caches are outside the statement: release nearcore checks code/hash
coherence only with a debug assertion (`ContractCode::new`), so a malformed historical global
distribution could poison a validator's cache; current malformed distributions are excluded
(`w.shape: global_code_identity`), historical cache contents are an environment assumption (item 12).

**The test that would fail if it were not.** `tools/d3/check_cache_independence.py` over the
`code-cache` family: for every case nearcore is judged three times on the same bytes — cold (the
reference), warm (all registry contracts precompiled, coherent), poisoned (each contract compiled
under the next one's hash). The script fails if any Lean accept or non-missing-code reject has
warm ≠ cold, or if the poisoned control never differs (which would mean the probe cannot see a
cache at all).

| Lean class (allFeatures) | cases | cold | warm | poisoned |
|---|---|---|---|---|
| accept | 2,507 | ok 2,507 | ok 2,507 | err 2,474, ok 33 |
| reject, missing contract code | 1,312 | err 1,312 | **ok 1,312** | err 1,312 |
| out of domain | 115 | ok 18, err 97 | ok 115 | err 115 |

Result: 0 violations on both tiers (completeCodeGlobal: 2,473 poisoned differences, 1,312 warm
differences on its missing-code class). The 1,312 warm accepts on the missing-code class
are the positive control: the probe does see a warm cache, and it changes exactly the class the
statement assigns to the cold cache. Of the 33 poisoned-equal accepts (all honest), 23 execute no
contract; in the other 10 the substituted compilation happens to give the same outcome.
The code-mutant family has no Lean reject other than missing code, so class 2 is tested on a sixth
run, `full805` (`--seed 805 --blocks 12 --mutate-every 3 --code-mutant-p 0.3 --drop-cap 6`, the
full mutant set: headers, trusted facts, witness nodes, code blobs): 796 cases, allFeatures 252
accept / 532 reject / 12 out of domain, 0 accept or reject disagreements with cold nearcore
(`completeCodeGlobal` identical in verdict and reason). UQ-001 check, 0 violations:

| Lean class (allFeatures), full805 | cases | cold | warm | poisoned |
|---|---|---|---|---|
| accept | 251 | ok | ok | err 247, ok 4 |
| reject, other reason | **342** | err | **err 342** | err |
| reject, missing contract code | 51 | err | ok 51 | err |
| out of domain | 12 | err | ok | err |
| not probed (claim-discipline, derived and transaction-validity mutants) | 140 | | | |

(The 252nd accept is a mutant judged with substituted transaction-validity flags, which the probe
does not replay.)

## 6. Before/after verdict tables

Pre-change checker `a1627ea3…` → final `fe992b40…`. "Lean accept of a nearcore reject": 0 in every row.

**Corpus STRAT (18,553 cases of d1run, d2corpus.v2, d3c7–d3c10), `completeCodeGlobal`:**

| before → after | cases | nearcore (cold label) |
|---|---|---|
| accept → accept | 10,130 | ok |
| reject `w.code_complete` → **accept** | **178** | ok |
| reject `w.code_complete` → reject `MissingTrieValue (contract code)` | 700 | reject |
| reject `w.code_complete` → reject, other reason (`finalize`/post state root) | 4 | reject |
| reject `w.code_complete` → out of domain `e.code_prep_race` | 4 | reject |
| reject or out of domain, same verdict and same reason string | 7,537 | as before |
| totals | before 10,130 / 8,162 / 261, after 10,308 / 7,980 / 265 (accept / reject / ood) | |

Only the 886 pre-change `w.code_complete` rows move; every other row is byte-identical in verdict and
reason. On the same 886 rows `completeCodeGlobal` and `allFeatures` now agree in verdict and reason.

**W08 pipeline population (103 code mutants):**

| tier | before | after | nearcore |
|---|---|---|---|
| completeCodeGlobal | reject 103 (`w.code_complete`) | accept 8, out of domain 95 (`e.code_prep_race`) | ok 8, reject 95 |
| allFeatures | accept 8, out of domain 95 (`e.wasm-α`) | accept 8, out of domain 95 (`e.code_prep_race`) | ok 8, reject 95 |

**Fixtures:** `code-cache` family before/after in §4. `tools/d3/code-policy-fixtures` (5 pairs): before
fails (rejects a deploy-served nearcore accept), after passes. `smoke_successor.py`: all 13 tiers
pass their verdict comparisons, `completeCodeGlobal` now on all 7 smoke cases (before: the
`e.code_cache` case was set aside). That run used the intermediate draft binary and then stopped on
its fixed 120 s subprocess timeout in the unrelated V2 parent-map section under host load ~170; it
was not rerun with the final binary.

**Gap census (3,138) and full corpus (235,716):** not rerun (host capped at 4 checker processes). By
construction the cold policy (`allFeatures` and every other tier but `completeCodeGlobal`) changed
only the race reason string, and on STRAT the complete policy changed only the 886 rows above. The
224 `d2corpus.v2` re-capture moves the full-corpus headline as recorded in
[d2corpus-cold](../d2corpus-cold/README.md) (`allFeatures`: 235,621 agree, 95 out of domain,
0 disagree).

## 7. What is left open

* Lean's race exclusion is wider than nearcore's verdict races: 27 `code.none` mutants (§4) where the
  failure point races but the verdict does not. Deciding them needs the checker to continue past a
  racing call to the next certain failure; not done.
* The eager/lazy probe establishes a race by observing both extreme schedules with 400 ms delays; it
  is evidence, not a proof that no third schedule exists. On this family the two schedules agreed with
  Lean's `Pipeline` model on every verdict race (88/88 excluded by Lean).
* The full 13-tier census was not rerun (host oversubscribed). `allFeatures`/`globalActions` change
  only the race reason string by construction (`resolveColdCode` changed nothing else).
* `TierMono.lean`'s O7 note and the W00 owner-map UQ-001 row are left to the integrator (lane 5 owns
  O7; `complete_eq_cold` is the resolution-level lemma a verdict-level `globalActions ≡
  completeCodeGlobal` result needs, given that production stores are hash-indexed).
* Merge note: the W12 lane changes the same function (`resolveCompleteCode`'s untimely-deploy arm →
  race exclusion). This branch rewrites the whole function and its race arm is exactly that
  exclusion, so the conflict resolves by taking this version.
