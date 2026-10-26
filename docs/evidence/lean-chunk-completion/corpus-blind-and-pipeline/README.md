# Corpus-wide blind replay, fixture sets and the preparation-pipeline fix (2026-10-26)

All numbers are from one checker, `nearspec-v3-check-successor` built from `5c60547b3`
(sha256 prefix `29bf5217f43a23d3`, see `checker.txt`), tier `allFeatures`.

## 1. The 8 `MissingTrieValue` disagreements (W08), and 89 unsound accepts

The cold validator can execute a pre-state contract whose code is not in the witness when a deploy
of the same code ran earlier in the chunk: `action_deploy_contract` precompiles every deploy into
the compiled-contract cache, including one that is rolled back (`runtime/src/actions.rs:297-339`),
and committed deploys stay in the deploy tracker (`core/store/src/contract.rs:104-128`). Whether
the call sees either depends on *when its preparation started*: `ReceiptPreparationPipeline::submit`
hands function calls to a worker thread that looks the code up immediately
(`runtime/src/pipelining.rs:152-424`), staggered one "interesting" receipt ahead of the main
thread (`schedule_contract_preparation`, `runtime/src/lib.rs:3256-3324`). A worker that runs before
the deploy finds no code and the validator fails with `MissingTrieValue`
(`runtime/src/function_call.rs:293-305`).

`spec/lean/v3/NearSpecV3/Successor/Pipeline.lean` replays that schedule over the same partial
state the validator has. A deploy-served call is decided when its task was never submitted or was
submitted after a deploy of the code finished; a task submitted earlier is a thread race and the
chunk is out of domain. The earlier rule keyed on the pre-state code key, which the validator never
reads and the witness never reveals, so every cache-served call fell to `MissingTrieValue`.

`code-mutant-pipeline-diff.json`: all 27,270 code mutants of d3c7-d3c10, before (`c27a6fb67`) and
after:

| change | cases | nearcore (cold) |
|---|---|---|
| reject → accept | 8 | accept (the 8 disagreements) |
| accept → out of domain | 89 | reject: **previously accepted invalid chunks** |
| reject → out of domain | 6 | reject |

After: 12,915 accept/accept, 14,260 reject/reject, 95 out of domain (all nearcore-rejected),
0 disagreements. `storageResolution` gives the identical table.

## 2. Corpus-wide blind replay

`tools/mainnet-replay/blind_corpus.py` over every non-mutant case of d1run, d2corpus.v2 and
d3c7-d3c10 (39,942), expected values from the nearcore-produced header the witness endorses, every
produced value removed from the inputs (`corpus-blind-report.json`, `corpus-blind-results.jsonl.gz`):

| category | cases |
|---|---|
| match (all 11 graded fields) | 39,452 |
| output mismatch / leak | 0 |
| genesis main transition (outputs are the stored `genesis_chunk_extra`, a claim input) | 266 |
| Lean `MissingTrieValue (contract code)` | 224 |

The 224 are all `d2corpus.v2/ood`: that corpus predates code in witnesses and its `nearcore: ok`
is the producer's verdict, not a cold-validator replay (no `verdict_source`); with no code in the
witness the cold verdict is `MissingTrieValue`. Matched cases exercising each previously-unexercised
field with a non-trivial value: proposals 1,152; bandwidth requests 528; delayed-receipt gas 5,783;
buffered-receipt gas 8,463; receipt bytes 13,101; implicit transitions 3,978.

## 3. Fixture sets on the same checker (`fixture-sets.json`)

| set | verdict vs nearcore | blind |
|---|---|---|
| curve-host-fixtures | 111/111 | 93 match (18 nearcore-rejected) |
| key-family-fixtures | 76/79, 3 out of domain (ML-DSA tx, ML-DSA receipt key, secp key with ED25519 signature) | 76 match |
| yield-fixtures | 202/202 | 74 match |
| storage-limit-fixtures | 88/88 | 64 match |
| resharding-fixtures | 38/38 | 19 match, 1 not blindable* |
| global-cache-fixtures | 28/28 | 28 match |
| global-promise-fixtures | 3/3 | 3 match |

\* In one split case the sibling child's chunk header in the segment carries the same outcome root,
so that value is a legitimate input and cannot be removed.

Mainnet shard 13 on this checker: blind 1,223/1,223, verdict 1,223/1,223 (`replay-results-*-5c60547b3`).
