# `d2corpus.v2`: the 224 warm-labelled witnesses, regenerated cold with code (2026-10-27)

The corpus headline had one caveat: 224 `d2corpus.v2/ood` cases (206 on `--tier signed`) were
Lean rejects (`invalid: MissingTrieValue (contract code)`) of witnesses labelled `nearcore: ok`.
Those witnesses carry no code, and their label is the producer's warm verdict. This change
regenerates all 224 with nearcore's cold validator and the code they need, and replaces them in
place in the pinned corpus. After the change the corpus has no Lean reject of a nearcore-accepted
chunk on either tier.

Target: nearcore 2.13.4 (`44f7ae6c`), PV86. Generator: `near-arena-oracle-v3-successor`
`rejudge-d2` (`01206a29…`, `oracle/v3-successor/src/d2cold.rs`). Lean checker:
`nearspec-v3-check-successor` `a1627ea3…` (main `7c94cbd3d`).

## Why the label was warm

The D2 generator (`oracle/v3-d1`, `gen --domain d2`) judged every honest witness with the TestEnv
client's own validator (`chaind2.rs`, `nearcore_judge(client, &wb, &[], …)`). It writes
`witness.bin` without code blobs (`d2.rs` `write_case`: `encode_witness(witness, &[])`), and it
precompiles every D2 contract into each client's compiled-contract cache before the first block
(`chaind2.rs` `setup_d2`). A chunk that calls a pre-state contract (the `s{k}ct` program contract,
or a `small_wasm` deployed in an earlier chunk) is therefore `ok` for that client. The pinned
validator does not ship contract code in the witness: it fetches the accessed code it lacks with a
`ContractCodeRequest` and merges the response into the base state
(`partial_witness_tracker.rs:693-696`). A cold validator given only the stored bytes fails the call
with `MissingTrieValue` (`runtime/runtime/src/function_call.rs:293-305`). The D3 generators already
judge cold with the needed codes appended (`oracle/v3-d3/src/d3judge.rs`); the D2 generator
predates that.

## What `rejudge-d2` does

It replays the D2 chain of each case (same seed, parameters and code as `chain_params_d2` and
`run_chain_d2`, so the RNG stream is identical; the replay's own corpus output goes to a scratch
directory and is discarded). For each selected case it:

1. checks that the regenerated `ChunkStateWitness` and claim are **byte-identical** to the corpus
   files;
2. takes nearcore's contract accesses for the chunk (`contract_updates.contract_accesses` of the
   distribution request), with the code bytes from the D2 registry (`program_wasm`, `small_wasm`);
3. judges the witness with the cold validator (`ColdJudge`, empty compiled-contract cache) once
   without codes and once with them;
4. writes `claim.bin`, `witness.bin` (with the codes) and `meta.json`. The meta keeps the corpus
   fields, sets `nearcore` to the cold verdict with codes and `verdict_source:
   "nearcore(cold)"`, and records `nearcore_warm_no_codes`, `nearcore_cold_no_codes`,
   `contract_accesses`, `codes` and `regenerated_from`.

```
G=near-arena-oracle-v3-successor
# LIST: one "ood/<case>" per line (the 224 cases)
for i in 0..13: $G rejudge-d2 --corpus $CORPORA/d2corpus.v2 --cases LIST --chain $i \
    --blocks {200, or 270 for chains 2, 7, 12} --out OUT --scratch SCRATCH
```

Each chain ran in 5–118 s (it stops after its last selected case).

## Results

`rejudge-summary.json` has one row per case.

| check | cases |
|---|---|
| regenerated witness and claim byte-identical to the corpus | 224 / 224 |
| accessed code found in the D2 registry | 224 / 224 |
| warm validator, no codes (the corpus label) | `ok` 224 |
| **cold validator, no codes** (the bytes the corpus held) | `MissingTrieValue` 224 |
| **cold validator, with the accessed codes** | `ok` 224 |

Lean (`replay_successor.py`, files `lean-{warm,cold}-{signed,allFeatures}.jsonl`):

| input | `allFeatures` | `signed` | cold nearcore |
|---|---|---|---|
| corpus bytes before (no code; label `ok`, warm) | reject 224 (`MissingTrieValue (contract code)`) | reject 206, out of domain 18 (`w.shape`: 10 ML-DSA keys, 8 non-ED25519 tx keys) | reject 224 (no codes) |
| regenerated cold (with code; label `ok`, cold) | **accept 224** | **accept 206**, out of domain 18 (same `w.shape`) | ok 224 |

The before row is not a Lean bug: against the cold verdict of the same bytes, Lean agreed on all
224. It was the label that was wrong. The as-stored witnesses also serve as the negative half of
this population: 224 code-less witnesses that cold nearcore rejects and Lean rejects with the same
reason.

## The corpus change

The 224 case directories in `$CORPORA/d2corpus.v2/ood` were replaced in place by the cold ones
(`claim.bin` unchanged, `witness.bin` with code, `meta.json` relabelled). The warm originals are
kept in `$CORPORA/d2corpus.v2-warm-originals/ood`, and the per-chain `rejudge-*.json` in
`$CORPORA/d2corpus.v2-cold/rejudge`. No other case of any corpus changed. The committed content
manifest (`docs/evidence/lean-chunk-L7/corpus-manifest.json`) is updated for the one family that
moved, `d2corpus.v2/ood` (390 cases; bytes 10,095,608 → 10,449,976; sha256 `edd831ad…` →
`b252f3fa…`). `corpus_manifest.py --verify` before the update reported exactly that family and
nothing else.

## Corpus headline, before and after

Only the 224 inputs changed, and every other case's bytes are identical, so the full-corpus
verdicts move by exactly these 224 rows (the replay is deterministic per input).

| tier | before | after |
|---|---|---|
| `allFeatures` (235,716) | 235,397 agree, 95 out of domain, 224 reject of a warm-labelled `ok` | **235,621 agree, 95 out of domain, 0 disagree** |
| `signed` (235,716) | 112,036 agree, 120,716 agree outside its domain, 2,758 out of domain, 206 reject of a warm-labelled `ok` | 112,036 agree, **120,922** agree outside its domain, 2,758 out of domain, **0 reject of a nearcore-accepted chunk** |

No Lean accept of a nearcore reject, before or after.
