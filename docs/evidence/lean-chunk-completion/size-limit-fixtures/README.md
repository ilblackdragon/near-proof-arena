# W02 size-limit fixtures: whole chunks at the 48 MiB and 64 MiB boundaries (workplan item 4)

The size-limits lane (`../size-limits/`) implemented nearcore's 48 MiB encoded-witness cap and the
64 MiB contract-code-response cap, but tested them on zstd frames and unit tests only. This
directory adds whole-chunk fixtures at both boundaries, judged by pinned nearcore 2.13.4
(`44f7ae6c`), and runs `nearspec-v3-check-successor --tier allFeatures` (checker `584976cf…`, see
`../eval-budget/`) on them. No Lean definition changes here.

## 0. A trap: the generator's nearcore has `test_features`

`oracle/v3-successor` links nearcore through `integration-tests`, which enables `test_features`.
Under that feature `MAX_COMPRESSED_STATE_WITNESS_SIZE`, `MAX_UNCOMPRESSED_STATE_WITNESS_SIZE` and
`MAX_UNCOMPRESSED_CONTRACT_CODE_RESPONSE_SIZE` are all **512 MiB**
(`partial_witness.rs:18-19`, `state_witness.rs:19-20`, `contract_distribution.rs:372-373`). So the
generator's own validator cannot judge either boundary. `ncref/` links only `near-primitives`
from the same pinned checkout **without** `test_features` (`ncref caps`:
`{"MAX_COMPRESSED_STATE_WITNESS_SIZE":50331648,"MAX_UNCOMPRESSED_STATE_WITNESS_SIZE":67108864,
"MAX_UNCOMPRESSED_CONTRACT_CODE_RESPONSE_SIZE":67108864}`) and runs nearcore's own codecs and
checks. The cold validator verdict of the chunk itself still comes from the generator's judge.

## 1. 64 MiB contract-code response (`code-response` scenario, seed 2029)

`NEAR_SUCCESSOR_SCENARIO=code-response gen --domain d3 --seed 2029 --chains 1 --blocks 30
--p-missing 0 --mutate-every 0 --code-mutant-p 0 --ood-cap 100000`. Genesis holds 18 contracts on
one shard: 16 of 4,194,000 B and two small ones of 4,792 B and 4,793 B
(`scenarios::sized_wasm`: `(memory 64) (func (export "run")) (data …)`, exact byte sizes). One
chunk calls 16 + the 4,792 B one, one chunk 16 + the 4,793 B one, and a control chunk 8 + the
4,792 B one; every call is its own transaction with signer = receiver, so all of them execute in
the chunk that includes them (`manifest-cr2029.json`: 17 / 17 / 9 `run` calls, each
`SuccessValue`, 0 problems). The run has 120 honest chunks, all accepted by the cold validator.

The codes a cold validator must fetch are those calls' pre-state codes (none is in the witness),
sent as one `ContractCodeResponse` whose borsh `Vec<CodeBytes>` is `4 + Σ (4 + |code|)`.
nearcore, per chunk (`code-response-nearcore.json`):

| chunk | borsh `Vec<CodeBytes>` | `ContractCodeResponse` V2 → `decompress_contracts` (production build) | cold, codes appended | cold, no codes | warm, no codes |
|---|---|---|---|---|---|
| `at64` (`ood/00-h10006-s3`) | **67,108,864** | ok | ok | reject `MissingTrieValue` | ok |
| `over64` (`ood/00-h10012-s3`) | **67,108,865** | **error: Decompressed data exceeded limit of 67.1 MB** | ok | reject `MissingTrieValue` | ok |
| `under64` (`ood/00-h10018-s3`) | 33,556,832 | ok | ok | reject | ok |

So at the cap a cold validator decodes the response and accepts. One byte over, the response is
dropped, the validator proceeds without the codes after `ACCESSED_CONTRACTS_REQUEST_TIMEOUT`
(`partial_witness_tracker.rs:45-48`) and rejects with `MissingTrieValue` — unless the codes are in
its compiled cache, in which case it accepts: the verdict depends on the validator's cache, the
`w.code_response_size` out-of-domain reason.

Lean (`code-response-lean.json`, `time_cases.py`):

| chunk | Lean `allFeatures` | CPU | max RSS |
|---|---|---|---|
| `at64` | **accept** | 100.5 s | 2,245 MiB |
| `over64` | **out of domain** (`w.code_response_size`: cold-fetched contract code exceeds MAX_UNCOMPRESSED_CONTRACT_CODE_RESPONSE_SIZE) | 1.8 s | 2,179 MiB |
| `under64` | accept | 49.7 s | 1,219 MiB |

Agreement at the boundary, and no accept where a cold validator can reject. The case directories
are 64 MiB each and are not committed; `code-response-sha256.txt` pins their bytes, and the
command above regenerates them. **Open:** one seed only (the three boundary chunks), and no
mutants of these chunks (a mutant would copy 64 MiB of code per case); the negative side of the
family is the `over64` chunk.

## 2. 48 MiB compressed witness

**Why padded encodings.** An honest producer encodes the witness with zstd level 1, 4 workers.
To reach 48 MiB encoded, a generated chunk would need about 48 MiB of incompressible witness
content. nearcore's producer limits keep a witness well below that: storage proof
`main_storage_proof_size_soft_limit` 4,000,000 B (plus one item over the soft limit,
`per_receipt_storage_proof_size_limit` 4,000,000 B), `combined_transactions_size_limit`
4,194,304 B for the applied and for the new transactions, `new_transactions_validation_state
_size_soft_limit` 572,864 B, and incoming receipts bounded per sending shard by
`outgoing_receipts_big_size_limit` 4,718,592 B (`parameters.snap:11-16`). Only incoming receipts
from many shards over several heights with missing chunks can approach 48 MiB, which this
4-shard generator cannot produce (the gate-b lane reached 9.46 MB with large transactions). So a
"natural" 48 MiB witness is not generated here.

What a validator checks, though, is the length of the *encoding*: `validate_partial_encoded_state
_witness` rejects `encoded_length > MAX_COMPRESSED_STATE_WITNESS_SIZE` first
(`validate.rs:82-88`), and `EncodedChunkStateWitness::decode` reads every zstd frame of the
stream (`CompressedData::decode_with_limit`, `zstd::stream::Decoder`, then borsh's end-of-input
check), skipping skippable frames. A producer may therefore distribute any encoding of the
witness. Each fixture here is a real cold-judged chunk whose witness was encoded with nearcore's
own producer codec (`ncref witness`: `EncodedChunkStateWitness::encode`) and padded with one zstd
skippable frame to exactly 48 MiB − 1, 48 MiB and 48 MiB + 1 bytes. For each padded encoding
`ncref` records the size check and the result of nearcore's `decode` (re-serialized and compared
byte for byte with the judged witness). nearcore's verdict is: reject when the size check fires;
otherwise, when the decode is identical, the case's cold verdict. `tools/d3/size_limit_fixtures.py`
regenerates the padded bytes, checks their sha256 against `ncref`'s, writes a
`near-arena-cwitness-v3` case, runs Lean and deletes the 48 MiB file.

**Population.** 4 seeds (corpora `d3c7`–`d3c10`), 150 honest chunks and 150 mutants per seed
(`random.Random(2026+i)`), 1,200 cases (`witness48-cases.txt`). 32 are skipped because the
mutated witness bytes are not nearcore's canonical encoding of a `ChunkStateWitness` (byte-level
witness mutants: `w.trailing_byte`, `w.unsorted_keys`, `w.extra_proof`, `w.dup_key_*`): a producer
cannot emit them through the codec, so there is no nearcore verdict for their encoding.

| variant | encoded length | comparisons | agree | Lean accepts a nearcore reject |
|---|---|---|---|---|
| plain (producer encoding) | 0.4–200 kB | 1,168 of 1,200 cases | **1,168** | 0 |
| under48 | 50,331,647 | 433 | **433** | 0 |
| at48 | 50,331,648 | 433 | **433** | 0 |
| over48 | 50,331,649 | 442 | **442** (all reject) | 0 |

The padded variants were run on 446 of the 1,200 cases (`witness48-padded.json.gz`: 146 from
`d3c7`, 100 each from `d3c8`–`d3c10`, about half honest and half mutants), 1,308 padded comparisons
in all, plus the 1,168 plain ones. A mutant's expected verdict is its corpus expectation: the cold
validator's, or `claim-v3 discipline` for claim mutants nearcore cannot judge (as in the corpus). The other 754 cases were not padded because of the host's
process cap (each padded variant writes and reads a 48 MiB file); nothing in the 446 suggests a
dependence on the case. 9 cases are graded on over48 only: their under/at48 decode is not
byte-identical to the judged (non-canonical, mutated) witness, so there is no nearcore verdict to
grade there, while the cap rejects regardless. Every Lean result has nearcore's verdict, with the
reason `invalid: encoded_length exceeds MAX_COMPRESSED_STATE_WITNESS_SIZE` on every over48 variant
and the case's own reason (e.g. `MissingTrieValue`, `InvalidGasUsed`, claim mismatches) otherwise.
Lean time per 48 MiB fixture: 1.0–2.3 s CPU, 1.7–2.1 GB resident (before the zstd fix: 650–990 s).

Controls: each over48 variant differs from its at48 sibling by one zero byte of skippable-frame
padding, and on every honest case the at48 sibling is accepted, so these pairs isolate the cap.
No Lean build without the cap was made for a breakage run (each full checker build costs about an
hour on this host); the frame-level controls of `../size-limits/` (13/13 corrupt frames detected)
cover the decoder.

## Reproduce

```
bash oracle/scripts/link-nearcore.sh
CARGO_TARGET_DIR=T cargo build --release --manifest-path docs/evidence/lean-chunk-completion/size-limit-fixtures/ncref/Cargo.toml
CARGO_TARGET_DIR=T cargo build --release --manifest-path oracle/v3-successor/Cargo.toml
NEAR_SUCCESSOR_SCENARIO=code-response T/release/near-arena-oracle-v3-successor gen --domain d3 --seed 2029 \
  --chains 1 --blocks 30 --p-missing 0 --mutate-every 0 --code-mutant-p 0 --ood-cap 100000 --out RUN
python3 tools/d3/collect_fuel_stress.py --source RUN --out manifest.json
T/release/ncref codes RUN/ood/00-h10012-s3/witness.bin
python3 tools/d3/time_cases.py --checker CHECKER --cases-file LIST --out OUT.json
python3 tools/d3/size_limit_fixtures.py --ncref T/release/ncref --checker CHECKER \
  --cases-file witness48-cases.txt --variants plain,under48,at48,over48 --work DIR --out OUT.json --jobs 2
```
