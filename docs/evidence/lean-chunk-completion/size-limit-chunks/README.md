# Whole-chunk fixtures at the two witness-size boundaries (workplan item 4, W02)

Target: nearcore 2.13.4 (`44f7ae6cd7ef08bab604e20a473bf77e35d4c993`), PV86, mainnet parameters.
Checker: `nearspec-v3-check-successor --tier allFeatures` (sha256 `a1627ea3…`, the lane's
`checker-before`). Generator: `oracle/v3-successor` with the new opt-in scenario
`NEAR_SUCCESSOR_SCENARIO=code-cap` and the new subcommand `code-cap-probe` (`src/xfam.rs`). Binary
sha256 `1c221576…` (`oracle-d2`).

Item 4 asked for whole-chunk nearcore fixtures at both boundaries, or a stated reason why they
cannot be generated. Before this, the 64 MiB cap had only unit tests and the 48 MiB cap only
frame-level fixtures ([size-limits](../size-limits/README.md) §3).

**Result.**
- **64 MiB code-response cap.** Whole chunks whose cold code response is
  4,194,308 / 33,554,436 / 62,914,561 / 67,108,863 / **67,108,864 (at)** /
  **67,108,865 (over)** bytes:
  - Lean decides "at" and accepts it, matching nearcore. "over" is out of domain
    `w.code_response_size`.
  - Pinned nearcore's own `ContractCodeResponse::decompress_contracts` decodes "at" and rejects
    "over".
  - Population: 286 replayed cases, 0 disagreements.
- **48 MiB encoded-witness cap.** Whole-chunk fixtures at 50,331,647 / **50,331,648** /
  **50,331,649** encoded bytes, made with a zstd skippable-frame pad. Lean accepts "at" and rejects
  "over" at the length check, as nearcore's validator does.
- **No Lean accept of a nearcore reject. No Lean reject of a nearcore-accepted chunk.**
- A valid witness that crosses 48 MiB with real content is discussed in §2.3.

## 1. The 64 MiB contract-code-response cap

### 1.1 Which side of the cap is valid (pinned source)

- **The constant.** `MAX_UNCOMPRESSED_CONTRACT_CODE_RESPONSE_SIZE` = `ByteSize::mib(64)` =
  67,108,864 B in a non-`test_features` build (`core/primitives/src/stateless_validation/contract_distribution.rs:371-373`).
  With `test_features` it is 512 MiB.
- **The decoder.** A validator decodes a response with `decompress_contracts`
  (`chain/client/src/stateless_validation/partial_witness/partial_witness_actor.rs:999`). That calls
  `CompressedData::decode` (`core/primitives/src/utils/compression.rs:44-76`), which reads the zstd
  stream through `CountingRead`. `CountingRead` fails **iff `total_read > hard_limit`**
  (`core/primitives/src/utils/io.rs:81-92`).
- **So:** a borsh `Vec<CodeBytes>` of exactly 67,108,864 B is valid, and 67,108,865 B is rejected.
  On error the `?` drops the response, so the validator never gets the code and cannot endorse.
- **Lean** models the same condition as `codeResponseBytes codes ≤ maxContractCodeResponseBytes`
  (`RuntimeCore.lean:51,198`), with `codeResponseBytes = 4 + Σ(4 + |code|)`.

`oracle code-cap-probe` (`code-cap-probe.jsonl`) runs pinned nearcore's own
`ContractCodeResponse::encode` (V2, PV86) and then `decompress_contracts` on every call set. It also
shows that the oracle build does **not** carry `test_features`, because the error names
67,108,864.

| set | codes | borsh `Vec<CodeBytes>` | Lean `codeResponseBytes` | pinned `decompress_contracts` |
|---|---|---|---|---|
| one | 1 | 4,194,308 | 4,194,308 | ok |
| eight | 8 | 33,554,436 | 33,554,436 | ok |
| fifteen | 15 | 62,914,561 | 62,914,561 | ok |
| at−1 | 16 | 67,108,863 | 67,108,863 | ok |
| **at** | 16 | **67,108,864** | 67,108,864 | **ok** |
| **over** | 16 | **67,108,865** | 67,108,865 | **err: `Exceeded the limit of 67108864 bytes`** |

### 1.2 The scenario (`code-cap`)

- **Chain.** A quiet chain: no baseline traffic and no crafted injections, chain 0 (4 shards,
  1 Pgas), seed 801, `--p-missing 0`.
- **Genesis contracts.** Genesis holds 18 contracts `s0cc00`–`s0cc17`, all on one shard (shard id 3).
  - Each is a minimal module (`main`: one `storage_write`), padded with a custom section `pad`
    to an exact length: 12 × 4,194,300 B and 4 × 4,194,299 B for the at set. All lengths are
    ≤ `max_contract_size` 4,194,304.
  - `s0cc16` is one byte longer than `s0cc15`, and `s0cc17` one byte shorter.
  - The padding is SHA-256 counter output (incompressible), seeded per index, so all 18 codes are
    distinct.
- **Calls.** Each call set is submitted at one height, 8 heights apart. Every call is a local
  `FunctionCall main` transaction, so each set is executed in one chunk and that chunk's cold code
  response is exactly the set's codes.
- **Registry.** The contracts are registered in the generator's code registry. That lets the cold
  judge get them appended, and lets TestEnv's validators hold them precompiled. TestEnv does not
  route `ContractCodeRequest`; without the registry, shard 3 stalls on the first call.

Regeneration (about 20 s, 3.4 GB of cases; **not committed**: each boundary case carries up to
71 MB of incompressible code):

```
bash oracle/scripts/link-nearcore.sh
CARGO_TARGET_DIR=/tmp/oracle-target cargo build --release --manifest-path oracle/v3-successor/Cargo.toml
B=/tmp/oracle-target/release/near-arena-oracle-v3-successor
$B code-cap-probe > code-cap-probe.jsonl
NEAR_SUCCESSOR_SCENARIO=code-cap RAYON_NUM_THREADS=128 $B gen --domain d3 --seed 801 --first-chain 0 \
  --chains 1 --blocks 55 --p-missing 0 --mutate-every 0 --code-mutant-p 1 --ood-cap 100000 \
  --drop-cap 0 --out cc
python3 tools/d3/replay_successor.py --tier allFeatures --cases-file LIST --out rep --jobs 10 \
  --batch 1 --timeout 3600      # one case per process: the default batch of 100 times out
```

`code-cap-cases.json` has the code hashes and lengths, and the sha256 of every boundary case's
`claim.bin` and `witness.bin`. The run is deterministic: same seed, same binary, same case bytes.

### 1.3 Whole-chunk verdicts (honest boundary chunks)

The cold judge appends the codes straight into the base state, as `partial_witness_tracker.rs:693-696`
does after a response is decoded. It does **not** go through `decompress_contracts`. So it accepts
"over" too. The authoritative verdict on the cap is the probe in §1.1.

| chunk | code response | nearcore cold judge | pinned `decompress_contracts` | Lean `allFeatures` | Lean wall / max RSS |
|---|---|---|---|---|---|
| `00-h10006-s3` (one) | 4,194,308 | accept | ok | accept | 6 s / 0.30 GiB |
| `00-h10014-s3` (eight) | 33,554,436 | accept | ok | accept | 47 s / 1.19 GiB |
| `00-h10022-s3` (fifteen) | 62,914,561 | accept | ok | accept | 1 min 24 s / 2.06 GiB |
| `00-h10030-s3` (at−1) | 67,108,863 | accept | ok | accept | 1 min 30 s / 2.18 GiB |
| **`00-h10038-s3` (at)** | **67,108,864** | accept | ok | **accept** | 1 min 29 s / 2.19 GiB |
| **`00-h10046-s3` (over)** | **67,108,865** | accept (bypasses the cap) | **err** | **out of domain `w.code_response_size`** | 3 s / 2.12 GiB |

Lean on 64 MiB of code is not slow: about 90 s and 2.2 GiB for the at chunk, mostly SHA-256 of the
codes and parsing the custom sections.

### 1.4 Population (honest + code mutants, 286 cases)

| class | nearcore cold | Lean `allFeatures` | cases |
|---|---|---|---|
| no code (quiet-chain chunks, `code.none`) | accept / reject | accept / reject | 214 / 6 |
| code response ≤ 67,108,864 | accept | accept | 17 |
| code response ≤ 67,108,864 | reject (`MissingTrieValue`: dropped / flipped / truncated code) | reject | 34 |
| code response > 67,108,864 | accept (cold judge, cap bypassed) | out of domain `w.code_response_size` | 12 |
| code response > 67,108,864 | reject | out of domain `w.code_response_size` | 3 |

**0 disagreements.**

- **Negative fixtures at the boundary.** These include `code.flip.{0,1,2}` of the at chunk: a
  response of exactly 67,108,864 B with one wrong code. Lean decides them and rejects them, as
  nearcore does.
- **The 12 out-of-domain cold-judge accepts.** These are the honest over chunk and the
  `code.duplicate` / `code.extra_*` / `code.reorder` mutants that push a response past the cap. A
  real validator could only receive such a response by request, and pinned nearcore rejects it at
  decode. The exclusion is the integrator's decision (size-limits §5): the verdict depends on the
  validator's cache.
- The replay harness reports these as `domain_exclusion_where_in_domain`, because the generator's
  classifier does not label `w.code_response_size`.

### 1.5 Deliberate-breakage control C-code

- **The bug.** A checker built from HEAD `e65da9101` in a scratch copy, with `codeResponseBytes`
  missing its 4-byte vector prefix (`foldl … 0` instead of `… 4`).
- **What it does.** Six over-cap cases leave the exclusion. The honest **over** chunk
  (67,108,865 B) and two over-cap mutants become **accept**. Three become reject.
- **What that shows.** Without the exact borsh prefix, Lean would accept a chunk that pinned nearcore
  cannot validate. The rest of the population is unchanged.

## 2. The 48 MiB encoded-witness cap

### 2.1 Source

- **The check.** `validate_partial_encoded_state_witness` rejects
  `encoded_length > MAX_COMPRESSED_STATE_WITNESS_SIZE` = 50,331,648
  (`chain/client/src/stateless_validation/validate.rs:82-88`, constant `partial_witness.rs:18`).
- **When it runs.** It is the function's first check. It runs before the part-index/size checks,
  the signature check and any Reed-Solomon or zstd decode.
- **What it reads.** It compares the declared `encoded_length`, so equal is valid.
- **Lean.** Lean applies the same rule to the `near-arena-cwitness-v3` input (size-limits §1).

### 2.2 Whole-chunk padding fixtures (`pad48-cases.tar.gz`, `pad48-cases.json`)

- **Base.** A real honest `state-init-emit` chunk, `se701/00-h10022-s1`: nearcore cold accepts it,
  and it carries a state init followed by successful emits (see `../remaining-shapes`).
- **Encoding.** Its witness is encoded exactly as nearcore distributes it: `zref encode`, the
  vendored zstd 1.5.6, level 1, 4 workers, which mirrors `CompressedData::encode`. That gives
  10,708 → 7,288 B.
- **Padding.** A zstd skippable frame (magic `0x184D2A50`, RFC 8878 §3.1.2) is appended so the
  encoded length is exact. zstd's stream decoder skips it.
- **Decode check.** `zref decode` under the 64 MiB limit, which mirrors `CompressedData::decode`,
  returns the base witness byte for byte for every variant.

| fixture | encoded length | padding | nearcore | Lean `allFeatures` | Lean wall / max RSS |
|---|---|---|---|---|---|
| base (in the clear) | — | — | accept (cold) | accept | 0.3 s / 0.06 GiB |
| `pad48.at-minus-1` | 50,331,647 | zeros | accept (decodes to the base) | accept | 15 min 4 s / 1.93 GiB |
| **`pad48.at`** | **50,331,648** | zeros | **accept** | **accept** | 14 min 0 s / 1.97 GiB |
| **`pad48.over`** | **50,331,649** | zeros | **reject** (`validate.rs:82-88`) | **reject**: `encoded_length exceeds MAX_COMPRESSED_STATE_WITNESS_SIZE` | 2 s / 1.61 GiB |
| `pad48.at.random` | 50,331,648 | SHA-256 counter | accept | accept | 14 min 18 s / 1.75 GiB |
| `pad48.over.random` | 50,331,649 | SHA-256 counter | reject | reject | 3 s / 1.61 GiB |

- **What is committed.** The base and the three zero-padded variants (185 KB gzipped). The random
  variants are regenerated with
  `python3 tools/d3/pad_encoded_witness.py ZREF BASE_CASE OUT`; their sha256 values are in
  `pad48-cases.json`.
- **Where the "accept" verdicts come from.** Nearcore's verdict on "at" is the cold judge's verdict
  on the base witness, carried over through the byte-identical decode. The oracle judge takes the
  witness in the clear and does not itself run the encoded-length check.
- **Performance.** Lean takes about 14 minutes to walk a 48 MiB skippable frame. This is a W16
  item: the decoder's per-byte cost on `List UInt8`.

### 2.3 A valid witness above 48 MiB with real content

- **Not generated here.** Whether an honestly produced PV86 witness can exceed 48 MiB, and with what
  consequence, is analysed in a restricted note that is outside this public repository and awaiting
  a disclosure decision.
- **What this harness has reached.** The largest witness any generator in this repo has produced
  is 9,464,574 B in the clear (`gate-b-caps` `wsize.above`); its padding compresses to almost
  nothing.
- **Why the padding fixtures stand in for it.** The two boundary rows above test exactly the
  validator rule that applies to such a witness. The rule depends only on `encoded_length`, so
  content-bearing fixtures would exercise the same comparison.

## 3. What is not covered

- **Code-cap mutants above the cap.** These are out of domain by decision (size-limits §5). A
  warm validator could hold all the codes compiled, request nothing, and validate the chunk.
- **`MAX_CONTRACTS_PER_REQUEST` = 1282.** Never reached: there are 16–17 codes per chunk here, and
  size-limits §5 argues it never binds.
- **The 64 MiB decoded-witness limit with real content.** Tested only at frame level (size-limits
  §3, `dec.at64` / `dec.over64`).
- **The signed tier.** Not run on these fixtures. Its `witness.bin` bound is open item 6(c).
