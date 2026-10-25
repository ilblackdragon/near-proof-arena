# D2 runs the chunk transition from inputs and produces matching outputs

Worktree `/data/illia/nearproof-wt/lean-d2-outputs`, branch `work/d2-output-evidence`, base commit
`5491f7f03d2c1521e62c6407d8df52afad4471df`. Companion to [RESULT.md](RESULT.md), which makes the same
claim for the D3 pipeline. This document closes two gaps in the D3 evidence when applied to D2:

1. The D2 output-agreement report lived in gitignored `var/`, so it was not committed evidence.
2. The *causal* mutant check existed only for D3: `tools/d3/check_output_mutants.py` hardcoded the
   `d3` family directory and had no `--d2` mode. The D2 corpus ships 12,507 `hdr.*` mutants that were
   never subjected to it.

Corpus: `/data/illia/nearproof-deps/corpora/d2corpus.v2` — 67,384 cases on disk: `d2/` 10,537,
`mutants/` 56,457, `ood/` 390. Generated against nearcore `44f7ae6cd7ef08bab604e20a473bf77e35d4c993`,
PV86, seed 6262.

Driver binary: `oracle/wasm-d3/lean/.lake/build/bin/nearspec-v3-check-d3-out`
`sha256 = 6ec0e691af1c9c4038ee62e1c20cf32f41c82bc91f585a9aee84af5580daa64a`.

## The claim

Lean's D2 checker consumes `claim.bin` and `witness.bin` — no oracle, no precomputed answer — executes
the chunk transition through the signed `checkD2Core`, and on acceptance returns the consensus outputs it
computed. For every honest case on disk those outputs equal the claim header's fields, and for every
header-output mutant the checker rejects *because* the mutated field disagrees with the computed value.

## 1. The tool change

`tools/d3/check_output_mutants.py` gained three options and two family tables. The default D3 path is
byte-identical to before: the same nine-family table, the same reason comparison, the same report schema.

| option | effect |
|---|---|
| `--d2` | runs `DRIVER --d2 CASE…` and reads honest bases from `<corpus>/d2` |
| `--family NAME` | overrides the honest-base subdirectory in either mode (default: `d2` with `--d2`, else `d3`) |
| `--families core\|extended` | selects the mutant-family table; `core` is the D3 default, `extended` is the default under `--d2` |

Two tables exist because the *corpora* differ in which families they ship, not because the checkers
differ. `checkD2CoreOut` is one shared computation, and the D2 driver mode evaluates it with
`d2Hooks`/`false`/no gas cap; the comparison block at `spec/lean/v3/NearSpecV3/ChunkValidationD2.lean:255-271`
is the same code for both modes. I confirmed this empirically rather than by reading: all 17 `hdr.*`
mutant families produce identical verdict and reason strings under `--d2` and under D3 on the same cases
(§4), so the `EXPECTED` reason table needed no per-mode override. It would have been a mistake to assume
that, and a mistake to weaken the check if it had been false.

* `core` (9 families, the D3 default and unchanged): `prev_state_root`, `prev_outcome_root`,
  `prev_gas_used`, `prev_balance_burnt`, `prev_outgoing_receipts_root`, `tx_root`,
  `encoded_merkle_root`, `encoded_length`, `gas_limit`.
* `extended` (14 families, default under `--d2`): `core` plus the other endorsed-header fields the same
  comparison block checks — `proposals` (`InvalidValidatorProposals`), `congestion`
  (`InvalidCongestionInfo`, three sub-fields), `bandwidth_requests` (`InvalidBandwidthRequests`).

The three header families that are **not** computed-output comparisons are never counted as passes:

| family | observed on all 747 bases | why excluded |
|---|---|---|
| `hdr.proposed_split.some` | reject `InvalidChunkHeaderShardSplit` (715/715) | structural header guard `H.proposedSplit.isNone`, not a computed value |
| `hdr.height_created` | accept (747/747) | the checker does not compare it |
| `hdr.height_included(unchecked)` | accept (747/747) | the name says unchecked; the checker does not compare it |

The script runs them and reports their verdict histogram under `uncovered_families`, so a behaviour change
is visible, but their acceptance is never scored as a mutant pass. The committed [mut-d2.json](mut-d2.json)
carries that histogram: `height_created` 747/747 accept, `height_included(unchecked)` 747/747 accept,
`proposed_split.some` 715/715 reject `InvalidChunkHeaderShardSplit`.

The "pre-empted by another output check is acceptable, unrelated guard is not" rule is preserved: a
mutant's reason may name its own field's check or another *output* field's check (an earlier comparison
can pre-empt a later one), and anything else is a failure. No mutant in this run was pre-empted — all
10,298 matched their own field's reason exactly.

## 2. Whole-corpus output agreement, D2 pipeline

`tools/d3/check_outputs.py` decodes each case's `claim.bin` independently in Python and compares every
emitted field. Run over all three families, so the denominator is every case on disk:

```sh
python3 tools/d3/check_outputs.py /data/illia/nearproof-deps/corpora/d2corpus.v2 \
  --d2 --families d2,mutants,ood --shards 20 --report var/out-runs/full-d2.json
```

| cases | accept | reject | out-of-domain | field mismatches | accepted-with-null-outputs | missing lines | failures |
|---|---|---|---|---|---|---|---|
| 67,384 | 17,738 | 49,256 | 390 | 0 | 0 | 0 | 0 |

Report: [full-d2.json](full-d2.json). A case with no emitted line counts as a failure, so a crashed
shard cannot pass silently.

## 3. Causal header-mutant check, D2 pipeline

```sh
python3 tools/d3/check_output_mutants.py /data/illia/nearproof-deps/corpora/d2corpus.v2 \
  --d2 --shards 24 --bases 747 --report var/out-runs/mut-d2.json
```

`--bases 747` is the full set: every base case in the corpus that has at least one covered `hdr.*` mutant
(747 of the 10,537 honest bases). The sweep exercised **10,298** of the 12,507 `hdr.*` mutants — every
mutant in the 14 covered families. The 2,209 excluded mutants are exactly the three non-output families
above.

| honest bases accepted with outputs | covered families | mutants checked | output-reject | wrong | failures |
|---|---|---|---|---|---|
| 747/747 | 14 | 10,298 | 10,298 | 0 | 0 |

Per-family, all 747/747 or 715/715 as shipped, zero wrong in every row:

| family | field | n | output-reject | wrong |
|---|---|---|---|---|
| `hdr.prev_state_root` | `stateRoot` | 747 | 747 | 0 |
| `hdr.prev_outcome_root` | `outcomeRoot` | 747 | 747 | 0 |
| `hdr.prev_gas_used` | `gasBurnt` | 747 | 747 | 0 |
| `hdr.prev_balance_burnt` | `balanceBurnt` | 747 | 747 | 0 |
| `hdr.prev_outgoing_receipts_root` | `outgoingReceiptsRoot` | 747 | 747 | 0 |
| `hdr.proposals.add` | `proposals` | 715 | 715 | 0 |
| `hdr.tx_root` | `txRoot` | 747 | 747 | 0 |
| `hdr.encoded_merkle_root` | `encodedMerkleRoot` | 747 | 747 | 0 |
| `hdr.encoded_length` | `encodedLength` | 747 | 747 | 0 |
| `hdr.gas_limit` | `gasLimit` | 747 | 747 | 0 |
| `hdr.congestion.allowed_shard` | `congestion` | 715 | 715 | 0 |
| `hdr.congestion.delayed_gas` | `congestion` | 715 | 715 | 0 |
| `hdr.congestion.receipt_bytes` | `congestion` | 715 | 715 | 0 |
| `hdr.bandwidth_requests.add` | `bwRequests` | 715 | 715 | 0 |

Report: [mut-d2.json](mut-d2.json).

A 40-base slice (`--bases 40`) also passes with 0 failures and covers every one of the 14 families; the
747-base run above is the committed denominator.

This is the causal link. Each mutant changes exactly one endorsed-header field and leaves the witness
untouched. Lean's computed value for that field is unchanged. The checker rejects, naming that field.
The rejection *is* the observation that Lean's computed value differs from the mutated header — a mutant
rejected for any unrelated guard would be counted as a failure.

## 4. The reason table holds across both pipelines

Before relying on one `EXPECTED` table for D2, I ran all 17 `hdr.*` families through both driver modes on
40 bases and compared the verdict/reason histograms. They are identical family for family: the 9 core
families, the 5 extended families, the `proposed_split` guard, and the two accepted families all match
between `--d2` and D3. This is the evidence that D2 needs no per-mode reason override, and it is why the
table was not weakened or duplicated.

## 5. The D3 path did not regress

The same script, unmodified in behaviour, re-run on D3 exactly as [RESULT.md](RESULT.md) documents:

```sh
python3 tools/d3/check_output_mutants.py /data/illia/nearproof-deps/corpora/d3c9 \
  --shards 20 --bases 40 --report var/out-runs/mut-d3c9-regress.json
```

40/40 bases accepted, 360/360 mutants rejected for the right field, 0 failures. The report is
**byte-identical** to the committed [mut-d3c9.json](mut-d3c9.json) (`cmp` clean), so the new options
changed nothing on the existing path.

## Reproduce

```sh
cd /data/illia/nearproof-wt/lean-d2-outputs

# build (only needed if the binary is absent)
(cd spec/lean/v3 && lake build NearSpecV3)
(cd spec/lean/v3 && lake build NearSpecV3.Logged.API)
(cd oracle/wasm-d3/lean && lake build nearspec-v3-check-d3-out)
sha256sum oracle/wasm-d3/lean/.lake/build/bin/nearspec-v3-check-d3-out   # 6ec0e691…a64a

# 2. whole-corpus output agreement (all three families = every case on disk)
python3 tools/d3/check_outputs.py /data/illia/nearproof-deps/corpora/d2corpus.v2 \
  --d2 --families d2,mutants,ood --shards 20 --report var/out-runs/full-d2.json

# 3. causal header-mutant check, full base set
python3 tools/d3/check_output_mutants.py /data/illia/nearproof-deps/corpora/d2corpus.v2 \
  --d2 --shards 24 --bases 747 --report var/out-runs/mut-d2.json

# 5. D3 regression (must be byte-identical to mut-d3c9.json)
python3 tools/d3/check_output_mutants.py /data/illia/nearproof-deps/corpora/d3c9 \
  --shards 20 --bases 40 --report var/out-runs/mut-d3c9-regress.json
cmp var/out-runs/mut-d3c9-regress.json docs/evidence/lean-chunk-final-outputs/mut-d3c9.json
```

Every script exits `0` only when its failure count is zero. The committed reports were copied from
`var/out-runs/`; `var/` itself is gitignored and is not evidence.

## What this does not establish

* **Nothing here is a proof of agreement.** Sections 2–3 are differential tests over the corpus on disk.
  A chunk outside this corpus could disagree. The *theorems* establish structural facts — the signed
  checker projects the observable one (`checkD2CoreObs_agrees`), and an accepted run's computed fields
  equal the header's — not agreement with nearcore on arbitrary inputs. The D2 verdict agreement against
  nearcore is measured elsewhere; this document is about the outputs and the causal mutant link.
* **The 2,209 non-output header mutants are not covered as output checks.** `proposed_split` is a
  structural guard; `height_created` and `height_included(unchecked)` are accepted by the checker and a
  change to them is not a disagreement. They are run and their verdicts reported, but a mutant the
  checker legitimately ignores cannot be a causal output test. Counting them as passes would be wrong;
  counting them as failures would be wrong too. They are neither.
* **Rejected cases emit no outputs.** The checker's computed values on a failing path are not reported;
  the reason string is. So the mutant check tests *which* comparison fired, not the numeric value of the
  disagreement. Emitting partial state through failure would require changing the signed relation, which
  this task deliberately did not touch.
* **`out of domain` cases are excluded from output comparison** by construction: the checker stops
  before computing outputs. Their verdicts are counted (390) but their outputs are not comparable.
* **The output comparison trusts the Python claim decoder**, not Lean's. It shares no code with Lean and
  is written against the same wire format, but a bug present in both decoders would not show. The
  independent nearcore-feature cross-check in [RESULT.md](RESULT.md) §3 covers that gap for D3; it was
  not repeated for D2 here, because the D2 corpus's `meta.json` feature fields that would serve as an
  independent witness were not audited in this pass. That is an open item, not a claim.
* **One binary, one host, one corpus generation.** The counts are this host's copy of the corpus. A
  regenerated corpus with a different seed would have different bases and would need its own run.
