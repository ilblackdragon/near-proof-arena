# Lean runs the chunk transition from inputs and produces matching outputs

Worktree `/data/illia/nearproof-wt/lean-chunk-final`, branch `work/lean-chunk-final-outputs`.
Requirement: `docs/requirements/LEAN_CHUNK_TRANSITION_PLAN.md`.

## The claim

Lean's checker consumes `claim.bin` and `witness.bin` — no oracle, no precomputed answer — executes the
chunk transition, and *returns* the consensus outputs it computed. Those outputs equal the values
nearcore produced when it applied the same chunk.

This is established in three independent ways, each measuring a different thing.

## 1. The checker computes and compares every output

`checkD2CoreObs` (`spec/lean/v3/NearSpecV3/ChunkValidationD2.lean`) runs the full D2/D3 pipeline and
returns an `Observable` record:

| field | how it is produced | compared against |
|---|---|---|
| `stateRoot` | `root` after main + all implicit transitions | `H.prevStateRoot` |
| `outcomeRoot` | `outcomeRootD1 out.outcomes` | `H.prevOutcomeRoot` |
| `gasBurnt` | `out.gasUsed` | `H.prevGasUsed` |
| `balanceBurnt` | `out.balanceBurnt` | `H.prevBalanceBurnt` |
| `outgoingReceiptsRoot` | `outgoingReceiptsRootD2 L out.outgoing` | `H.prevOutgoingReceiptsRoot` |
| `proposals` | `out.proposals.map Proposal.encode` | `H.proposals` |
| `txRoot` | `merklizeBorsh (w.newTxs.map TxD2.raw)` | `H.txRoot` |
| `encodedMerkleRoot` | `encodedMerkleRoot c.rsDataParts c.rsTotalParts body` | `H.encodedMerkleRoot` |
| `encodedLength` | same | `H.encodedLength` |
| `congestion` | `out.congestion` | `H.congestion` |
| `bwRequests` | `out.bwRequests` | `H.bwRequests` |
| `logs` | `out.outcomes.map (·.logs) \|>.flatten` | folded into `outcomeRoot` |
| `receiptCount` | `out.outgoing.length` | folded into `outgoingReceiptsRoot` |
| `wasmGas` | `out.wasmGas` | capped by `G_α` |

Every field is a value the checker *computed*; none is read back from the header. The signed checker
`checkD2Core` is defined as `(checkD2CoreObs …).map fun _ => ()`, so the accept/reject decision and every
downstream proof are definitionally unchanged. `checkD2CoreObs_agrees` states the equivalence; its axiom
footprint is `propext`, `Quot.sound`.

**Why this matters.** An earlier version emitted the header's own fields
(`Observable.ofChunkInner H [] [] 0 0`), so a report comparing emitted outputs against the claim header
was comparing a value with itself. The evidence below measures the computation instead.

## 2. Outputs agree with the claim header across the whole corpus

`tools/d3/check_outputs.py` runs the driver over every case and compares each emitted field against an
independent decode of `claim.bin` (`tools/d3/claim_outputs.py`, written against the same wire format but
sharing no code with Lean).

Corpora `d3c7`, `d3c8`, `d3c9`, `d3c10`; families `d3`, `mutants`, `ood`.

| corpus | cases | accept | reject | out-of-domain | field mismatches | accepted-with-null-outputs | failures |
|---|---|---|---|---|---|---|---|
| d3c7 | 33,248 | 11,834 | 20,685 | 729 | 0 | 0 | 0 |
| d3c8 | 56,246 | 17,662 | 30,702 | 1,126 | 0 | 0 | 0 |
| d3c9 | 15,995 | 5,715 | 9,938 | 342 | 0 | 0 | 0 |
| d3c10 | 16,551 | 5,920 | 10,280 | 351 | 0 | 0 | 0 |

Denominator: every case on disk. A case with no emitted line counts as a failure, so a crashed shard
cannot pass silently.

## 3. Outputs agree with nearcore's *independent* record

`tools/d3/check_nearcore_features.py` compares Lean's computed values against fields nearcore wrote into
`meta.json` — which Lean never reads. Two comparisons are strictly independent of the claim:

* `wasmGas` vs `fc_gas_burnt_for_function_call`
* log count vs `n_logs`

| corpus | honest accepted | independent comparisons | mismatches |
|---|---|---|---|
| d3c9 | 2,656 | 5,312 | 0 |
| d3c7 | 5,381 | 10,762 | 0 |

Example (`d3c9/d3/00-h10012-s0`): Lean computes `wasmGas = 659,245,237,430`; nearcore's own feature
records `fc_gas_burnt_for_function_call = 659,245,237,430`. Before the fix the driver emitted `0`.

## 4. A wrong output field is caught for the right reason

`tools/d3/check_output_mutants.py` takes honest base cases and their header-output mutants. For each
mutant it requires: base accepted with outputs; mutant rejected; rejection reason is the checker's reason
for *that specific field*.

| corpus | honest bases | mutants | rejected for the right field | wrong |
|---|---|---|---|---|
| d3c7 | 40 | 360 | 360 | 0 |
| d3c8 | 40 | 360 | 360 | 0 |
| d3c9 | 40 | 360 | 360 | 0 |
| d3c10 | 40 | 360 | 360 | 0 |

Field-by-field (d3c9, 40 each): `prev_state_root` → `InvalidStateRoot`, `prev_outcome_root` →
`InvalidOutcomesProof`, `prev_gas_used` → `InvalidGasUsed`, `prev_balance_burnt` → `InvalidBalanceBurnt`,
`prev_outgoing_receipts_root` → `InvalidReceiptsProof`, `tx_root` → `InvalidTxRoot`,
`encoded_merkle_root` → `InvalidChunkEncodedMerkleRoot`, `encoded_length` → `InvalidChunkEncodedLength`,
`gas_limit` → `InvalidGasLimit`. All 40/40 each.

This is the causal link: the mutant changes exactly one header field; Lean's computed value for that
field is unchanged; the checker rejects naming that field. The rejection therefore *is* the observation
that Lean's computed value differs from the mutated header.

## 5. The output driver does not change any verdict

The signed driver (`nearspec-v3-check-d3`) and the output driver (`nearspec-v3-check-d3-out`) are the
same computation; the second projects to a record. Sampled: 120 honest cases and 200 mutant cases,
**0 disagreements** in verdict or reason string.

## Reproduce

```sh
cd /data/illia/nearproof-wt/lean-chunk-final

# build
(cd spec/lean/v3 && lake build NearSpecV3)                       # 102 jobs
(cd spec/lean/v3 && lake build NearSpecV3.Logged.API)            # 90 jobs
(cd oracle/wasm-d3/lean && lake build nearspec-v3-check-d3-out)  # 123 jobs

# 2. whole-corpus output agreement
for c in d3c7 d3c8 d3c9 d3c10; do
  python3 tools/d3/check_outputs.py /data/illia/nearproof-deps/corpora/$c \
    --families d3,mutants,ood --shards 20 --report var/out-runs/full-$c.json
done

# 3. independent feature cross-check
for c in d3c7 d3c9; do
  python3 tools/d3/check_nearcore_features.py /data/illia/nearproof-deps/corpora/$c \
    --family d3 --shards 12 --report var/out-runs/nearcore-feat-$c.json
done

# 4. causal header-mutant check
for c in d3c7 d3c8 d3c9 d3c10; do
  python3 tools/d3/check_output_mutants.py /data/illia/nearproof-deps/corpora/$c \
    --shards 20 --bases 40 --report var/out-runs/mut-$c.json
done
```

Every script exits `0` only when its failure count is zero.

## What this does not establish

* **Nothing here is a proof of agreement.** Sections 2–4 are differential tests over the corpora on
  disk. A chunk outside those corpora could disagree. The *theorems* establish the structural facts
  (the signed checker projects the observable one; an accepted run's computed fields equal the header's),
  not agreement with nearcore on arbitrary inputs.
* **`out of domain` cases are excluded from output comparison** by construction: the checker stops
  before computing outputs. Their verdict agreement is measured, their outputs are not comparable.
* **Rejected cases emit no outputs.** The checker's computed values on a failing path are not reported;
  the reason string is. Emitting them would require the checker to keep partial state through failure,
  which the signed relation deliberately does not do.
* **`receiptCount` is not compared against `receipt_classes`.** An earlier attempt did and reported 540
  disagreements; the metric is wrong (`receipt_classes` counts classified receipt events, while the
  outgoing set also includes receipts materialised during execution). `outgoingReceiptsRoot` — a merkle
  commitment over the whole outgoing set — is the authoritative comparison and matches on 300/300 sampled
  honest cases.
