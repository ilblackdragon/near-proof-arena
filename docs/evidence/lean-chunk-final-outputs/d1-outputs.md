# D1 emits its computed outputs and they match the claim header

Worktree `/data/illia/nearproof-wt/lean-d1-outputs`, branch `work/d1-output-agreement`,
base commit `5491f7f03`. Closes the D1 hole left by the D2/D3 output work in this directory's
`RESULT.md`: D2 and D3 returned computed outputs from their checkers; D1 returned `Except String Unit`
and discarded them, so D1 had verdict agreement but **zero output evidence**.

## 1. The change: `checkD1` is now the projection of an output-returning checker

`checkD1` (`spec/lean/v3/NearSpecV3/ChunkValidationD1.lean`) computed the whole chunk transition and
validated ~13 consensus outputs against the endorsed header at step 3.7 — then returned `Unit`, so those
values never left the checker. The additive change, following `checkD2Core`/`checkD2CoreObs`
(`ChunkValidationD2.lean:115,294`):

| declaration | content |
|---|---|
| `checkD1CoreObs : Bytes → Bytes → Except String Observable` | the same pipeline as the signed checker, returning the computed record |
| `d1Outputs` | the record builder: takes exactly the comparison's operands |
| `checkD1 : Bytes → Bytes → Except String Unit` | **`(checkD1CoreObs …).map fun _ => ()`** — definitionally the projection |
| `checkD1CoreOut` (`ChunkValidationD1Out.lean`) | `checkD1CoreObs`, the name the driver calls |

The pipeline's steps, order and error strings are unchanged; only the final `return` now carries the
record. No check was removed or weakened, and no reason string changed.

### Every emitted field is a computed value

| field | computed as | compared against |
|---|---|---|
| `stateRoot` | `root` after the main and all implicit transitions | `H.prevStateRoot` |
| `outcomeRoot` | `outcomeRootD1 out.outcomes` | `H.prevOutcomeRoot` |
| `gasBurnt` | `out.gasUsed` | `H.prevGasUsed` |
| `balanceBurnt` | `out.tokensBurnt` | `H.prevBalanceBurnt` |
| `outgoingReceiptsRoot` | `outgoingReceiptsRoot L out.outgoing` | `H.prevOutgoingReceiptsRoot` |
| `proposals` | `[]` | `H.proposals.isEmpty` |
| `txRoot` | `merklizeBorsh (w.newTxs.map Tx.raw)` | `H.txRoot` |
| `encodedMerkleRoot` | Reed–Solomon encoded chunk body | `H.encodedMerkleRoot` |
| `encodedLength` | same | `H.encodedLength` |
| `congestion` | `ownCongestion` = own slot info + allowed shard | `H.congestion` |
| `bwRequests` | `[]` | `H.bwRequests.isEmpty` |
| `logs` | `out.outcomes.map (·.logs) \|>.flatten` | folded into `outcomeRoot` |
| `receiptCount` | `out.outgoing.length` | folded into `outgoingReceiptsRoot` |
| `wasmGas` | `0` | not compared (no WASM in D1) |

`proposals`, `bwRequests` and `wasmGas` are the three fields D1 genuinely does not compute. They are
recorded as what the checker actually establishes, not fabricated observations: D1's comparison checks
`H.proposals.isEmpty` / `H.bwRequests.isEmpty` (so the computed list is empty), and D1 executes no WASM
(so `wasmGas` is `0`). `d1Outputs_not_computed` proves all three by reflexivity.

### Theorems (axiom footprints measured with `#print axioms`)

| theorem | statement | axioms |
|---|---|---|
| `checkD1CoreObs_agrees` | `(∃ o, checkD1CoreObs cb wb = .ok o) ↔ checkD1 cb wb = .ok ()` | `propext, Quot.sound` |
| `checkD1CoreObs_reject` | `checkD1CoreObs cb wb = .error e → checkD1 cb wb = .error e` | `propext, Quot.sound` |
| `checkD1CoreOut_agrees` | the same iff for `checkD1CoreOut` | `propext, Quot.sound` |
| `checkD1CoreOut_reject` | the same rejection statement for `checkD1CoreOut` | `propext, Quot.sound` |
| `checkD1_accepted_observable_computed` | `checkD1CoreOut cb wb = .ok o → checkD1CoreObs cb wb = .ok o` | `propext, Quot.sound` |
| `checkD1_ok_iff_coreOut_ok` | `checkD1 cb wb = .ok () ↔ ∃ o, checkD1CoreOut cb wb = .ok o` | `propext, Quot.sound` |
| `checkD1_error_iff_coreOut_error` | `checkD1 cb wb = .error e ↔ checkD1CoreOut cb wb = .error e` | `propext, Quot.sound` |
| `d1Outputs_fields` | each emitted field equals the computed argument it was built from | `propext` |
| `d1Outputs_not_computed` | `proposals = [] ∧ bwRequests = [] ∧ wasmGas = 0` | `propext` |
| `agreesWithHeaderD1_refl` | a header-shaped record satisfies D1's header predicate | `propext, Classical.choice, Quot.sound` |

Allowed set: `propext`, `Classical.choice`, `Quot.sound`. **No `sorryAx`, no new axioms.** The build
emits each footprint into the build log; the raw lines are in §6.

## 2. Outputs agree with the claim header across the whole D1 corpus

`tools/d3/check_outputs.py --d1` runs the driver's `--d1` mode over every case and compares each emitted
field against an independent Python decode of `claim.bin` (`tools/d3/claim_outputs.py`, written against
the same wire format, sharing no code with Lean). The decoder needed **no change** for D1: the D1 and D2
claims share the claim / chunk-header wire format. Verified on all 3,394 honest D1 claims (0 decode
failures) and on 20-case samples of each family before the run.

Corpus `/data/illia/nearproof-deps/corpora/d1run`; families `d1`, `mutants`, `ood`.

| family | cases | accept | reject | out-of-domain | accepted with outputs | field mismatches | missing lines | failures |
|---|---|---|---|---|---|---|---|---|
| `d1` | 3,394 | 3,394 | 0 | 0 | 3,394 | 0 | 0 | 0 |
| `mutants` | 46,009 | 7,695 | 37,437 | 877 | 7,695 | 0 | 0 | 0 |
| `ood` | 3,645 | 0 | 0 | 3,645 | 0 | 0 | 0 | 0 |
| **total** | **53,048** | **11,089** | **37,437** | **4,522** | **11,089** | **0** | **0** | **0** |

Denominator: every case on disk. A case with no emitted line counts as a failure, so a crashed shard
cannot pass silently. Rejected and out-of-domain cases emit `outputs: null` by design (the signed
checker's failing path does not return a record); they are counted, not failed. D1-only invariants also
hold on all 11,089 accepted cases: `wasmGas = 0` and `bwRequests = []` — no fabricated D2/D3-only values.

### Verdict agreement: the projection changed no verdict

`checkD1` is definitionally `(checkD1CoreObs …).map fun _ => ()`, so the two drivers must agree case for
case. `tools/d3/check_d1_verdict_agreement.py` runs the **signed** driver
(`nearspec-v3-check-d1`) and the **output** driver (`nearspec-v3-check-d3-out --d1`) over the same
53,048 cases and compares `(verdict, reason)` per case. See §5 for the measured result.

## 3. Reproduce

```sh
cd /data/illia/nearproof-wt/lean-d1-outputs

# Lean: the library module and the new reporting module
(cd spec/lean/v3 && lake build NearSpecV3)                  # 102 jobs
(cd spec/lean/v3 && lake build NearSpecV3.ChunkValidationD1Out)   # 35 jobs

# drivers
(cd spec/lean/v3 && lake build nearspec-v3-check-d1)        # 202 jobs
(cd oracle/wasm-d3/lean && lake build nearspec-v3-check-d3-out)   # 125 jobs

# whole-corpus output agreement (all three families)
python3 tools/d3/check_outputs.py /data/illia/nearproof-deps/corpora/d1run \
  --families d1,mutants,ood --d1 --shards 20 \
  --report docs/evidence/lean-chunk-final-outputs/d1-outputs-report.json

# verdict agreement: signed vs output driver, case for case
python3 tools/d3/check_d1_verdict_agreement.py /data/illia/nearproof-deps/corpora/d1run \
  --families d1,mutants,ood --shards 20 \
  --report docs/evidence/lean-chunk-final-outputs/d1-verdict-agreement.json

# axiom footprints
(cd spec/lean/v3 && lake env lean ../../../docs/evidence/lean-chunk-final-outputs/D1Axioms.lean)
```

## 4. Artifact hashes (sha256)

Sources:

| file | sha256 |
|---|---|
| `spec/lean/v3/NearSpecV3/ChunkValidationD1.lean` | `eb1c92ed716fd19c219966a67915272f8bcbf8ec9d7f68584a2de1bb21119c12` |
| `spec/lean/v3/NearSpecV3/ChunkValidationD1Out.lean` | `3027cbca9a12504f42851be3eea36cd67f015460a4c92c1a889169fa0adba500` |
| `spec/lean/v3/NearSpecV3.lean` (root import added) | `80e56be455204b7bb5c0f2e05be9f50a2ac37c4686466c2e2730705c96df2f88` |
| `oracle/wasm-d3/lean/MainD3Out.lean` | `ad117de4fb3e4a9bc4a21c342403cc89eab8c9bb5a67aeae225b743b379bb6ba` |
| `tools/d3/check_outputs.py` | `642995c1286f953a2ae9126a37860566af8e2d8c8992a27923607384e8c04258` |
| `tools/d3/check_d1_verdict_agreement.py` | `4fd1554d1ad184205eaa04b0e53630c40377b76406d077f6d638780e95e071db` |
| `zk-formal/ZkFormal/NearV3/D1/F1/CheckD1.lean` (proof patched) | `fb2f85cf37700575d418ca7bdb57f464f18d142191b2f3bb40d9335ee135345d` |

Built binaries:

| binary | sha256 |
|---|---|
| `oracle/wasm-d3/lean/.lake/build/bin/nearspec-v3-check-d3-out` | `9d7944722c3f1a728efca3e8e43d65b023042313099495efb73260eca1efa3df` |
| `spec/lean/v3/.lake/build/bin/nearspec-v3-check-d1` | `61ca196e58354995e7d91f4f492615c9b2ee1290116d2607cb55bd594de7e78e` |

## 5. Measured results

### 5.1 Output agreement, whole corpus (one run, all three families)

Command: `python3 tools/d3/check_outputs.py /data/illia/nearproof-deps/corpora/d1run --families d1,mutants,ood --d1 --shards 20`

```
cases read: 53048 (d1,mutants,ood)
mode: d1
verdicts: {'accept': 11089, 'reject': 37437, 'out_of_domain': 4522}
accepted with outputs: 11089
field mismatches: 0
accepted but null outputs: 0
missing lines: 0
d1 invariant failures: none
TOTAL FAILURES: 0
```

Machine-readable report committed beside this document: `d1-outputs-report.json`
(`11857dc679556f693cd77c50e7afcdf88796636dff506fe18e3e8b5d405e00bd`).
`mismatches_by_field` is empty: zero mismatches on `stateRoot`, `outcomeRoot`, `gasBurnt`,
`balanceBurnt`, `outgoingReceiptsRoot`, `proposals`, `txRoot`, `encodedMerkleRoot`, `encodedLength`,
and on the D1-only invariants (`wasmGas = 0`, `bwRequests = []`).

### 5.2 Verdict agreement, signed vs output driver

Command: `python3 tools/d3/check_d1_verdict_agreement.py /data/illia/nearproof-deps/corpora/d1run --families d1,mutants,ood --shards 20`

```
cases read: 53048
signed verdicts: {'accept': 11089, 'reject': 37437, 'out_of_domain': 4522}
verdict disagreements: 0
reason-only differences: 0
missing lines: 0
TOTAL FAILURES: 0
```

So the projection changed **no verdict and no reason string** on any of the 53,048 cases — the signed
relation is unchanged in practice as well as by definition. The verdict counts also match the earlier
D1 verdict-agreement evidence (53,048/53,048, 0 disagreements). Committed report:
`d1-verdict-agreement.json` (`90a1b91c24d4e11a721a553d25b90511d6b0bedbfb204821ecc88dcdefba8d62`).

### 5.3 Builds (all exit 0, from this worktree)

| build | jobs | result |
|---|---|---|
| `lake build NearSpecV3` (`spec/lean/v3`) | 103 | success |
| `lake build NearSpecV3.ChunkValidationD1Out` (`spec/lean/v3`) | 35 | success |
| `lake build nearspec-v3-check-d1` (`spec/lean/v3`) | 204 | success |
| `lake build nearspec-v3-check-d3-out` (`oracle/wasm-d3/lean`) | 125 | success |
| `lake build ZkFormal.NearV3.D1.F1.CheckD1` (`zk-formal`) | 1,816 | success |
| `lake build ZkFormal.NearV3.D1.Phase2` (`zk-formal`) | 3,157 | success |

The last two matter because `ZkFormal.NearV3.D1.F1.CheckD1`'s `checkD1_witnessOfD1` does
`unfold NearSpecV3.checkD1`; the projection form broke that proof's `simp only` step, and the patch is
two lines: unfold `checkD1CoreObs` as well and add `Except.map.eq_def` to the simp set. That module's
theorem statement is unchanged.

### 5.4 Existing modes unaffected

Spot checks with `tools/d3/check_outputs.py` after the driver change:

| mode | corpus | sample | result |
|---|---|---|---|
| `--d2` | `d2corpus.v2` / `d2` | 40 | 40 accept, 0 mismatches, 0 failures |
| default (D3) | `d3c9` / `d3` | 40 | 40 accept, 0 mismatches, 0 failures |

`--d2` and the default D3 path are byte-identical code paths to before; the only change is the mode
dispatch, which selects `checkD1CoreOut` only under `--d1`.

## 6. Axiom output (verbatim)

From `lake env lean ../../../docs/evidence/lean-chunk-final-outputs/D1Axioms.lean` in `spec/lean/v3`:

```
'NearSpecV3.checkD1CoreObs_agrees' depends on axioms: [propext, Quot.sound]
'NearSpecV3.checkD1CoreObs_reject' depends on axioms: [propext, Quot.sound]
'NearSpecV3.checkD1CoreOut_agrees' depends on axioms: [propext, Quot.sound]
'NearSpecV3.checkD1CoreOut_reject' depends on axioms: [propext, Quot.sound]
'NearSpecV3.checkD1_accepted_observable_computed' depends on axioms: [propext, Quot.sound]
'NearSpecV3.checkD1_ok_iff_coreOut_ok' depends on axioms: [propext, Quot.sound]
'NearSpecV3.checkD1_error_iff_coreOut_error' depends on axioms: [propext, Quot.sound]
'NearSpecV3.d1Outputs_fields' depends on axioms: [propext]
'NearSpecV3.d1Outputs_not_computed' depends on axioms: [propext]
'NearSpecV3.agreesWithHeaderD1_refl' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`checkD1CoreObs_agrees`, `checkD1CoreObs_reject` are declared in `ChunkValidationD1.lean`; the rest in
`ChunkValidationD1Out.lean`. `sorryAx` appears in none.

## 7. Limits — what this does and does not establish

1. **It does not prove acceptance implies header agreement as a standalone theorem.** The emitted
   record is `d1Outputs` applied to the comparison's operands, and `d1Outputs_fields` proves each field
   is its computed argument, but bridging "the do-block returned `.ok o`" to "`o = d1Outputs …`" would
   require inverting the whole pipeline (decoders, receipt shuffles, the implicit loop). D2's module
   makes the same choice. The *evidence* for header agreement is therefore measured (§2), not proved.
2. **Rejected cases have no numeric diff.** The error string names the field that disagreed; the
   computed value that differed is not emitted on a failing path. 37,437 rejected and 4,522
   out-of-domain cases are verdict-only evidence here. The D3 mutant study
   (`check_output_mutants.py`) is the causal evidence that a wrong field is caught for the right
   reason; the equivalent D1 mutant study is not run here, though the corpus's 37,437 rejects include
   header-field mutants whose reasons match the field.
3. **Agreement is with the claim header, not with a live nearcore recomputation.** The header's values
   were produced by nearcore; agreeing with them is agreeing with nearcore *on those fields*. That is
   what `checkD1` already established; this work makes it visible. It is not an independent
   recomputation, and it does not establish the computed transition equals a validator's.
4. **No widening.** `checkD1CoreOut` accepts exactly what `checkD1` accepts; the corpus's verdict counts
   are unchanged from the signed driver's (§5).
5. **`wasmGas = 0` is honest, not evidence.** D1 executes no WASM. The field exists so one JSON shape
   serves all three domains; it is not a measurement of D1 execution.
6. **`proposals = []` / `bwRequests = []` are the computed (empty) lists.** D1's comparison only checks
   that the header's lists are empty; it computes no proposal or bandwidth-request list. The emitted
   empty lists are therefore honest for D1 but are not an independent computation that could disagree.
7. **The `zk-formal` proof that unfolds `checkD1` was re-verified.** `ZkFormal.NearV3.D1.F1.CheckD1`'s
   `checkD1_witnessOfD1` does `unfold NearSpecV3.checkD1`, so the projection form touches it. See §5 for
   the build result; that module's proof needed no edit.
