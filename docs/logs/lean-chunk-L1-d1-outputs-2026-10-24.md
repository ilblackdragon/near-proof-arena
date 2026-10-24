# L1 (d1-outputs) — D1 emits its computed outputs, with proof that the signed relation is unchanged

| field | value |
|---|---|
| owner | L1 lane (`d1-output-agreement` sub-lane) |
| worktree | `/data/illia/nearproof-wt/lean-d1-outputs` |
| branch | `work/d1-output-agreement` |
| base commit | `5491f7f03d2c1521e62c6407d8df52afad4471df` (`5491f7f03`, "docs: record the output-agreement evidence (result, method, limits)") |
| tip | see §12 (recorded on commit; base + this lane's commit) |
| inventory IDs | none claimed. This closes the D1 row of the output-evidence gap in `docs/evidence/lean-chunk-final-outputs/RESULT.md`, not an inventory item |
| evidence | `docs/evidence/lean-chunk-final-outputs/d1-outputs.md`, `D1Axioms.lean`, `full-run2.log` results in §6 |

## 1. The gap this closes

`docs/evidence/lean-chunk-final-outputs/RESULT.md` established, for D2 and D3, that the checker computes
the consensus outputs and returns them (`checkD2CoreObs`, `checkD2CoreOut`), with whole-corpus agreement
measured (D2: 67,384 cases, 0 mismatches; D3: four corpora, 0 mismatches). D1 had **verdict** agreement
(53,048/53,048, 0 disagreements) but **zero output evidence**: `checkD1` returned `Except String Unit`
and threw its computed outputs away, so its ~13-value comparison block at
`ChunkValidationD1.lean:170-189` (base numbering) never emitted anything.

D1 was the remaining hole. This lane closes it additively.

## 2. Changed declarations, with precise statements

### 2.1 `spec/lean/v3/NearSpecV3/ChunkValidationD1.lean`

New declarations:

```lean
def d1Outputs (root : Bytes) (outcomes : List OutD1) (gasBurnt tokensBurnt : Nat)
    (layout : Layout) (outgoing : List Receipt) (txRoot : Bytes) (emr : Bytes) (len : Nat)
    (congestion : Congestion) : Observable

def checkD1CoreObs (claimBytes witnessBytes : Bytes) : Except String Observable

theorem checkD1CoreObs_agrees (cb wb : Bytes) :
    (∃ o, checkD1CoreObs cb wb = .ok o) ↔ checkD1 cb wb = .ok ()

theorem checkD1CoreObs_reject (cb wb : Bytes) (e : String)
    (h : checkD1CoreObs cb wb = .error e) : checkD1 cb wb = .error e
```

Changed declaration (**the only behavioural change**):

```lean
def checkD1 (claimBytes witnessBytes : Bytes) : Except String Unit :=
  (checkD1CoreObs claimBytes witnessBytes).map fun _ => ()
```

Before: `def checkD1 … := do … end`, returning `Unit` from the pipeline. After: the pipeline body moved
verbatim to `checkD1CoreObs` (same steps, same order, same error strings), and `checkD1` is its
projection. `acceptsD1`, `RelD1` and its `Decidable` instance are unchanged and still compile.

`d1Outputs`'s fields are the comparison's operands: `stateRoot := root`,
`outcomeRoot := outcomeRootD1 outcomes`, `gasBurnt := gasBurnt`, `balanceBurnt := tokensBurnt`,
`outgoingReceiptsRoot := outgoingReceiptsRoot layout outgoing`, `txRoot := txRoot`,
`encodedMerkleRoot := emr`, `encodedLength := len`, `congestion := congestion`,
`receiptCount := outgoing.length`, `logs := outcomes.map (·.logs) |>.flatten`; and the three fields D1
does not compute: `proposals := []`, `bwRequests := []`, `wasmGas := 0`.

### 2.2 `spec/lean/v3/NearSpecV3.lean` (root import)

Added `import NearSpecV3.ChunkValidationD1Out` immediately after `ChunkValidationV0`, so the new module
(and its axiom audits) are in the default build target's closure. Verified: a plain `lake build` builds
103 jobs including `ChunkValidationD1Out`. Additive only — no signed statement is reachable from it.

### 2.3 `spec/lean/v3/NearSpecV3/ChunkValidationD1Out.lean` (new module)

```lean
def Observable.agreesWithHeaderD1 (o : Observable) (H : ChunkInner) : Bool

def checkD1CoreOut (claimBytes witnessBytes : Bytes) : Except String Observable

theorem checkD1CoreOut_eq (cb wb : Bytes) : checkD1CoreOut cb wb = checkD1CoreObs cb wb
theorem checkD1CoreOut_agrees (cb wb : Bytes) :
    (∃ o, checkD1CoreOut cb wb = .ok o) ↔ checkD1 cb wb = .ok ()
theorem checkD1CoreOut_reject (cb wb : Bytes) (e : String)
    (h : checkD1CoreOut cb wb = .error e) : checkD1 cb wb = .error e
theorem checkD1_accepted_observable_computed (cb wb : Bytes) (o : Observable)
    (hacc : checkD1CoreOut cb wb = .ok o) : checkD1CoreObs cb wb = .ok o
theorem checkD1_ok_iff_coreOut_ok (cb wb : Bytes) :
    checkD1 cb wb = .ok () ↔ ∃ o, checkD1CoreOut cb wb = .ok o
theorem checkD1_error_iff_coreOut_error (cb wb : Bytes) (e : String) :
    checkD1 cb wb = .error e ↔ checkD1CoreOut cb wb = .error e
theorem agreesWithHeaderD1_refl (H : ChunkInner) :
    ({ … H's own fields, proposals := [], bwRequests := [], logs := [], receiptCount := 0,
       wasmGas := 0 } : Observable).agreesWithHeaderD1 H = true
theorem d1Outputs_fields (… all ten arguments …) :
    (d1Outputs …).stateRoot = root ∧ (d1Outputs …).outcomeRoot = outcomeRootD1 outcomes ∧ … ∧
    (d1Outputs …).receiptCount = outgoing.length
theorem d1Outputs_not_computed (… all ten arguments …) :
    (d1Outputs …).proposals = [] ∧ (d1Outputs …).bwRequests = [] ∧ (d1Outputs …).wasmGas = 0
```

`agreesWithHeaderD1` restates step 3.7's comparison over the emitted record. It covers the eleven checks
that have an `Observable` field. Two checks of the signed block have no field and are **not** in the
predicate: `H.gasLimit == slotB2.gasLimit` (a slot fact, not a chunk output) and
`H.proposedSplit.isNone` (no shard split in D1). That omission is deliberate and documented in the
module docstring; the predicate must not overstate what the record represents.

### 2.4 Axiom footprints (measured, `#print axioms`; allowed set `propext`, `Classical.choice`, `Quot.sound`)

| theorem | axioms |
|---|---|
| `checkD1CoreObs_agrees` | `[propext, Quot.sound]` |
| `checkD1CoreObs_reject` | `[propext, Quot.sound]` |
| `checkD1CoreOut_agrees` | `[propext, Quot.sound]` |
| `checkD1CoreOut_reject` | `[propext, Quot.sound]` |
| `checkD1_accepted_observable_computed` | `[propext, Quot.sound]` |
| `checkD1_ok_iff_coreOut_ok` | `[propext, Quot.sound]` |
| `checkD1_error_iff_coreOut_error` | `[propext, Quot.sound]` |
| `d1Outputs_fields` | `[propext]` |
| `d1Outputs_not_computed` | `[propext]` |
| `agreesWithHeaderD1_refl` | `[propext, Classical.choice, Quot.sound]` |

No `sorryAx`, no new axioms. Verbatim output in the evidence document §6; regenerate with
`lake env lean ../../../docs/evidence/lean-chunk-final-outputs/D1Axioms.lean` from `spec/lean/v3`.

### 2.5 Residual premises (honest limits)

1. **No extraction theorem.** The emitted record is `d1Outputs` applied to the comparison's operands, and
   `d1Outputs_fields` proves each field equals its argument — but bridging "the do-block returned `.ok o`"
   to "`o = d1Outputs …`" needs inverting the whole pipeline (decoders, receipt shuffles, the implicit
   loop). Not attempted; D2's module makes the same choice. Header agreement is therefore *measured*,
   not proved.
2. **No numeric diff on rejected cases.** 37,437 rejects and 4,522 out-of-domain cases emit
   `outputs: null`; their evidence is the verdict and reason string only. The reason names the field, not
   both values.
3. **Agreement is with the claim header.** The header's fields came from nearcore; agreement with them is
   agreement with nearcore on those fields. It is not an independent recomputation, and it does not
   establish the computed transition equals a validator's.
4. **`proposals = []` / `bwRequests = []` are computed-as-empty, not independently computed.** D1's
   comparison only requires the header's lists to be empty; D1 computes no list. The emitted empty lists
   cannot disagree with anything.
5. **`wasmGas = 0` is a constant.** D1 executes no WASM. The field exists so one JSON shape serves all
   three domains.
6. **`--d1` runs the D1 pipeline only.** It does not run D0 or the D1a amendments; a case that is
   `out_of_domain` for D1a but accepted by D1 will appear as `accept` here. That is the signed D1
   relation's answer, which is what this driver reports.

## 3. The proof obligation discharged: `checkD1` definitionally unchanged

The requirement is that the signed relation not move. Two things establish it:

* **By definition.** `checkD1 = (checkD1CoreObs …).map fun _ => ()`, and `Except.map` on `.ok a` is
  `.ok ()`, on `.error e` is `.error e`. So `.ok ()` and `.error e` occur for exactly the same inputs.
  `checkD1CoreObs_agrees` and `checkD1CoreObs_reject` state this and are proved by `unfold`, `rw
  [Except.map.eq_def]`, `cases … <;> simp` — the same script as D2's.
* **On real bytes.** `tools/d3/check_d1_verdict_agreement.py` ran the signed driver and the output driver
  over all 53,048 cases: **0 verdict disagreements, 0 reason-only differences, 0 missing lines**.

The only downstream proof that unfolds `checkD1` is `zk-formal`'s `checkD1_witnessOfD1`
(`ZkFormal/NearV3/D1/F1/CheckD1.lean`). It needed a two-line patch (unfold `checkD1CoreObs` too, add
`Except.map.eq_def` to the simp set); its statement is unchanged and both its target and the whole
`ZkFormal.NearV3.D1.Phase2` build root are green (§4).

## 4. Build and test commands (actual results)

| command | jobs | result |
|---|---|---|
| `cd spec/lean/v3 && lake build NearSpecV3` | 103 | **success** |
| `cd spec/lean/v3 && lake build NearSpecV3.ChunkValidationD1Out` | 35 | **success** |
| `cd spec/lean/v3 && lake build nearspec-v3-check-d1` | 204 | **success** |
| `cd oracle/wasm-d3/lean && lake build nearspec-v3-check-d3-out` | 125 | **success** |
| `cd zk-formal && lake build ZkFormal.NearV3.D1.F1.CheckD1` | 1,816 | **success** |
| `cd zk-formal && lake build ZkFormal.NearV3.D1.Phase2` | 3,157 | **success** |

`spec/lean/v3/.lake` and `oracle/wasm-d3/lean/.lake` were built fresh in this worktree (no cache copied,
no hard links). `zk-formal/.lake` was built fresh as well.

## 5. Actual counts — whole D1 corpus, `--d1`

Corpus `/data/illia/nearproof-deps/corpora/d1run`; families `d1`, `mutants`, `ood`; 20 shards.

| family | cases | accept | reject | out-of-domain | accepted with outputs | field mismatches | missing | failures |
|---|---|---|---|---|---|---|---|---|
| `d1` | 3,394 | 3,394 | 0 | 0 | 3,394 | 0 | 0 | 0 |
| `mutants` | 46,009 | 7,695 | 37,437 | 877 | 7,695 | 0 | 0 | 0 |
| `ood` | 3,645 | 0 | 0 | 3,645 | 0 | 0 | 0 | 0 |
| **total** | **53,048** | **11,089** | **37,437** | **4,522** | **11,089** | **0** | **0** | **0** |

D1-only invariants on all 11,089 accepted cases: `wasmGas = 0`, `bwRequests = []`. No fabricated
D2/D3-only values. Rejected/out-of-domain cases emit `outputs: null` — counted, not failed, as required.

## 6. Failing cases

**None.** 0 field mismatches, 0 missing lines, 0 accepted-with-null-outputs, 0 verdict disagreements on
53,048 cases. The report's `mismatches_by_field` is `{}` and `mismatches` is `[]`.

## 7. Artifact hashes (sha256)

| artifact | sha256 |
|---|---|
| `spec/lean/v3/NearSpecV3/ChunkValidationD1.lean` | `eb1c92ed716fd19c219966a67915272f8bcbf8ec9d7f68584a2de1bb21119c12` |
| `spec/lean/v3/NearSpecV3/ChunkValidationD1Out.lean` | `3027cbca9a12504f42851be3eea36cd67f015460a4c92c1a889169fa0adba500` |
| `oracle/wasm-d3/lean/MainD3Out.lean` | `ad117de4fb3e4a9bc4a21c342403cc89eab8c9bb5a67aeae225b743b379bb6ba` |
| `tools/d3/check_outputs.py` | `642995c1286f953a2ae9126a37860566af8e2d8c8992a27923607384e8c04258` |
| `tools/d3/check_d1_verdict_agreement.py` | `4fd1554d1ad184205eaa04b0e53630c40377b76406d077f6d638780e95e071db` |
| `zk-formal/ZkFormal/NearV3/D1/F1/CheckD1.lean` | `fb2f85cf37700575d418ca7bdb57f464f18d142191b2f3bb40d9335ee135345d` |
| `oracle/wasm-d3/lean/.lake/build/bin/nearspec-v3-check-d3-out` | `9d7944722c3f1a728efca3e8e43d65b023042313099495efb73260eca1efa3df` |
| `spec/lean/v3/.lake/build/bin/nearspec-v3-check-d1` | `61ca196e58354995e7d91f4f492615c9b2ee1290116d2607cb55bd594de7e78e` |

Note: the binary hashes are build products of this worktree and change with the toolchain/cache; the
source hashes are the durable identity. The driver binary's hash is recorded in the evidence document §4.

## 8. What is new in the driver and the checker script

* `oracle/wasm-d3/lean/MainD3Out.lean` — a `Mode` inductive (`d3` default, `d2`, `d1`); `--d1` calls
  `checkD1CoreOut`. The JSON shape is unchanged: `{"case", "verdict", "reason", "outputs"}`. The default
  and `--d2` code paths are the same expressions as before; only the dispatch is new.
* `tools/d3/check_outputs.py` — `--d1` flag, mutually exclusive with `--d2`; `run_driver` takes `d1`;
  the D1-only invariant checks; the report gains `mode` and `d1_invariant_failures`. With neither flag,
  behaviour is byte-identical to before.
* `tools/d3/check_d1_verdict_agreement.py` — new: signed driver vs output driver, case for case.
* `tools/d3/claim_outputs.py` — **unchanged**. Verified against all 3,394 honest D1 claims: 0 decode
  failures. D1 and D2 share the claim / chunk-header wire format.

## 9. Next step

The cheapest useful continuation is the D1 analogue of `tools/d3/check_output_mutants.py`: take honest
D1 base cases and their header-output mutants, require base accept-with-outputs, mutant reject, and the
rejection reason to name *that* field. That would give D1 the causal evidence D3 has (§4 of `RESULT.md`)
and would close limit 2 in §2.5 for the field mutants specifically. It needs a mutant generator over the
D1 corpus; the D3 one is the template.

Second, and larger: a *standalone extraction theorem* (limit 1). The honest way is to split the pipeline
so the comparison block is a named function over the record and the pipeline's return is
`(H, slotGasLimit, o)`, then prove acceptance implies the comparison accepted `o`. That needs the
comparison to be reordered or the RS computation deferred; both touch the reason-order surface, so it is
a design decision, not a mechanical edit.

## 10. Safe-to-edit files

Safe: `spec/lean/v3/NearSpecV3/ChunkValidationD1Out.lean`, `tools/d3/check_outputs.py`,
`tools/d3/check_d1_verdict_agreement.py`, this log, and the evidence document.

**Read the signed surface before editing:** `spec/lean/v3/NearSpecV3/ChunkValidationD1.lean` is the
signed D1 relation's module. `checkD1CoreObs`'s pipeline steps, their order and their error strings are
the signed statement's behaviour — a change there needs the full difftest, not just a build.
`oracle/wasm-d3/lean/MainD3Out.lean` is shared by D2 and D3 evidence; keep the default and `--d2` paths
byte-identical. `zk-formal/ZkFormal/NearV3/D1/F1/CheckD1.lean`'s proof depends on the projection form;
if the projection changes shape again, that proof needs the same treatment.

Do **not** hard-link or copy `.lake` caches into this worktree; the builds here are fresh.

## 11. Rejected alternatives

* **Emitting the header's own fields** (the `Observable.ofChunkInner` approach the D2 lane replaced in
  `a2221c48e`). That would make the report's comparison tautological. Rejected for the same reason D2
  rejected it.
* **A separate duplicate pipeline for D1.** Copying the do-block into a second definition would let the
  two drift and would make the agreement theorem a re-derivation over ~50 lines including receipt
  shuffles and the implicit loop. The projection makes agreement definitional instead.
* **Leaving `checkD1` untouched and putting `checkD1CoreObs` in a separate module.** Not possible: a
  projection must be defined after its source, and `checkD1` lives in the signed module. Keeping the
  signed module's pipeline and adding a duplicate observable one would reintroduce the drift risk.

## 12. Tip commit

Recorded on the commit that carries this log and the evidence document. Run `git log --oneline -2` in
the worktree; the lane commit's parent is `5491f7f03`.
