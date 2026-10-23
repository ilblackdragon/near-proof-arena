# The join: `join_additive` retired, `compose_pv86` proved

Lane: `pq-join-compose`.  Date 2026-10-22.  Base `229518416`, plus this lane's two commits.

Evidence classes: **[K]** kernel-checked here, **[M]** measured here, **[S]** stated, **[O]** open.

## The defect, stated exactly

`zk-formal/ZkFormal/PQ/StatePort/JoinFold.lean:71-84` declared

```
def JoinStmt : Prop :=
  ∀ B cb w cfg resp runs, RelD1a B cb w → (∀ r ∈ runs, ∃ … WasmRunStmt …) → RelD1a B cb w

theorem join_additive : JoinStmt := by
  intro B cb w cfg resp runs hrel _hruns
  exact hrel
```

The conclusion is the premise.  The `runs` hypothesis — "every `FunctionCall` in the witness is
backed by a Wasm run" — is bound and **never used** (`_hruns`).  The statement therefore cannot be
the D3 join, and no strengthening of it can be, because its conclusion type is `RelD1a`.

The reason is structural and lives in the decoders, not in the proof:

| claim | cite |
|---|---|
| D1 transactions reject every action tag but `Transfer(3)` | `NearSpecV3/TxD1.lean:97` |
| D1 receipts reject every action tag but `Transfer(3)` | `NearSpec/Codec.lean:75` |
| `checkD1` rejects every contract code blob (`w.no_code`) | `NearSpecV3/ChunkValidationD1.lean:63` |

A `RelD1a` witness thus contains **no** `FunctionCall`, so "every call is backed" is vacuously true
there.  `RelD3`, by contrast, is `checkD2Core (d3Hooks …) true …` on the **D2** witness
(`ChunkValidationD2.decodeStateWitnessD2`), which admits any action list and admits code blobs.

## What was done about it

**1. The defect is now a theorem, not a comment.**  `Join/Compose.lean` proves

* `joinStmt_conclusion_is_premise` — the statement's conclusion is its premise, so the backing
  hypothesis cannot matter;
* `joinStmt_backing_is_erasable` — the same conclusion follows without the backing hypothesis at
  all.  An erasable hypothesis is the definition of dead weight.

`JoinStmt` and `join_additive` are kept (the audit file `zk-formal/test/AuditPQStatePort.lean`
`#check`s and `#print axioms`es them) but their docstrings now say RETIRED / vacuity witness and
point at the replacement.  Nothing is deleted that a report cites; nothing can be mistaken for the
join either.

**2. The honest join is proved.**  `Join/Compose.lean` gives two new theorems [K]:

| theorem | statement |
|---|---|
| `join_obligation_is_call_arm` | if `sa` matches `d3Hooks` on `.fcall`, then `patchArm cfg sa = d3Hooks cfg` |
| `join_pipeline_eq` | with `.fcall` agreement, `checkD2Core (patchArm cfg sa) … = checkD2Core (d3Hooks cfg) …` |
| `compose_pv86` | `hagree` + `hstate` ⇒ `NearSpecV3.D3.RelD3 cb w` |
| `compose_is_pv86_only` | `RelD3 cb w ↔ checkD2Core (d3Hooks pv86) … = .ok ()` |

All four are kernel-checked with axioms `{propext, Classical.choice, Quot.sound}`.

`compose_pv86` is non-vacuous in the way the goal requires: its **conclusion is `RelD3`**, and its
premises are real statements about the chunk —

* `hagree : ∀ c st ar m a g d, sa c st ar (.fcall m a g d) = d3Hooks pv86 .functionCall c st ar (.fcall m a g d)`
  — the per-call agreement between the state proof's answer function and the D3 spec's;
* `hstate : checkD2Core (patchArm pv86 sa) true cb w (some gAlpha) = .ok ()` — the state pipeline's
  verdict on the chunk's **own witness bytes**.

Both are consumed.  Neither is a restatement of the conclusion.

**3. Why there is no `cfg`-general form.**  `checkD3` is fixed at `Wasm.pv86`
(`D3/FunctionCall.lean:400-401`), so a join concluding `RelD3` must be at `pv86`.  A
protocol-parametric `compose_cfg` would conclude `checkD2Core (d3Hooks cfg) …`, which is *not*
`RelD3`.  `compose_is_pv86_only` records this so a future pass does not try to generalise it and
quietly change the relation being proved.

## The structural result the join rests on [K]

`patchArm_eq_d3` (`Join/Fold.lean:103`) is the whole-chunk rewrite: `ActionHooks` is a one-field
structure (`D2/Actions.lean:73-75`), so a hook *is* its `functionCall`, and the pipeline reads it at
exactly one place — `applyAction`'s `.fcall` arm.  Every other layer (receipts, queues,
transactions, yield timeouts, the scheduler, the header comparison) is untouched by the patch.  So
the join obligation really is only the call arm, and `join_obligation_is_call_arm` states that as a
theorem rather than as prose.  `checkD2Core_patch` is then a single `rw`, not a ~900 s per-layer
induction over the 100,000-step drain.

## What is still open [O]

`compose_pv86` takes `hagree` and `hstate` as hypotheses.  Neither is discharged here:

* **`hagree`** needs the HOST chip plus the `runCall`/`d3Hooks` correspondence
  (`JOIN-INTERFACE.md` §2-§5).  The Wasm side's answer function must be shown to equal the spec's
  on `.fcall`, which is where the host-response wire and the gas/register agreement enter.
* **`hstate`** needs the D2 witness carried by the chunk to be the one the state pipeline accepts.
  `Coverage.coverage_pv86` (`:146`) and `Fold.relD3_of_checkD2Core` (`:211`) both leave this open,
  and the `Statement.Compose` definition (`Join/Statement.lean:641-642`) is still stated-not-proved
  in its `Joint` form.

So the join is **bounded, named and reduced to two hypotheses**, each of which is a statement about
chunk bytes rather than a reflexive restatement.  It is not closed.  What changed is that the
vacuous statement can no longer be cited as if it were.

## Also relevant to "chunk → preparation"

The D3 artifact path (`docs/logs/d3-artifact-soundness-2026-10-22.md`) already connects acceptance to
`RelD3` for the shipped binary, and its `Read.check` genuinely executes the whole `checkD3` including
`Wasm.prepare`.  That is the *executable* chunk→preparation link.  The join above is the *proof-level*
link for a two-proof architecture (state proof + Wasm proof) whose halves are still being built.  The
two are independent and neither substitutes for the other: the artifact path has a real binary and a
real preparation run but no succinctness; the join path has the decomposition but neither half's AIR.
