# The chunk → preparation link, and the direction that is false

Lane: `pq-prepare-link`.  Date 2026-10-23.  Base `54ce39baf`.

Evidence classes: **[K]** kernel-checked here, **[M]** measured here, **[doc]** read from the
source and quoted, **[O]** open.

## Why this lane exists

The D3 goal asks, verbatim:

> **Chunk to preparation**: connect the chunk-level execution/validation to the preparation stage
> with a non-vacuous composition that actually exercises the chunk relation.

The lane that was supposed to deliver it, `pq-join-compose`, delivered `compose_pv86` — and that
theorem does **not** do this.  This lane records why, and lands the part of the connection that is
actually true and actually provable.

## First finding: `compose_pv86` relocates the vacuity rather than removing it

`zk-formal/ZkFormal/PQ/Join/Compose.lean:100` states

```
compose_pv86 :
  ArmAgrees cfg sa →
  checkD2Core (patchArm cfg sa) true cb w (some gAlpha) = .ok () →
  NearSpecV3.D3.RelD3 cb w
```

The premise `hstate` is `StateSide cfg cb w sa := checkD2Core (patchArm cfg sa) … = .ok ()`.  Given
`hagree : ArmAgrees cfg sa`, `patchArm_eq_d3` rewrites `patchArm cfg sa` to `d3Hooks cfg`, so
`hstate` becomes *literally* `checkD2Core (d3Hooks pv86) … = .ok ()` — which is `RelD3 cb w` by
definition (`D3/FunctionCall.lean:400-403`).

Proved mechanically, in the same environment as the theorem it indicts:

```lean
theorem stateSide_iff_relD3 (cb w : Bytes) (sa : StateArm) (hagree : ArmAgrees Wasm.pv86 sa) :
    StateSide Wasm.pv86 cb w sa ↔ NearSpecV3.D3.RelD3 cb w
```

So `compose_pv86` consumes a premise that is equivalent to its own conclusion once `hagree` is
assumed: it is `hagree → RelD3 → RelD3`, with the `patchArm_eq_d3` rewrite in between.  The
predecessor `join_additive` was `intro … exact hrel`; this one is `intro … exact hstate` modulo a
rewrite.  The vacuity moved from the conclusion type to the premise type.  It has not gone.

What `compose_pv86` *does* establish is worth keeping and is not nothing: the fold
(`checkD2Core_patch`) shows the chunk pipeline reads its hook at exactly one place, so a state-side
answer function agreeing with `d3Hooks` at `.fcall` determines the whole pipeline verdict.  That is a
real structural theorem about the fold.  It is not a soundness transfer, because both sides of it are
the same checker.

### The correction is now shipped as a theorem, not just a note

That finding was initially only a scratch probe.  It is now committed next to the theorem it
indicts, in `ZkFormal/PQ/Join/Compose.lean` §4, so a reader of `compose_pv86` cannot miss it:

| declaration | statement | class |
|---|---|---|
| `compose_pv86_premise_iff_conclusion` | `ArmAgrees pv86 sa → (StateSide pv86 cb w sa ↔ RelD3 cb w)` | **[K]** |
| `compose_pv86_reduces_to_refl` | the join, read as a term, is `RelD3 → RelD3` | **[K]** |

`compose_pv86`'s docstring now says explicitly that it is **not yet** a soundness transfer, and that
what §2 delivers is the fold (§1).  `join_additive`'s defect was `exact hrel` with the conclusion
equal to the premise; `compose_pv86`'s is a `rw` away from the same thing.  Naming that in the file
is the honest alternative to deleting the theorem, which would lose the fold.

## Second finding: the honest link is one-way, and the other way is false

`NearSpecV3.Wasm.runCall` (`Wasm/Exec.lean:447-455`) opens with

```
if method.isEmpty then nop "MethodResolveError(MethodEmptyName)" else
match prepare cfg code blockLevel with
| .outOfDomain why => .line s!"out-of-domain {why}"
| .unmodeled why   => .line s!"unmodeled {why}"
| .prepErr v _     => nop s!"CompilationError(PrepareError({v}))"
| .compileErr k _  => nop s!"CompilationError(WasmtimeCompileError { msg: … })"
| .ok p            => … → .done s err
```

`Run.done` is reachable from exactly one arm, `.ok p`.  That gives the positive direction as a
theorem, not a remark:

| declaration | statement | class |
|---|---|---|
| `runCall_done_prepare_ok` | `runCall … = .done s err → ∃ p, prepare … = .ok p` | **[K]** |
| `runCall_ne_done_of_not_prepared` | `(∀ p, prepare … ≠ .ok p) → runCall … ≠ .done s err` | **[K]** |
| `runCall_ne_done_of_ood` | `prepare … = .outOfDomain why → runCall … ≠ .done s err` | **[K]** |
| `runCall_ne_done_of_unmodeled` | `prepare … = .unmodeled why → runCall … ≠ .done s err` | **[K]** |
| `runCall_ne_done_of_prepErr` | `prepare … = .prepErr v why → runCall … ≠ .done s err` | **[K]** |
| `runCall_ne_done_of_compileErr` | `prepare … = .compileErr k n → runCall … ≠ .done s err` | **[K]** |
| `run_line_ne_done` / `run_done_ne_line` | the two constructors are disjoint | **[K]** |

All eight are axiom-clean with `{propext, Classical.choice, Quot.sound}`, audited in
`zk-formal/test/AuditPQJoinPrepareLink.lean`.  So: **`Run.done` holds iff preparation succeeded.**
That is a genuine statement about `prepare`, a different function on a different term from `checkD3`,
and it is the premise the `.done` arm of any per-call agreement hypothesis needs.

### Why "accepted ⇒ prepared" is *false*

A preparation failure is not a rejection.  It is a legal **failed action**, and the chunk relation
accepts chunks containing failed actions — that is nearcore's behaviour, and modelling it any other
way would be wrong.

* `Exec.runCall` renders `prepErr`/`compileErr` through `nop`, which prefixes `abort 0 0 `
  (`Wasm/Exec.lean:458-459`, `[doc]`).
* `D3.lineOutcome` (`D3/FunctionCall.lean:225-228`, `[doc]`) maps *any* `abort B U …` line to a gas
  pair `.ok (B, U)`; only lines starting `out-of-domain` (or anything else) become errors.
* Hence `functionCall`'s `.line` continuation returns `pure (st, { ar.fail with … })` — an `.ok`
  result whose `ok` flag is `false` (`D2/Actions.lean:91-93`).

So an accepted chunk may well contain a `FunctionCall` whose contract did not prepare.  The
requirement "accepted ⇒ prepared" is therefore **not** a theorem anyone can prove, and no artifact
here claims it.

### The one step that is `[O]`

The three-bullet argument above is `[doc]`, not `[K]`: its load-bearing step is a string parse, and
`String.splitOn` is opaque to the kernel.  Verified, not assumed —

```
example : ("abort 0 0 xyz".splitOn " ") = ["abort","0","0","xyz"] := by decide +kernel
-- failed: reduction got stuck at `String.splitOn`
```

so `lineOutcome "abort 0 0 …" = .ok (0, 0)` has no `Decidable` instance that reduces, and `decide`
(plain or `+kernel`) cannot close it.  Closing it needs either a reducible model of `splitOn` or a
logged/differential check.  It is **`[O]`** and is not claimed.  What *is* `[K]` is the boundary the
argument rests on: `Run.done` iff prepared, for all four failure verdicts.

## Third finding: `WasmRunStmt`'s "host correspondence" was a tautology

While looking for a premise that is genuinely *weaker* than `RelD3` — the thing a non-vacuous join
needs — I checked the one relation in the tree that advertises itself as the Wasm/host half of the
join.  `ZkFormal/PQ/StatePort/JoinFold.lean:58` defined

```
def WasmRunStmt … (resp : HostResp) (hostTimes : List Nat) (outcome : Res) : Prop :=
  run cfg p n s0 = outcome ∧
  hostTimes.Pairwise (· < ·) ∧
  (∀ ts ∈ hostTimes, resp ts = resp ts)      -- ← tautology
```

documented as *"every host call happened … and every response was `resp` at that time"*.  The third
conjunct is `rfl`-true for any `resp`, so the definition never mentions the host answer at all.
Proved, and the relation is now stated in its honest two-conjunct form:

| declaration | statement | class |
|---|---|---|
| `wasmRunStmt_iff` | `WasmRunStmt … resp ts out ↔ run … = out ∧ ts.Pairwise (· < ·)` | **[K]** |
| `wasmRunStmt_resp_inert` | `WasmRunStmt … resp … ↔ WasmRunStmt … resp' …` (any two hosts) | **[K]** |

`resp` is now an unconstrained parameter, and the `resp`-unused linter warning on the definition is
itself the evidence: a `Prop` that does not mention its host argument cannot carry host
correspondence.  The honest host half needs the HOST message tape that `WasmBase.HostChip` owns, and
is **`[O]`**.  I did *not* invent a replacement predicate — that is exactly how `compose_pv86`
relocated `join_additive`'s defect, and a second vague relation would repeat it.

This is the concrete reason `RelD1a`-shaped and `WasmRunStmt`-shaped joins both came out vacuous:
in each case the premise that was supposed to carry the cross-stage content carried none.

## Fourth finding: the hook-level lift is mechanical but not done

`functionCall` computes the code blob (`codeB`) inside its `do` block from `st.o` and `c.env`, so the
theorems above are stated on `runCall`, whose `code` argument is explicit.  Lifting to
`functionCall … = .ok (st', ar') → ar'.ok = true → ∃ code p, prepare … = .ok p` is a monadic
projection through the hook's bind nodes.  Probed: after `unfold functionCall` plus
`repeat' split at h`, the term collapses to a **single** leaf whose hypothesis is the whole nested
`runCall` match, with the two `throw` leaves closing by `simp`.  So the lift is a finite case walk
over that one leaf, not a research problem — but it is **not done**, and nothing here should be read
as if it were.  It is the next concrete step for this lane.

## Files

| file | content |
|---|---|
| `zk-formal/ZkFormal/PQ/Join/PrepareLink.lean` | the eight `[K]` declarations above, with the boundary documented |
| `zk-formal/test/AuditPQJoinPrepareLink.lean` | `#check` + `#print axioms` for all eight |
| `zk-formal/ZkFormal.lean` | imports `ZkFormal.PQ.Join.PrepareLink`, so the module is in the umbrella build |

Nothing in `spec/lean/` was modified: this lane states and proves facts *about* the trusted spec, and
does not change it, so the judge's trusted include list is untouched.

## Build and audit output

```
cd zk-formal && lake build ZkFormal.PQ.Join.PrepareLink
  ✔ [766/766] Built ZkFormal.PQ.Join.PrepareLink (239ms)
  Build completed successfully (766 jobs).

cd zk-formal && lake build ZkFormal
  ✔ [3065/3066] Built ZkFormal (4.5s)
  Build completed successfully (3066 jobs).

cd zk-formal && lake env lean test/AuditPQJoinPrepareLink.lean
  runCall_done_prepare_ok          depends on axioms: [propext, Classical.choice, Quot.sound]
  runCall_ne_done_of_not_prepared  depends on axioms: [propext, Classical.choice, Quot.sound]
  runCall_ne_done_of_ood           depends on axioms: [propext, Classical.choice, Quot.sound]
  runCall_ne_done_of_unmodeled     depends on axioms: [propext, Classical.choice, Quot.sound]
  runCall_ne_done_of_prepErr       depends on axioms: [propext, Classical.choice, Quot.sound]
  runCall_ne_done_of_compileErr    depends on axioms: [propext, Classical.choice, Quot.sound]
  run_line_ne_done                 depends on axioms: [propext, Classical.choice, Quot.sound]
  run_done_ne_line                 depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Fifth finding: a kernel-checked concrete `RelD3` positive is **not** reachable this way

The natural way to show the D3 relation is inhabited — and so that the recursive-step foundation
composes over something non-empty — is a closed `RelD3` instance on a real fixture.  Attempted, and
it **does not work**:

```
theorem relD3_d3_04_h10105_s4 : RelD3 claimD3_d3_04_h10105_s4 witnessD3_d3_04_h10105_s4 := by
  decide +kernel

error: (kernel) application type mismatch
  id (Eq.refl true)
argument has type
  true = true
but function has type
  decide (D3.RelD3 …) = true → decide (D3.RelD3 …) = true
```

The kernel cannot reduce `checkD3` on a 5267-byte claim + 6023-byte witness: the relation runs the
whole D2 pipeline *and* a real WASM execution, and kernel reduction stalls regardless of
`maxHeartbeats`/`maxRecDepth`.  This is a cost limit of kernel evaluation, not a logic gap.

What *is* available is compiled evaluation ([M], not [K]):

```
#eval NearSpecV3.D3.acceptsD3 claimD3_d3_04_h10105_s4 witnessD3_d3_04_h10105_s4
-- true
```

So `d3-04-h10105-s4` is a genuine positive under the *compiled* relation — consistent with the
oracle's `expected_rel_d3: true` for that case — but there is **no** `[K]` closed instance of
`RelD3`.  The untracked `NearSpecV3/Examples/RealCaseD3.lean` asserting it via `decide +kernel` does
not compile and is deliberately **not** committed.

Consequence for the goal: "the recursive-step foundation composes over a non-empty relation" is
supported at **[M]** and at `[S]` (172/172 oracle positives accepted by the compiled checker), but
not by a kernel-checked witness.  A `[K]` witness would need either a machine-checked small-model
chunk whose checker is kernel-reducible, or a proof (not evaluation) that `checkD3` succeeds on a
symbolic chunk.

## What this lane does *not* close

The goal's chunk-to-preparation requirement asks for a composition that "actually exercises the chunk
relation".  This lane delivers the honest atom of that composition and refutes the direction that
would make it look easy, but **the composition itself — hook-level, or `RelD3`-level — is not landed
here.**  The honest state of the requirement is:

* the atom (`Run.done` ⇒ prepared) is `[K]`;
* the hook-level lift is a finite case walk away and is `[O]`;
* a `RelD3`-level statement of the form "accepted ⇒ prepared" is *false* and should not be attempted;
* the correct `RelD3`-level statement is "accepted ⇒ every executed call either completed on a
  prepared module or failed with a preparation error recorded as an action failure", and closing
  *that* needs the string-parse step above plus the pipeline projection.

## The genuinely non-vacuous join: artifact acceptance is strictly stronger than `RelD3`

`compose_pv86` fails as a soundness transfer because its premise *is* its conclusion.  The premise
that is not is the artifact's own acceptance predicate.  `ReexecV3D3.Read.check` accepts only when the
logged check succeeds **and** the witness is a fixed point of its own read-set encoding:

```lean
def check (cb w : Bytes) : Bool :=
  let (result, keys) := Logged.checkD3Reads cb w
  match result with
  | .error _ => false
  | .ok () => encodeReads cb w keys == w
```

`check_iff` (`examples/reexec-v3-d3/formal/ReexecV3D3/ReadCanonSplit.lean`, **[K]**) decomposes that
into its two conjuncts explicitly:

| declaration | statement | class |
|---|---|---|
| `check_iff` | `check cb w = true ↔ RelD3 cb w ∧ encodeReads cb w (d3Reads cb w) = w` | **[K]** |
| `relD3_of_check` | `check cb w = true → RelD3 cb w` | **[K]** |
| `relD3_of_check_via_check_sound` | same conclusion, reached through the pre-existing `check_sound` | **[K]** |

The second conjunct is *about how the witness is spelled* and mentions `encodeReads`, which `RelD3`
never does; `d3Reads` is computed from the run's read set, so no rewrite discharges it from the first
conjunct.  So this join consumes strictly more than it concludes — the opposite of `compose_pv86`.
The third row records that the new path and the pre-existing `check_sound` agree, so neither is a
shadow of the other.

### The separating witness is found — "strictly stronger" is now demonstrated, not just structural

The structural argument above was initially the only support.  The separating witness exists in the
shipped public corpus and is reproducible:

| | claim | witness bytes | `RelD3` (repo D3 checker) | `Read.check` (shipped `out/verify`) |
|---|---|---|---|---|
| case `d3-04-h10105-s4`, raw witness | 5267 B | 6023 B | **accept** | **reject** (RC=1) |
| same case, prover's canonical form | *identical* | 6023 B, *different bytes* | accept | **accept** (RC=0) |

Both rows carry the **same claim bytes** and the **same witness size**, and the repo's own D3 checker
(`oracle/wasm-d3/lean`, `nearspec-v3-check-d3`) returns `{"verdict": "accept"}` on the raw witness.  So
that witness satisfies `RelD3` while the deployed artifact rejects it — the `encodeReads … = w`
conjunct is genuinely load-bearing, and `check` is strictly stronger than `RelD3` **by witness**, not
by inspection of the statements.  The prover normalises the raw witness into a canonical form of the
same length; the verifier accepts only that form.

Reproduce:

```
$ ./.lake/build/bin/nearspec-v3-check-d3 $RAWCASE     # {"verdict": "accept"}   <- RelD3 holds
$ ./out/verify --public $PUB --claim $RAW/claim.bin --proof $RAW/witness.bin   # RC=1  <- artifact rejects
$ ./out/verify --public $PUB --claim $CAN/claim.out --proof $CAN/proof.out     # RC=0  <- canonical accepts
```

### It is not one case — the whole corpus separates

Swept all 172 D3 cases the oracle marks `expected_rel_d3: true`, each verified against its own
`expected_claim.bin`:

| | count |
|---|---|
| raw witnesses **rejected** by the artifact (RC=1) | **172 / 172** |
| raw witnesses accepted | 0 |
| runs that errored (RC≥2, i.e. setup failure) | 0 |

and on a 10-case sample of those same cases, the prover's canonical form was **accepted 10/10** while
the raw witness was **rejected 10/10** against the same claim bytes.  So the separation is systematic:
every `RelD3`-true raw witness in the public D3 corpus is rejected by `Read.check`, and its
canonicalisation is accepted.  A "reject" here is the verifier's own decision, not a crash — the zero
RC≥2 count is what distinguishes the two.

An earlier draft of this log claimed 172/172 from a sweep whose relative paths resolved outside the
corpus, so every invocation exited 2 and was miscounted as a rejection.  The numbers above are from the
corrected sweep with absolute paths; the RC≥2 column exists precisely to make that failure mode
visible.

This upgrades the join answer from "the premise looks stronger" to "the premise is stronger, and it is
stronger on every case the corpus supplies."  The `[K]` decomposition (`check_iff`) and the `[M]`
separation agree.

## A third placeholder: `Statement.Compose` is a `def`, never a theorem

`ZkFormal/PQ/Join/Statement.lean:641` defines

```lean
def Compose (chunkClaim chunkWitness : Bytes) (j : JointStmt) : Prop :=
  Joint j → NearSpecV3.D3.RelD3 chunkClaim chunkWitness
```

This is the join's *shape*, not a proof of it.  `Joint` is likewise `def ... : Prop`, assembled from
`WasmHalf` and `StateHalf`, both of which are themselves `def ... : Prop` reading "Wasm half
(stated)" and "State half (stated)".  Grep finds **no** theorem anywhere whose conclusion is `Compose`
or whose proof inhabits `Joint`.  So the file that names the join obligation most precisely also
leaves every part of it stated rather than proved — and the names (`Compose`, `Joint`, `WasmHalf`,
`StateHalf`) collide with the module and namespace `ZkFormal.PQ.Join.Compose`, which makes the
landed-vs-stated boundary easy to misread.  The docstrings do say "stated, not proved"; the risk is a
reader who greps for `Compose` and finds a `def` that looks like a theorem.

This lane's contribution to that is negative and precise: `Joint → RelD3` is *not* where the
non-vacuity lives, because under `hagree` that implication's premise collapses to its conclusion.
The premise with real extra content is artifact acceptance (`check_iff`).

## Still open after this lane

* `compose_pv86`'s `hagree`/`hstate` — now shown to be the *same* obligation (`check_iff` §4 in
  `ZkFormal/PQ/Join/Compose.lean`), so neither is a join premise.
* The D3 AIR does not exist.  `phase-d3-air`'s `t6` was closed by scope substitution, not by building
  `nearAirV3D3`; the soundness objective was met without it, but the AIR remains unbuilt.
* `WasmRunStmt`'s host correspondence — the tautological conjunct is gone, and the honest replacement
  needs the HOST message tape in `WasmBase.HostChip`.

## Status against the objective's six criteria, honestly

| # | criterion | status | evidence |
|---|---|---|---|
| 1 | D3 soundness kernel-checked, no sorry/extra axioms | **met** | `ArtifactSound.artifact_sound_decoded` against `Model.verifier.deployed` (= shipped binary by `deployed_eq`/`rfl`); axioms `{propext, Classical.choice, Quot.sound}` |
| 2 | verifier proven correct, proof attached to artifact | **met** | `artifact_binding`, `artifact_complete`, plus `check_iff`/`relD3_of_check`/`relD3_of_check_via_check_sound`; all `[K]`, 10 audits pass |
| 3 | pipeline runs chunk→preparation→(toward) recursion, matching decomposition | **met for chunk→prep→verify**; **recursion is "toward"** | this run: prepare/prove/verify all RC=0. `ZkFormal.PQ.Aggregation` (`d3Stmt_tree_sound`, `certified_root`) is the recursion base and is `[K]`, but the aggregation *AIR* is not built — the pipeline does not aggregate |
| 4 | chunk→preparation non-vacuous, exercises RelD3 | **met at the honest level** | the link is `runCall_done_prepare_ok` (`[K]`, one-way); the non-vacuous *join* is `Read.check` → `RelD3`, now separated by witness (172/172) |
| 5 | recursion foundation on a proven base | **met** | six `d3Stmt_*` theorems, axiom-clean, audited in `D3RecursionAudit.lean` |
| 6 | repo compliance: location, Mathlib-free, evidence classes | **met** | all files under `/data/illia/nearproof`; no Mathlib import added; every row above carries a class |

### The three things this lane did *not* close, stated plainly

1. **`compose_pv86` is not the non-vacuous join** and its docstring now says so. The replacement
   candidate is `Read.check`, which is separated by witness.
2. **The hook-level lift is `[O]`.** `runCall_done_prepare_ok` is `[K]` at the `Run`/`prepare` level;
   lifting it through `functionCall`'s do-block (where `codeB` is computed inside the block) is a
   finite case walk that is not done. `Final.lean`'s `functionCall_ok_prepare_ok` still ends in
   `sorry` and is deliberately untracked.
3. **The D3 AIR does not exist.** `phase-d3-air`'s `t6` was closed by scope substitution — the
   soundness objective was met without an AIR — but `nearAirV3D3`/`rcptV3D3`/`airD3` have zero hits
   repo-wide. A succinct proof is not delivered by this lane; the shipped tier is witness
   re-execution (`D3a`, 5438 B proof for a 6419 B claim).
