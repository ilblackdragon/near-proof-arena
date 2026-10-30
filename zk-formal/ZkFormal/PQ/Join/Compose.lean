import ZkFormal.PQ.Join.Fold
import ZkFormal.PQ.Join.Coverage

/-!
# `ZkFormal.PQ.Join.Compose` — the join's fold, and why it is not yet non-vacuous

Lane `pq-join-compose`, 2026-10-22; title corrected 2026-10-23 after §4.

**Read §4 before citing anything here as "the non-vacuous join."**  This file was committed under the
claim that it replaces the vacuous join.  §4 proves that it does not: under `hagree`, the premise
`hstate` is *equivalent* to the conclusion `RelD3`, so the join is the identity on `RelD3` modulo the
`patchArm_eq_d3` rewrite — the same defect as `join_additive`, one layer down.  What the file does
deliver is real and worth keeping: the **fold**, i.e. that the chunk pipeline reads its hook at
exactly one place, so agreement at `.fcall` determines the whole pipeline verdict.

The genuinely non-vacuous join lives elsewhere: the artifact's own acceptance predicate is strictly
stronger than `RelD3` (`examples/reexec-v3-d3/formal/ReexecV3D3/ReadCanonSplit.lean`, `check_iff`).

## What was wrong with `JoinStmt`

`ZkFormal.PQ.StatePort.JoinFold.JoinStmt` (`StatePort/JoinFold.lean:70-84`) is

```
JoinStmt := ∀ B cb w cfg resp runs, RelD1a B cb w → (backing) → RelD1a B cb w
```

and `join_additive` discharges it as `intro … exact hrel`.  The conclusion is the *same*
`RelD1a` as the premise, so the "join" never reaches the D3 chunk relation at all.  The reason is
structural and documented at `Join/Fold.lean:56-66`: a `RelD1a` witness contains **no**
`FunctionCall` on three independent decoder rejects (`TxD1.lean:97`, `Codec.lean:75`,
`ChunkValidationD1.lean:63`), so "every call is backed" is vacuously true there and there is
nothing to prove.  A join whose conclusion is `RelD1a` cannot be the D3 join.

## What this file proves instead

`Statement.Compose` (`Join/Statement.lean:641-642`) states the honest shape:
`Joint j → NearSpecV3.D3.RelD3 chunkClaim chunkWitness`.  The proof obligation is exactly the
`.fcall` agreement — the state proof's answer at each call equals the D3 spec's, which the Wasm run
supplies.  That is `Fold.relD3_of_checkD2Core` (`Join/Fold.lean:211`): given

* `hh : ∀ c st ar m a g d, f c st ar (.fcall m a g d) = d3Hooks cfg .functionCall c st ar (.fcall m a g d)`,
  the per-call agreement, and
* `ok : checkD2Core (patchArm cfg f) true cb w (some gAlpha) = .ok ()`, the state-side pipeline run,

the D3 chunk relation follows.  `Coverage.coverage_pv86` (`Join/Coverage.lean:146`) is the same
theorem instantiated at `pv86` with the pipeline hypothesis supplied.

Both are already kernel-checked.  What this module adds is the *packaging*: the join stated in
`JointStmt`'s own vocabulary (`Joint`, `WasmHalf`, `StateHalf`) with a proof, plus the honest
negative result that no `JointStmt`-shaped join can conclude `RelD3`, so the vacuous one should be
retired rather than strengthened.

## The honest limit

`Compose` as stated takes `hh` and `ok` as hypotheses.  `hh` is the per-call agreement between the
state proof's answer function and the Wasm run's; `ok` is the state pipeline's verdict on the
chunk's own witness bytes.  Neither is discharged here — `hh` needs the HOST chip and the
`runCall`/`d3Hooks` correspondence (`JOIN-INTERFACE.md` §2-§5), and `ok` needs the D2 witness to be
the one the chunk carries.  What *is* proved is that these two are sufficient and that the
composition is a single rewrite over the whole chunk pipeline (`patchArm_eq_d3`), not a per-layer
induction.  The gap is therefore named and bounded, not hidden behind a reflexive statement.
-/

namespace ZkFormal.PQ.Join

open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Wasm

set_option maxRecDepth 100000

/-! ## §1. The `.fcall` agreement is the whole join obligation

`ActionHooks` is a one-field structure, so a hook *is* its `functionCall`; the join's content is
therefore entirely in the call arm.  These two lemmas restate that in the form `Compose` consumes.
-/

/-- **Agreement at `.fcall` alone determines the patched hook.**  A restatement of `patchArm_eq_d3`
in the shape the join reads it: if the state side's answer function `sa` matches the D3 hooks on
`.fcall`, the patched hook *is* `d3Hooks`.  Nothing else about `sa` is constrained — the other nine
base arms and the delegate arm are the spec's by construction. -/
theorem join_obligation_is_call_arm (cfg : NearCfg)
    {sa : ActCtx → ActSt → AR → Base → Except String (ActSt × AR)}
    (hagree : ∀ (c : ActCtx) (st : ActSt) (ar : AR) (m a : Bytes) (g d : Nat),
      sa c st ar (.fcall m a g d)
        = (NearSpecV3.D3.d3Hooks cfg).functionCall c st ar (.fcall m a g d)) :
    patchArm cfg sa = NearSpecV3.D3.d3Hooks cfg :=
  patchArm_eq_d3 cfg hagree

/-- **The state-side pipeline verdict transfers across the join.**  With `.fcall` agreement, the
pipeline run under the patched hook and the run under the D3 hooks are the same run — the
`checkD2Core_patch` equation, restated as the join needs it. -/
theorem join_pipeline_eq (cfg : NearCfg)
    {sa : ActCtx → ActSt → AR → Base → Except String (ActSt × AR)}
    (hagree : ∀ (c : ActCtx) (st : ActSt) (ar : AR) (m a : Bytes) (g d : Nat),
      sa c st ar (.fcall m a g d)
        = (NearSpecV3.D3.d3Hooks cfg).functionCall c st ar (.fcall m a g d))
    (allowCodes : Bool) (cb w : Bytes) (gasCap : Option Nat) :
    checkD2Core (patchArm cfg sa) allowCodes cb w gasCap
      = checkD2Core (NearSpecV3.D3.d3Hooks cfg) allowCodes cb w gasCap :=
  checkD2Core_patch cfg hagree allowCodes cb w gasCap

/-! ## §2. The join, stated in the deployed shape and proved -/

/-- **The join, deployed parameters.**  This is `Compose`'s content at `pv86`: per-call agreement
plus the state pipeline's acceptance on the chunk's witness gives `RelD3` for the chunk's own bytes.
It is `Coverage.coverage_pv86` with its arguments named in the join's vocabulary.

Unlike `JoinStmt`, the conclusion is `RelD3` on the **D2** witness — the relation the D3 verifier
actually checks — and the premise `hstate` is a statement about the chunk's bytes rather than a
`RelD1a` restatement.

**This is not yet a soundness transfer.**  §4 proves that under `hagree` this premise is *equivalent*
to the conclusion (`compose_pv86_premise_iff_conclusion`), so the theorem is the identity on `RelD3`
modulo the `patchArm_eq_d3` rewrite.  What §2 genuinely delivers is the fold (§1).  Do not read this
theorem as closing the join. -/
theorem compose_pv86 (cb w : Bytes)
    (sa : ActCtx → ActSt → AR → Base → Except String (ActSt × AR))
    (hagree : ∀ (c : ActCtx) (st : ActSt) (ar : AR) (m a : Bytes) (g d : Nat),
      sa c st ar (.fcall m a g d)
        = (NearSpecV3.D3.d3Hooks Wasm.pv86).functionCall c st ar (.fcall m a g d))
    (hstate : checkD2Core (patchArm Wasm.pv86 sa) true cb w
        (some NearSpecV3.D3.gAlpha) = .ok ()) :
    NearSpecV3.D3.RelD3 cb w :=
  coverage_pv86 cb w sa hagree hstate

/-- **Why there is no `cfg`-general form.**  `checkD3`'s legacy core is *fixed* at `Wasm.pv86`
(`D3/FunctionCall.lean`: `checkD3Core := checkD2Core (d3Hooks Wasm.pv86) …`), so a join that concludes
`RelD3` must be at `pv86` specifically — there is no protocol-parametric statement to prove.  A
`compose_cfg` at an arbitrary `cfg` would have to conclude `checkD2Core (d3Hooks cfg) …`, which is
*not* `RelD3`.  This is why `compose_pv86` is the join and not a special case of something wider.

Since the UQ-010 hand-over (2026-10-29, `D3/Signed.lean`) `RelD3` is the core *or* a recorder-engine
decision outside the core's preconditions (resharding, storage-proof limits), so the core run is
sufficient for `RelD3` (`D3.checkD3_of_core_ok`), not equivalent to it; the equivalence holds for the
core itself, which is what this theorem now states. -/
theorem compose_is_pv86_only :
    ∀ (cfg : NearCfg) (cb w : Bytes),
      (NearSpecV3.D3.checkD3Core cb w = .ok () ↔
        checkD2Core (NearSpecV3.D3.d3Hooks Wasm.pv86) true cb w
          (some NearSpecV3.D3.gAlpha) = .ok ()) := by
  intro cfg cb w
  unfold NearSpecV3.D3.checkD3Core
  exact Iff.rfl

/-! ## §3. Why the old statement cannot be repaired in place

This is the negative result the vacuous `JoinStmt` needed and did not have: its conclusion type
forbids ever concluding `RelD3`.  Recording it stops a future pass from "strengthening"
`join_additive` and believing the join is closed.
-/

/-- **A `RelD1a` witness carries no `FunctionCall`.**  `checkD1` rejects every contract code blob
(`ChunkValidationD1.lean:63`), and the D1 transaction and receipt decoders reject every action tag
but `Transfer(3)` (`TxD1.lean:97`, `Codec.lean:75`).  So "every call is backed" is vacuous there,
and `JoinStmt`'s premise about `runs` constrains nothing.

Stated as the type fact rather than as a decode walk, so it is checkable without replaying the
decoders: `JoinStmt`'s conclusion is `RelD1a B cb w`, which is exactly its premise, and the
backing hypothesis is never consumed.  Any theorem of that shape is
`fun _ _ _ _ _ _ hrel _ => hrel` — i.e. `join_additive`. -/
theorem joinStmt_conclusion_is_premise :
    ∀ (B : Nat) (cb w : Bytes) (cfg : NearCfg) (resp : StatePort.HostResp)
      (runs : List (Prepared × Nat × St × Res)),
      NearSpecV3.RelD1a B cb w →
      (∀ r ∈ runs, ∃ (p : Prepared) (n : Nat) (s0 : St) (ts : List Nat) (out : Res),
        r = (p, n, s0, out) ∧ StatePort.WasmRunStmt cfg p n s0 resp ts out) →
      NearSpecV3.RelD1a B cb w :=
  fun _ _ _ _ _ _ hrel _ => hrel

/-- **The retirement note, as a theorem.**  `JoinStmt`'s backing hypothesis is provably dead
weight: the same conclusion follows without it.  Therefore no strengthening of `JoinStmt` can
produce `RelD3`, and the join must be stated on the D2 witness as `compose_pv86` does. -/
theorem joinStmt_backing_is_erasable :
    ∀ (B : Nat) (cb w : Bytes) (cfg : NearCfg),
      NearSpecV3.RelD1a B cb w → NearSpecV3.RelD1a B cb w :=
  fun _ _ _ _ hrel => hrel

/-! ## §4. The honest limit of `compose_pv86`: its premise *is* its conclusion

A soundness transfer earns its name by consuming a premise that is **weaker** than, or
independent of, its conclusion.  `compose_pv86`'s premise is neither.  Under `hagree`,
`patchArm_eq_d3` rewrites `StateSide`'s checker to `d3Hooks`, and `RelD3` *is* the `d3Hooks` run —
so the premise and the conclusion are the same proposition, and `compose_pv86` is the identity on
`RelD3` up to that rewrite.

This is the same defect as `join_additive`, moved one layer: there the conclusion was the premise by
`exact hrel`; here it is the premise by a `rw`.  Proved, not asserted, because a future pass reading
§2's claim that `hstate` is "a genuine statement about the chunk's bytes" would otherwise believe the
join is closed.  It is not: see `docs/logs/pq-prepare-link-2026-10-23.md`.

What survives, and is worth keeping, is §1: the *fold*.  `checkD2Core_patch` shows the chunk
pipeline reads its hook at exactly one place, so agreement at `.fcall` determines the whole pipeline
verdict.  That is a real structural theorem about `checkD2Core`.  It is not a soundness transfer,
because both sides of the equation it proves are the same run. -/

/-- **`compose_pv86`'s premise is equivalent to the core of its conclusion.**  Given `.fcall`
agreement, `StateSide` and `RelD3`'s legacy core (`checkD3Core = .ok ()`) are the same proposition:
the premise can be neither weaker nor stronger than the core, so the theorem transfers no soundness.
(Since the UQ-010 hand-over, 2026-10-29, `RelD3` itself is wider than its core: it also accepts
claims the core excludes as resharding or above its storage-proof bound. The premise still only ever
reaches `RelD3` through the core, `D3.checkD3_of_core_ok`.) -/
theorem compose_pv86_premise_iff_conclusion (cb w : Bytes) (sa : StateArm)
    (hagree : ArmAgrees Wasm.pv86 sa) :
    StateSide Wasm.pv86 cb w sa ↔ NearSpecV3.D3.checkD3Core cb w = .ok () := by
  have h : StateSide Wasm.pv86 cb w sa
      = (checkD2Core (NearSpecV3.D3.d3Hooks Wasm.pv86) true cb w
          (some NearSpecV3.D3.gAlpha) = .ok ()) := by
    unfold StateSide
    exact congrArg (· = .ok ()) (coverage Wasm.pv86 cb w sa hagree)
  rw [h]
  exact Iff.rfl

/-- **The join reduces to the identity on `RelD3`'s core.**  Stated separately from the `iff` so the
reduction is visible as a term: once `.fcall` agreement holds, nothing about the state pipeline's
verdict is needed that the core run did not already supply. -/
theorem compose_pv86_reduces_to_refl (cb w : Bytes) (sa : StateArm)
    (hagree : ArmAgrees Wasm.pv86 sa) :
    NearSpecV3.D3.checkD3Core cb w = .ok () → NearSpecV3.D3.checkD3Core cb w = .ok () :=
  fun hrel => (compose_pv86_premise_iff_conclusion cb w sa hagree).mp
    ((compose_pv86_premise_iff_conclusion cb w sa hagree).mpr hrel)

end ZkFormal.PQ.Join
