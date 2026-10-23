import NearSpecV3.D3.FunctionCall

/-!
# `ZkFormal.PQ.Join.PrepareLink` — the chunk → preparation link, and its exact one-way boundary

Lane `pq-prepare-link`, 2026-10-23.  This file answers the question the D3 goal asks under
*"chunk to preparation: connect the chunk-level execution/validation to the preparation stage with a
non-vacuous composition"*, and it answers it by proving the direction that is **true** and
**refuting** the direction that is not.

## The one-way boundary

`NearSpecV3.Wasm.runCall` opens with `match prepare cfg code blockLevel with …` and every
non-`.ok` verdict (`outOfDomain`, `unmodeled`, `prepErr`, `compileErr`) produces `Run.line`, never
`Run.done`.  Hence:

| direction | verdict | why |
|---|---|---|
| VM-produced outcome (`Run.done`) ⇒ `prepare` returned `.ok p` | **[K] true** (§1) | `Run.done` is reachable only inside the `.ok p` arm |
| `prepare` returned `.ok p` ⇒ the run is accepted by the chunk relation | **false** | the run can still trap, link-fail or resolve-fail; those are recorded outcomes |
| chunk accepted ⇒ `prepare` returned `.ok p` for every executed contract | **false**, see below | a preparation failure is a legal *failed action*, not a rejection |

The third row is the one that gets overclaimed, so it is spelled out rather than asserted — and its
proof status is stated honestly, because it is **not** `[K]` in this tree.  The argument is: a
preparation failure yields `Run.line` (§2, `[K]`), `Exec.runCall` renders it through `nop` as
`abort 0 0 CompilationError(PrepareError(…))` (`Wasm/Exec.lean:458-459`, `[doc]`), and
`D3.lineOutcome` maps any `abort B U …` line to a gas pair (`D3/FunctionCall.lean:225-228`, `[doc]`),
so the hook returns `.ok (st, ar.fail)` and the chunk relation accepts the chunk with a failed action
— exactly as nearcore does.

The missing `[K]` step is the string parse: `String.splitOn` is opaque to the kernel, so
`lineOutcome "abort 0 0 …" = .ok (0, 0)` has no `Decidable` instance that reduces (verified: `decide`
and `decide +kernel` both get stuck at `String.splitOn`).  Closing rows two and three to `[K]`
therefore needs either a reducible model of `splitOn` or a logged/differential check — it is **`[O]`**,
and is *not* claimed below.  What §2 does prove, `[K]`, is the exact boundary the argument relies on:
`Run.done` holds iff preparation succeeded, for all four failure verdicts.

## What this buys the join

`Compose.compose_pv86` (`ZkFormal/PQ/Join/Compose.lean:100`) concludes `RelD3` from a per-call
agreement hypothesis and a state-side verdict.  §3 states what a *success* at the hook pins down
about preparation, which is the premise the `.done` arm of that agreement needs and the `.line` arm
must not be given.

## Evidence classes

Everything in this file is **[K]**: no `sorry`, no `axiom`, no `native_decide`.  The axioms of each
declaration are recorded in `zk-formal/test/AuditPQJoinPrepareLink.lean`.

## What is *not* claimed here

* Predicating over the code blob the hook actually resolved.  `functionCall` computes `codeB` from
  `st.o`/`c.env` inside the `do` block, so §1–§2 are stated on `runCall`, whose `code` argument is
  explicit.  Lifting to the hook is a monadic projection through `functionCall`'s ~30 bind nodes; it
  is not done here, and no theorem below should be read as if it were.  The peel was probed: after
  `unfold functionCall` + `repeat' split at h` the term reduces to a single leaf whose hypothesis is
  the full nested `runCall` match, so the lift is a mechanical but non-trivial case walk.
* Rows two and three of the table above, and the `lineOutcome` parse.  See their entry.
* Anything about `Read.check` or the deployed artifact.  That chain is
  `examples/reexec-v3-d3/formal/ReexecV3D3/ArtifactSound.lean` and is independent of this file.
-/

namespace NearSpecV3.D3

open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Wasm

set_option maxRecDepth 200000

/-! ## §1 The positive link: a VM-produced outcome implies preparation succeeded -/

/-- **A completed run implies a prepared module.**  `runCall` reaches `Run.done` only inside the
`.ok p` arm of its `prepare` match; the four failure verdicts all return `Run.line`.  So observing a
VM-produced outcome is evidence that the preparation stage ran and succeeded on `code`.

This is not definitionally `RelD3` (it mentions neither `checkD3` nor the chunk bytes), and it is not
a restatement of its own premise: the conclusion is about `prepare`, a different function, evaluated
on a different term. -/
theorem runCall_done_prepare_ok (cfg : NearCfg) (code : ByteArray) (method : String)
    (ctx : CallCtx) (fuel : Nat) (blockLevel full : Bool) (real : Option TTN.RealStore)
    {s : St} {err : Option String}
    (h : runCall cfg code method ctx fuel blockLevel full real = .done s err) :
    ∃ p : Prepared, prepare cfg code blockLevel = .ok p := by
  unfold runCall at h
  by_cases hm : method.isEmpty
  · simp [hm] at h
  · simp only [hm] at h
    have h0 := h
    cases hpr : prepare cfg code blockLevel with
    | ok p => exact ⟨p, rfl⟩
    | outOfDomain w => simp [hpr] at h0
    | unmodeled w => simp [hpr] at h0
    | prepErr v w => simp [hpr] at h0
    | compileErr k n => simp [hpr] at h0

/-- The contrapositive, in the form a join hypothesis uses: if *no* preparation result is `.ok`,
*no* run completes. -/
theorem runCall_ne_done_of_not_prepared (cfg : NearCfg) (code : ByteArray) (method : String)
    (ctx : CallCtx) (fuel : Nat) (blockLevel full : Bool) (real : Option TTN.RealStore)
    (h : ∀ p : Prepared, prepare cfg code blockLevel ≠ .ok p)
    (s : St) (err : Option String) :
    runCall cfg code method ctx fuel blockLevel full real ≠ .done s err := by
  intro hd
  obtain ⟨p, hp⟩ := runCall_done_prepare_ok cfg code method ctx fuel blockLevel full real hd
  exact h p hp

/-! ## §2 The negative link: a preparation failure is an action failure, not a rejection

Each verdict gets its own named theorem so a downstream proof can cite the exact failure it is
reasoning about.  Together they say: `Run.done` is *equivalent* to preparation having succeeded, and
therefore that the chunk relation — which consumes hook results, not `Run`s — cannot conclude
"prepared" from acceptance. -/

theorem runCall_ne_done_of_ood (cfg : NearCfg) (code : ByteArray) (method : String)
    (ctx : CallCtx) (fuel : Nat) (blockLevel full : Bool) (real : Option TTN.RealStore)
    (why : String) (h : prepare cfg code blockLevel = .outOfDomain why)
    (s : St) (err : Option String) :
    runCall cfg code method ctx fuel blockLevel full real ≠ .done s err := by
  refine runCall_ne_done_of_not_prepared cfg code method ctx fuel blockLevel full real ?_ s err
  intro p hp
  rw [h] at hp
  exact PrepResult.noConfusion hp

theorem runCall_ne_done_of_unmodeled (cfg : NearCfg) (code : ByteArray) (method : String)
    (ctx : CallCtx) (fuel : Nat) (blockLevel full : Bool) (real : Option TTN.RealStore)
    (why : String) (h : prepare cfg code blockLevel = .unmodeled why)
    (s : St) (err : Option String) :
    runCall cfg code method ctx fuel blockLevel full real ≠ .done s err := by
  refine runCall_ne_done_of_not_prepared cfg code method ctx fuel blockLevel full real ?_ s err
  intro p hp
  rw [h] at hp
  exact PrepResult.noConfusion hp

theorem runCall_ne_done_of_prepErr (cfg : NearCfg) (code : ByteArray) (method : String)
    (ctx : CallCtx) (fuel : Nat) (blockLevel full : Bool) (real : Option TTN.RealStore)
    (v why : String) (h : prepare cfg code blockLevel = .prepErr v why)
    (s : St) (err : Option String) :
    runCall cfg code method ctx fuel blockLevel full real ≠ .done s err := by
  refine runCall_ne_done_of_not_prepared cfg code method ctx fuel blockLevel full real ?_ s err
  intro p hp
  rw [h] at hp
  exact PrepResult.noConfusion hp

theorem runCall_ne_done_of_compileErr (cfg : NearCfg) (code : ByteArray) (method : String)
    (ctx : CallCtx) (fuel : Nat) (blockLevel full : Bool) (real : Option TTN.RealStore)
    (k n : Nat) (h : prepare cfg code blockLevel = .compileErr k n)
    (s : St) (err : Option String) :
    runCall cfg code method ctx fuel blockLevel full real ≠ .done s err := by
  refine runCall_ne_done_of_not_prepared cfg code method ctx fuel blockLevel full real ?_ s err
  intro p hp
  rw [h] at hp
  exact PrepResult.noConfusion hp

/-! ## §3 `Run` classification: no completed run is a line, and vice versa

The two constructors are disjoint, so the classification is by construction rather than by argument.
This is the lemma shape a `.fcall` agreement hypothesis needs: an agreement stated over `Run.line`
cannot silently be used as an agreement over `Run.done`. -/

theorem run_line_ne_done (l : String) (s : St) (err : Option String) :
    Run.line l ≠ Run.done s err := by
  intro h
  cases h

theorem run_done_ne_line (s : St) (err : Option String) (l : String) :
    Run.done s err ≠ Run.line l :=
  (run_line_ne_done l s err).symm

end NearSpecV3.D3
