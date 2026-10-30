import ZkFormal.PQ.Join.RunCallFold
import ZkFormal.PQ.Join.Statement
import ZkFormal.PQ.StatePort.D1
import ZkFormal.PQ.StatePort.JoinFold
import NearSpecV3.ChunkValidationD1a
import NearSpecV3.ChunkValidationD2
import NearSpecV3.D3.FunctionCall

/-!
# ZkFormal.PQ.Join.Fold — the fold: the chunk pipeline is determined by the `.fcall` arm

Lane `pq-runcall-fold`, 2026-10-21.  Structural half of gap-analysis §2.6 /
`JOIN-INTERFACE.md` §4.3 step 4 ("the `runCall` fold").  `Coverage.lean` is the theorem half.

## The observation that makes the fold a statement-level theorem

`ActionHooks` (`D2/Actions.lean:73-75`) is a **one-field structure**:

```lean
structure ActionHooks where
  functionCall : ActCtx → ActSt → AR → Base → Except String (ActSt × AR)
```

So a hook *is* its `functionCall`.  `d3Hooks` differs from `d2Hooks` only in that field, and
`checkD2Core` reads the hook at exactly one place — it hands it to `applyNewChunkD2`, which threads
it down to `applyAction`'s `.fcall` arm:

```
checkD2Core → applyNewChunkD2 → processLocals / processDelayed / processIncoming
            → processWithInstant → processWithTotals → processReceipt
            → applyActionReceipt → actionLoop → applyAction → hooks.functionCall
```

Hence `patchArm_eq_d3`: a hook that keeps the spec's answers on every non-call action and replaces
only `.fcall` is **equal** to `d3Hooks` as soon as it answers `.fcall` the same way.  And
`checkD2Core_patch` is then `rw [patchArm_eq_d3 hh]` — one rewrite for the whole chunk (every
receipt kind, the queues, transactions, yield timeouts, the scheduler, the header comparison).

This is strictly stronger than `RunCallFold.d3_only_execution`, which had to assume the *whole*
action was non-`fcall`: here only `.fcall` is constrained.  `applyAction_congr` records why (the
other twelve base arms and the delegate arm never read the hook), and `actionLoop_congr` is the
deliverable's action-list induction, stated at the level the hook is consumed.

A first draft of this file proved one `*_congr` per pipeline layer (for `actionLoop`,
`applyActionReceipt`, `processReceipt`, `processWithTotals`, the instant drain, `processLocals`,
`processIncoming`, `processDelayed`, `applyNewChunkD2`).  Those hold, but they are unnecessary: on
this one-field structure the patch argument subsumes them, and it costs two rewrites instead of
~900 s of kernel re-checking the unfolded 100,000-step drain.  The layered proof was abandoned for
that reason, not because it was wrong.

## The structural finding that changes the shape of the claim

**`PQ/StatePort/JoinFold.JoinStmt` is vacuous**, and `join_additive`'s one-line proof is why.  It
states `RelD1a B cb w → (backing) → RelD1a B cb w`.  But a `RelD1a` witness contains **no**
`FunctionCall` at all, on three independent grounds, each a decoder's reject:

* transactions go through `NearSpecV3.pTxD1`, which rejects every action tag but `3` (Transfer) —
  `TxD1.lean:97`;
* receipts go through `NearSpec.pReceipt`, same restriction — `NearSpec/Codec.lean:75`;
* `checkD1` rejects every contract code blob — `ChunkValidationD1.lean:63` (`w.no_code`).

So "every `FunctionCall` in the witness is backed by a Wasm run" is *vacuously true* on a `RelD1a`
witness.  `RelD3`, by contrast, is `checkD2Core (d3Hooks …) true …` on the **D2** witness
(`ChunkValidationD2.decodeStateWitnessD2`), which admits any action list and admits code blobs.

Consequence: the coverage theorem cannot be a same-bytes `RelD1a → RelD3`.  `Coverage.lean` §6
therefore states the D1→D3 witness-format lift as its own named `Prop`, instead of hiding it behind
a reflexive `JoinStmt`.

## What is not here

Nothing about a trace.  This file is statement-level and trace-free; the Wasm half
(`Holds (wasmBaseHostAir …)` ⇒ the run) lives in `research/near-compression/wasm-base-lean`, which
`zk-formal` cannot import.  `Coverage.lean` bridges to it (`runCall_eq_done`) and names the join.
-/

namespace ZkFormal.PQ.Join

open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Wasm

set_option maxRecDepth 100000

/-! ## 1. Agreement on `.fcall` is record equality -/

/-- **A hook that differs from the D3 hooks only at `.fcall`.**  `ActionHooks` is a one-field
structure, so a hook is its `functionCall`; this patch keeps the spec's answer on every non-call
action and replaces only the call arm.  The state proof supplies the call answers; everything else
stays the D3 spec's, which is exactly the division of labour the join claims. -/
def patchArm (cfg : NearCfg) (f : ActCtx → ActSt → AR → Base → Except String (ActSt × AR)) :
    ActionHooks :=
  ⟨fun c st ar b => match b with
    | .fcall m a g d => f c st ar (.fcall m a g d)
    | _ => (NearSpecV3.D3.d3Hooks cfg).functionCall c st ar b⟩

@[simp] theorem patchArm_fc (cfg : NearCfg)
    (f : ActCtx → ActSt → AR → Base → Except String (ActSt × AR))
    (c : ActCtx) (st : ActSt) (ar : AR) (m a : Bytes) (g d : Nat) :
    (patchArm cfg f).functionCall c st ar (.fcall m a g d) = f c st ar (.fcall m a g d) := rfl

/-- **A patch that answers `.fcall` like the D3 hooks *is* the D3 hooks.**  `ActionHooks` has one
field, so this is record ext; the `.fcall` case is the hypothesis and the other twelve base arms are
`rfl` because the patch copied the spec's arm there. -/
theorem patchArm_eq_d3 (cfg : NearCfg)
    {f : ActCtx → ActSt → AR → Base → Except String (ActSt × AR)}
    (h : ∀ (c : ActCtx) (st : ActSt) (ar : AR) (m a : Bytes) (g d : Nat),
      f c st ar (.fcall m a g d)
        = (NearSpecV3.D3.d3Hooks cfg).functionCall c st ar (.fcall m a g d)) :
    patchArm cfg f = NearSpecV3.D3.d3Hooks cfg := by
  have e : (patchArm cfg f).functionCall
      = (NearSpecV3.D3.d3Hooks cfg).functionCall := by
    funext c st ar b
    cases b with
    | fcall m a g' d => exact h c st ar m a g' d
    | createAccount => rfl
    | deploy cd => rfl
    | transfer d => rfl
    | stake s pk => rfl
    | addKey pk ak => rfl
    | deleteKey pk => rfl
    | deleteAccount ben => rfl
    | toGasKey pk dep => rfl
    | fromGasKey pk amt => rfl
    | deployGlobal d => rfl
    | useGlobal u => rfl
    | stateInit d => rfl
  revert e
  rw [show patchArm cfg f = ⟨(patchArm cfg f).functionCall⟩ from rfl,
      show NearSpecV3.D3.d3Hooks cfg
        = ⟨(NearSpecV3.D3.d3Hooks cfg).functionCall⟩ from rfl]
  intro e
  rw [e]

/-- **`applyAction` reads the hook only in the `.fcall` arm.**  The other twelve base arms and the
delegate arm are hook-free — this is *why* `hooks_ext` needs only `.fcall` agreement and not
agreement on all of `Base`. -/
theorem applyAction_congr {h1 h2 : ActionHooks}
    (h : ∀ (c : ActCtx) (st : ActSt) (ar : AR) (m a : Bytes) (g d : Nat),
      h1.functionCall c st ar (.fcall m a g d) = h2.functionCall c st ar (.fcall m a g d))
    (c : ActCtx) (st : ActSt) (act : Act) :
    applyAction h1 c st act = applyAction h2 c st act := by
  unfold applyAction
  rcases act with ⟨raw, ba⟩ | raw
  · rcases ba with _ | _ | ⟨m, a, g, d⟩ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
    all_goals first | rfl | simp only [h]
  · rfl

/-- **The action-list induction.**  The deliverable's "induction over the receipt/action list", at
the level the hook is actually consumed: a receipt's action loop, by induction on the list.  (This
lemma is independent of `hooks_ext` and is what shows the fold's shape; `hooks_ext` then subsumes it
for the *whole* chunk.) -/
theorem actionLoop_congr {h1 h2 : ActionHooks}
    (h : ∀ (c : ActCtx) (st : ActSt) (ar : AR) (m a : Bytes) (g d : Nat),
      h1.functionCall c st ar (.fcall m a g d) = h2.functionCall c st ar (.fcall m a g d))
    (env : Env) (r : Rcpt) (a : ActionR) (inputs : List (Option Bytes))
    (deployed attempted : List Bytes) :
    ∀ (i : Nat) (acts : List Act) (acc : ActSt × AR),
      actionLoop h1 env r a inputs deployed attempted i acts acc
        = actionLoop h2 env r a inputs deployed attempted i acts acc := by
  intro i acts
  induction acts generalizing i with
  | nil => intro acc; rfl
  | cons act rest ih =>
    intro acc
    simp only [actionLoop]
    let c : ActCtx := { env, r, a, idx := i, nActs := a.actions.length, inputs, deployed,
                        attempted }
    generalize hx : applyAction h1 c acc.1 act = v
    have hx2 : applyAction h2 c acc.1 act = v :=
      (applyAction_congr h c acc.1 act).symm.trans hx
    rw [hx2]
    cases hv : v with
    | error e => rfl
    | ok pp =>
      obtain ⟨st, ar⟩ := pp
      simp only [bind, Except.bind]
      repeat' split
      all_goals first | rfl | (exact ih _ _)

/-! ## 2. The chunk pipeline is equivariant in the hook

`checkD2Core` reads `hooks` exactly once, handing it to `applyNewChunkD2`; and `hooks_ext` turns
pointwise `.fcall` agreement into record equality, so the whole chunk — every receipt kind, the
queues, transitions, yield timeouts, the scheduler and the header comparison — is covered by one
`rw`. -/

/-- **The checker's verdict on a patched hook is the D3 verdict**, given `.fcall` agreement.  This
is the fold: no layer between `checkD2Core` and the hook inspects anything but `.fcall`. -/
theorem checkD2Core_patch (cfg : NearCfg)
    {f : ActCtx → ActSt → AR → Base → Except String (ActSt × AR)}
    (hh : ∀ (c : ActCtx) (st : ActSt) (ar : AR) (m a : Bytes) (g d : Nat),
      f c st ar (.fcall m a g d)
        = (NearSpecV3.D3.d3Hooks cfg).functionCall c st ar (.fcall m a g d))
    (allowCodes : Bool) (cb w : Bytes) (gasCap : Option Nat) :
    checkD2Core (patchArm cfg f) allowCodes cb w gasCap
      = checkD2Core (NearSpecV3.D3.d3Hooks cfg) allowCodes cb w gasCap := by
  rw [patchArm_eq_d3 cfg hh]

/-- The legacy core of the D3 relation (`D3.checkD3Core`) is the D2 pipeline with the D3 hooks, code
blobs allowed and the `G_α` cap (`D3/FunctionCall.lean`), so `patchArm_eq_d3` closes it. Since the
UQ-010 hand-over (2026-10-29) `checkD3` is this core plus a recorder-engine decision outside the
core's preconditions (`D3/Signed.lean`); an accepting core run is an accepting `checkD3` run
(`D3.checkD3_of_core_ok`), which is all `relD3_of_checkD2Core` needs. -/
theorem checkD3_congr {f : ActCtx → ActSt → AR → Base → Except String (ActSt × AR)}
    (hh : ∀ (c : ActCtx) (st : ActSt) (ar : AR) (m a : Bytes) (g d : Nat),
      f c st ar (.fcall m a g d)
        = (NearSpecV3.D3.d3Hooks Wasm.pv86).functionCall c st ar (.fcall m a g d))
    (cb w : Bytes) :
    checkD2Core (patchArm Wasm.pv86 f) true cb w (some NearSpecV3.D3.gAlpha)
      = NearSpecV3.D3.checkD3Core cb w := by
  unfold NearSpecV3.D3.checkD3Core
  rw [patchArm_eq_d3 Wasm.pv86 hh]

/-- **The coverage reduction, in checker form.**  `RelD3 cb w` follows from the same pipeline run
with the hook supplied by an arbitrary `f`, given that `f` answers `.fcall` as the Wasm run does.
The hypothesis `hh` *is* the per-`FunctionCall` statement, applied at whichever call the checker
reaches. -/
theorem relD3_of_checkD2Core {f : ActCtx → ActSt → AR → Base → Except String (ActSt × AR)}
    (hh : ∀ (c : ActCtx) (st : ActSt) (ar : AR) (m a : Bytes) (g d : Nat),
      f c st ar (.fcall m a g d)
        = (NearSpecV3.D3.d3Hooks Wasm.pv86).functionCall c st ar (.fcall m a g d))
    (cb w : Bytes)
    (ok : checkD2Core (patchArm Wasm.pv86 f) true cb w (some NearSpecV3.D3.gAlpha) = .ok ()) :
    NearSpecV3.D3.RelD3 cb w :=
  NearSpecV3.D3.checkD3_of_core_ok cb w (by rw [← checkD3_congr hh cb w]; exact ok)

end ZkFormal.PQ.Join
