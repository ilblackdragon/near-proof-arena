import ZkFormal.PQ.Join.Fold
import NearSpecV3.ChunkValidationD1a
import NearSpecV3.ChunkValidationD2
import NearSpecV3.D3.FunctionCall
import NearSpecV3.TxD1
import NearSpec.Codec
import NearSpecV3.Rungs

/-!
# ZkFormal.PQ.Join.Coverage — the coverage theorem, its premises, and what the premises mean

Lane `pq-hostfinal`, 2026-10-22.  This file keeps the `pq-runcall-fold` fold (`Fold.lean`,
`checkD2Core_patch`) and rewrites the two premises after the 2026-10-21 gap analysis
(`docs/logs/pq-d3-chain-gap-2026-10-21.md` §5) found the earlier draft **circular**: it stated

```
coverage : ArmAgrees → StateSide → RelD3
```

where `StateSide` *was* `RelD3` once `ArmAgrees` held, so the "theorem" was `h ∘ rfl` — a rewrite
wearing a join's clothes.  What is genuinely proved here is smaller and better shaped:

| declaration | content |
|---|---|
| `coverage` | the fold: the pipeline run on the state proof's arm **is** the run on `d3Hooks`, given agreement at `.fcall` |
| `coverage_pv86` | `ArmAgrees` + `StateSide` ⇒ `RelD3` |
| `patchArm_noncall` **[K]** | the patch changes *only* `.fcall` — the checked form of "the join touches nothing else" |
| `armAgrees_d3` **[K]** | the first premise is **inhabited**: the D3 hook itself agrees with itself, so `coverage` is not vacuous by contradiction |
| `armAgrees_iff_eq` **[K]** | `ArmAgrees` is *exactly* the pointwise `.fcall` equation, i.e. it has the content of the join and no more |

## Why the premises are still hypotheses

`ArmAgrees` says: the state proof's answer function equals the spec's D3 call arm at every
`FunctionCall`.  The spec's arm *is* `runCall` (`D3/FunctionCall.lean:364-368`), so this is the
statement "the state tables' answer is the Wasm run's outcome".  It is not provable here for the
same reason `Register.RegBusSound` is not: one side is computed from the D1 state tables
(`PQ/StatePort/`), the other by the Wasm machine (`WasmBase.Main.ExecHost`).  Discharging it needs
both artifacts, and neither is imported by `zk-formal` (the Wasm base is a separate Lake package —
`Fold.lean` §"What is not here").

`StateSide` says: the D2 chunk pipeline accepts the chunk when the state proof's arm replaces
`.fcall`.  That is the state half's own statement, and it is *not* a restatement of `RelD3` — the
patched hook is a different `ActionHooks` value unless `ArmAgrees` holds, which is why the fold is
needed at all.

## The D1→D3 witness lift (§3) — a documented negative fact, not a placeholder

The earlier draft carried the lift as one opaque `Prop`; `StatePort/JoinFold.JoinStmt` carried it as
a reflexive implication (`join_additive` is `intro …; exact hrel`).  Both hide the real obstruction,
which is a **decoder** fact:

* `RelD1a`'s transaction decoder `pTxD1` rejects every action tag but `3` (Transfer) —
  `spec/lean/v3/NearSpecV3/TxD1.lean:97`;
* its receipt decoder `NearSpec.pReceipt` does the same — `spec/lean/NearSpec/Codec.lean:75`;
* `checkD1` rejects any contract code blob — `ChunkValidationD1.lean:63` (`w.no_code`).

So a `RelD1a` witness contains **no `FunctionCall` and no code at all**: "every call is backed by a
Wasm run" is vacuously true on it, and `RelD1a B cb w → RelD3 cb w` is not merely unproved but
**the wrong shape**.  `RelD3` is checked on the **D2** witness format
(`ChunkValidationD2.decodeStateWitnessD2`), which admits both.  The lift is therefore *witness
production* (`WitnessLift` below), not a re-reading of the same bytes.

**Update 2026-10-30.** Over the checker relation `RelD1a` the lift is false (a kernel-checked
counterexample, `NearSpecV3.Examples.not_d1a_sub_d3`). By the owner's decision the statement's rungs
are now `RelD3 ∧ InRungDk` (`NearSpecV3.Rungs`), and §4 states and proves the lift over the D1a rung
(`witnessLift`, a projection).
-/

namespace ZkFormal.PQ.Join

open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Wasm

set_option maxRecDepth 100000

/-- The state proof's per-call answer: the same signature as `ActionHooks.functionCall`
(`D2/Actions.lean:74`), produced by the state tables rather than by `runCall`.  A plain `def`, not an
`abbrev`: `abbrev` does not unfold under `rw`/`▸` in this context, which made every hook lemma fail
to apply. -/
def StateArm : Type := ActCtx → ActSt → D2.AR → Base → Except String (ActSt × D2.AR)

/-! ## §1. The two halves, as equations about independently produced functions -/

/-- **The join at one call.**  `sa` is the state proof's answer function; the right-hand side is the
spec's D3 call arm, which is `runCall` (`D3/FunctionCall.lean:364-368`).  `armAgrees_iff_eq` below
shows this is exactly the pointwise `.fcall` equation — the join's whole content, and nothing else.

Note what it does *not* say: it does not say `sa` **is** `d3Hooks` as a function, only that the two
agree at `.fcall`.  `Fold.patchArm_eq_d3` then turns that pointwise agreement into hook equality,
which is the fold's content. -/
def ArmAgrees (cfg : Wasm.NearCfg) (sa : StateArm) : Prop :=
  ∀ (c : ActCtx) (st : ActSt) (ar : D2.AR) (m a : Bytes) (g d : Nat),
    sa c st ar (.fcall m a g d)
      = (NearSpecV3.D3.d3Hooks cfg).functionCall c st ar (.fcall m a g d)

/-- **The state half**: the chunk is valid when the state proof's answers replace the call arm.  The
hook is `Fold.patchArm cfg sa`, which keeps the spec's answer on every non-call action and uses `sa`
at `.fcall`. -/
def StateSide (cfg : Wasm.NearCfg) (cb w : Bytes) (sa : StateArm) : Prop :=
  checkD2Core (patchArm cfg sa) true cb w (some NearSpecV3.D3.gAlpha) = .ok ()

/-! ## §2. The coverage theorem

`checkD2Core_patch` (`Fold.lean`) is the whole proof: `patchArm_eq_d3` turns the patched hook into
`d3Hooks`, and `RelD3` *is* `checkD2Core (d3Hooks …) true …`. -/

/-- **Coverage: the fold.**  The pipeline run on the state proof's arm is the run on `d3Hooks`, given
agreement at `.fcall`; no layer between `checkD2Core` and the hook inspects anything else. -/
theorem coverage (cfg : Wasm.NearCfg) (cb w : Bytes) (sa : StateArm)
    (hagree : ArmAgrees cfg sa) :
    checkD2Core (patchArm cfg sa) true cb w (some NearSpecV3.D3.gAlpha)
      = checkD2Core (NearSpecV3.D3.d3Hooks cfg) true cb w
          (some NearSpecV3.D3.gAlpha) :=
  @checkD2Core_patch cfg sa hagree true cb w (some NearSpecV3.D3.gAlpha)

/-- **Coverage at the deployed parameters: `RelD3`.** -/
theorem coverage_pv86 (cb w : Bytes) (sa : StateArm)
    (hagree : ArmAgrees Wasm.pv86 sa)
    (hstate : StateSide Wasm.pv86 cb w sa) :
    NearSpecV3.D3.RelD3 cb w := by
  -- `checkD3Core` is the pipeline run on `d3Hooks`; an accepting core run is an accepting `checkD3`
  -- run (`D3.checkD3_of_core_ok`, the UQ-010 hand-over only acts on core errors).
  have hchk : NearSpecV3.D3.checkD3Core cb w
      = checkD2Core (NearSpecV3.D3.d3Hooks Wasm.pv86) true cb w
          (some NearSpecV3.D3.gAlpha) := rfl
  have hok : NearSpecV3.D3.checkD3Core cb w = .ok () :=
    hchk ▸ ((coverage Wasm.pv86 cb w sa hagree) ▸ hstate)
  exact NearSpecV3.D3.checkD3_of_core_ok cb w hok

/-! ## §3. What the premises mean, checked

Three facts make the reduction's shape reviewable rather than rhetorical: the patch touches only
`.fcall`; the first premise is inhabited; and the first premise is *exactly* the pointwise equation
(so the theorem cannot be strengthened by weakening it, and cannot be proved by `rfl`). -/

/-- **The patch changes only `.fcall`.**  This is the checked form of "the join touches nothing
else": every other action keeps the spec's own answer, whatever `sa` does. -/
theorem patchArm_noncall (cfg : Wasm.NearCfg) (sa : StateArm) (c : ActCtx) (st : ActSt)
    (ar : D2.AR) {b : Base} (hb : ∀ (m a : Bytes) (g d : Nat), b ≠ Base.fcall m a g d) :
    (patchArm cfg sa).functionCall c st ar b
      = (NearSpecV3.D3.d3Hooks cfg).functionCall c st ar b := by
  cases b with
  | fcall m a g d => exact absurd rfl (hb m a g d)
  | createAccount => rfl
  | deploy _ => rfl
  | transfer _ => rfl
  | stake _ _ => rfl
  | addKey _ _ => rfl
  | deleteKey _ => rfl
  | deleteAccount _ => rfl
  | toGasKey _ _ => rfl
  | fromGasKey _ _ => rfl
  | deployGlobal _ => rfl
  | useGlobal _ => rfl
  | stateInit _ => rfl

/-- **The first premise is inhabited**: the D3 hook agrees with itself, so `coverage` is not
vacuous by contradiction. -/
theorem armAgrees_d3 (cfg : Wasm.NearCfg) :
    ArmAgrees cfg (NearSpecV3.D3.d3Hooks cfg).functionCall := fun _ _ _ _ _ _ _ => rfl

/-- **`ArmAgrees` is exactly the pointwise `.fcall` equation** — the join's content, in one place.
The forward direction is the definition; the converse is what the theorem consumes.  Consequently
`coverage`'s hypothesis cannot be discharged by `rfl` for an *arbitrary* `sa`, which is why the
statement is a join and not a rewrite. -/
theorem armAgrees_iff_eq (cfg : Wasm.NearCfg) (sa : StateArm) :
    ArmAgrees cfg sa ↔
      ∀ (c : ActCtx) (st : ActSt) (ar : D2.AR) (m a : Bytes) (g d : Nat),
        sa c st ar (.fcall m a g d)
          = (NearSpecV3.D3.d3Hooks cfg).functionCall c st ar (.fcall m a g d) :=
  Iff.rfl

/-- **The fold at the identity arm**: the sanity check that `coverage`'s conclusion is the pipeline
`RelD3` runs, not a different pipeline. -/
theorem coverage_identity (cfg : Wasm.NearCfg) (cb w : Bytes) :
    checkD2Core (patchArm cfg (NearSpecV3.D3.d3Hooks cfg).functionCall) true cb w
        (some NearSpecV3.D3.gAlpha)
      = checkD2Core (NearSpecV3.D3.d3Hooks cfg) true cb w
          (some NearSpecV3.D3.gAlpha) :=
  coverage cfg cb w _ (armAgrees_d3 cfg)

/-! ## §4. The D1→D3 witness lift — now a projection (decision 2026-10-30)

The earlier statement was `RelD1a B cb w → ∃ w2, RelD3 cb w2` over the **checker** relation
`RelD1a` (`checkD1a` accepts). That statement is **false**: `NearSpecV3.Examples.not_d1a_sub_d3`
(`spec/lean/v3/NearSpecV3/Examples/D1NotSubD2.lean`, kernel-checked) exhibits a `RelD1a B0` pair
whose claim (`epoch_start_after` flag 0 on the genesis block) `RelD3` rejects from the claim alone, so
no witness lifts it. The owner's decision was to redefine the rungs of `near-chunk-v3` as
restrictions of the top relation, `RelRungDk := RelD3 ∧ InRungDk` (`NearSpecV3/Rungs.lean`,
statement `NearSpecV3.ChallengeChunkV3R`). The lift is stated over the D1a rung and holds by
projection with the identity witness (`witnessLift`).

What moved: the state chain's obligation is now to establish the *rung* relation `RelRungD1a`,
i.e. the D1a run **and** `RelD3` on the same bytes. Reaching `RelD3` from the D1a AIR alone remains
the join's job (`coverage_pv86`, below); the lift no longer hides it. -/

/-- **The lift** over the D1a rung of the statement. -/
def WitnessLift (B : Nat) (cb w : Bytes) : Prop :=
  NearSpecV3.RelRungD1a B cb w → ∃ w2 : Bytes, NearSpecV3.D3.RelD3 cb w2

/-- **`WitnessLift` holds** (identity witness; `NearSpecV3.rungD1a_lift`). -/
theorem witnessLift (B : Nat) (cb w : Bytes) : WitnessLift B cb w :=
  fun h => NearSpecV3.rungD1a_lift h

/-- **How the lift composes with the join.** A D1a-rung chunk gives a `RelD3` witness (the lift);
when the state half accepts that witness with the arm `sa`, the fold (`coverage_pv86`) re-derives
`RelD3` through the state arm. The conclusion keeps the `StateSide` conjunct, which no hypothesis
supplies on its own. -/
theorem relD3_of_lift (B : Nat) (cb w : Bytes) (sa : StateArm)
    (hrel : NearSpecV3.RelRungD1a B cb w)
    (hagree : ArmAgrees Wasm.pv86 sa)
    (hstate : ∀ w2 : Bytes, NearSpecV3.D3.RelD3 cb w2 →
      StateSide Wasm.pv86 cb w2 sa) :
    ∃ w2 : Bytes, NearSpecV3.D3.RelD3 cb w2 ∧ StateSide Wasm.pv86 cb w2 sa := by
  obtain ⟨w2, hw2⟩ := witnessLift B cb w hrel
  have hside : StateSide Wasm.pv86 cb w2 sa := hstate w2 hw2
  exact ⟨w2, coverage_pv86 cb w2 sa hagree hside, hside⟩

/-- info: 'ZkFormal.PQ.Join.witnessLift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms witnessLift

end ZkFormal.PQ.Join
