import ZkFormal.PQ.Join.Fold

/-!
# ZkFormal.PQ.Join.Coverage — the coverage theorem: joined proof ⇒ the D3 chunk relation

Lane `pq-runcall-fold`, 2026-10-21.  Gap-analysis §2.6 / `JOIN-INTERFACE.md` §4.3 step 4.
`Fold.lean` proves the fold; this file is the theorem and the two named obligations it consumes.

## Statement

Given

* **`ArmAgrees`** — the state proof's own per-call answer agrees with the Wasm run's at every
  `FunctionCall` the chunk reaches, and
* **`StateSide`** — the chunk is valid when that answer replaces the hook's call arm
  (`StateSide cfg cb w sa`, i.e. `checkD2Core (patchArm cfg sa) … = .ok ()`),

the D3 chunk relation holds (`coverage`, and at the deployed parameters `coverage_pv86`).

## Why this is not a tautology

`d3Hooks` *is* `functionCallD3` wrapping `functionCall` (`D3/FunctionCall.lean:364-368`), so
"`d3Hooks`'s arm equals `functionCall`" would be `rfl` and useless.  The theorem therefore quantifies
over an **arbitrary** `f : ActCtx → ActSt → AR → Base → Except …` — the state proof's answer
function, computed from the D1 tables and from no `runCall` — and takes its agreement with the Wasm
run as the hypothesis.  `Fold.patchArm` then builds the hook that keeps the *spec's* answer on every
non-call action and uses `f` only at `.fcall`; `Fold.patchArm_eq_d3` proves that hook is `d3Hooks`,
so `checkD2Core` runs the real D3 pipeline.  The state proof cannot reach any other action through
`f`, which is the formal content of "the join only touches the call".

## The two halves

* **Wasm half** (`ArmAgrees` / `coverage`'s `hagree`, owner `pq-wasm-base` + `pq-host-chip`):
  `wasm_base_exec_host` gives
  `run = .fin sN` from `Holds (wasmBaseHostAir …)` + `HostOK` + `HostResp`; `runCall_eq_done` (§4)
  turns a `callEntry` fact into the `runCall` that the hook branches on; what remains is the
  code/`ctx` binding (`Statement.lean`'s `CodeBound`) so that the module the Wasm proof certified is
  the one `prepare cfg codeB` built.  `A-IC` is not used.
* **State half** (`StateSide` / `coverage`'s `hstate`, owner `pq-state-port`): `pq_d1_rel` gives
  `RelD1a`; the D1→D3
  witness lift (`Fold.lean` header, §"structural finding") is the gap between `RelD1a`'s
  Transfer-only, code-free witness and the D2 witness `RelD3` checks.

`ExtractD1StmtT`, `ExtractV3StmtAt` and `SwirlRel` (via the proved `holdsP_of_swirl`) are the
state half's inputs and are untouched here.
-/

namespace ZkFormal.PQ.Join

open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Wasm

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- `checkD3` *is* the D2 pipeline with the D3 hooks, code blobs allowed and the `G_α` cap
(`D3/FunctionCall.lean:398-403`).  Stated separately because `gAlpha`'s numeral makes the equation
expensive to *use* inline; as a named `rfl` it is cheap. -/
theorem hchk (cb w : Bytes) :
    NearSpecV3.D3.checkD3 cb w
      = checkD2Core (NearSpecV3.D3.d3Hooks Wasm.pv86) true cb w
          (some NearSpecV3.D3.gAlpha) := rfl

/-- The state proof's per-call answer: the same signature as `ActionHooks.functionCall`
(`D2/Actions.lean:74`), produced by the state tables rather than by `runCall`.  A plain `def`, not an
`abbrev`: `abbrev` does not unfold under `rw`/`▸` in this context, which made every hook lemma
fail to apply. -/
def StateArm : Type := ActCtx → ActSt → D2.AR → Base → Except String (ActSt × D2.AR)

/-! ## §4. `runCall`'s `.done` is the spec entry call's outcome -/

/-- The machine state `functionCall` hands to `runCall`: the instantiated module with the call's
context, the deposit added, and the trie-backed `External` installed
(`D3/FunctionCall.lean:495-497`). -/
def callSt (s0 : St) (ctx : CallCtx) (real : Option TTN.RealStore) : St :=
  { s0 with ctx := ctx, balance := ctx.accountBalance + ctx.attachedDeposit,
             storageUsage := ctx.storageUsage, real := real }

/-- **`runCall`'s `.done` is the spec entry call's outcome.**  This is the only place a
`WasmRunStmt` (a statement about `Wasm.run`, `PQ/StatePort/JoinFold.lean`) becomes a statement about
the branch `functionCall` takes.  Every hypothesis is a fact `functionCall` establishes before it
calls `runCall`: it prepared the code (`prepare … = .ok p` after rejecting `outOfDomain`/
`unmodeled`), it passed `some real` (so the curve-host gate is off), and the loading/link/resolve/
instantiate steps are the ones `runCall` itself performs. -/
theorem runCall_eq_done (cfg : Wasm.NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx)
    (fuel : Nat) (full : Bool) (real : TTN.RealStore)
    (p : Prepared) (mi : Nat) (gs gs' : Gas) (s0 sN : St) (e : Option String)
    (hmeth : method.isEmpty = false)
    (hprep : prepare cfg code true = .ok p)
    (hreal : p.m.imports.any (fun i => curveHosts.contains i.name) = false)
    (hload : payPer (Gas.init ctx.prepaidGas) C.contractLoadingBytes code.size = (gs, none))
    (hbase : payBase gs C.contractLoadingBase = (gs', none))
    (hlink : link p = .ok)
    (hres : resolve p method = .ok mi)
    (hinst : instantiate cfg p gs' = .ok s0)
    (hstart : p.m.start = none)
    (hce : callEntry cfg p fuel (callSt s0 ctx (some real)) mi = .ok (sN, e)) :
    runCall cfg code method ctx fuel true full (some real) = .done sN e := by
  unfold runCall
  simp only [hmeth, hprep, hreal, hload, hbase, hlink, hres, hinst, hstart, callSt]
  split
  · rename_i h
    exact absurd h (by simp [hmeth])
  · simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, ite_false]
    simp only [callSt] at hce
    rw [hce]

/-! ## §5. The join: the two halves agree at every call -/

/-- **The join of the two halves at one call.**  `sa` is the state proof's answer function; the
right-hand side is the Wasm run's.  Both sides are independently produced (`sa` from the D1 tables,
the right side from `runCall`), so this is a real obligation, not a definition. -/
def ArmAgrees (cfg : Wasm.NearCfg)
    (sa : ActCtx → ActSt → D2.AR → Base → Except String (ActSt × D2.AR)) : Prop :=
  ∀ (c : ActCtx) (st : ActSt) (ar : AR) (m a : Bytes) (g d : Nat),
    sa c st ar (.fcall m a g d)
      = (NearSpecV3.D3.d3Hooks cfg).functionCall c st ar (.fcall m a g d)

/-- **The state half**: the chunk is valid when the state proof's answers replace the call arm.  The
hook is `Fold.patchArm cfg sa`, which keeps the spec's answer on every non-call action and uses `sa` at
`.fcall`. -/
def StateSide (cfg : Wasm.NearCfg) (cb w : Bytes)
    (sa : ActCtx → ActSt → D2.AR → Base → Except String (ActSt × D2.AR)) : Prop :=
  checkD2Core (patchArm cfg sa) true cb w (some NearSpecV3.D3.gAlpha) = .ok ()

/-! ## §6. The coverage theorem -/

/-- **Coverage: the joined proof yields `RelD3`.**  The state proof's answers agree with the Wasm
runs at every call (`hagree`) and the chunk checks out with those answers (`hstate`); the D3 chunk
relation follows.

The proof is the fold: `patchArm_eq_d3` turns the patched hook into `d3Hooks` (it differs only at
`.fcall`, where `hagree` makes it the same), and `RelD3` *is* `checkD2Core (d3Hooks …) true …`. -/
theorem coverage (cfg : Wasm.NearCfg) (cb w : Bytes)
    (sa : ActCtx → ActSt → D2.AR → Base → Except String (ActSt × D2.AR))
    (hagree : ∀ (c : ActCtx) (st : ActSt) (ar : D2.AR) (m a : Bytes) (g d : Nat),
      sa c st ar (.fcall m a g d)
        = (NearSpecV3.D3.d3Hooks cfg).functionCall c st ar (.fcall m a g d)) :
    checkD2Core (patchArm cfg sa) true cb w (some NearSpecV3.D3.gAlpha)
      = checkD2Core (NearSpecV3.D3.d3Hooks cfg) true cb w
          (some NearSpecV3.D3.gAlpha) :=
  @checkD2Core_patch cfg sa hagree true cb w (some NearSpecV3.D3.gAlpha)

/-- **Coverage at the deployed parameters: `RelD3`.**  `pv86` is the chunk protocol version, so
`d3Hooks pv86` is the pipeline `RelD3` checks; the general theorem above plus that instantiation
gives the chunk relation. -/
theorem coverage_pv86 (cb w : Bytes)
    (sa : ActCtx → ActSt → D2.AR → Base → Except String (ActSt × D2.AR))
    (hagree : ∀ (c : ActCtx) (st : ActSt) (ar : D2.AR) (m a : Bytes) (g d : Nat),
      sa c st ar (.fcall m a g d)
        = (NearSpecV3.D3.d3Hooks Wasm.pv86).functionCall c st ar (.fcall m a g d))
    (hstate : checkD2Core (patchArm Wasm.pv86 sa) true cb w
        (some NearSpecV3.D3.gAlpha) = .ok ()) :
    NearSpecV3.D3.RelD3 cb w := by
  have hchk : NearSpecV3.D3.checkD3 cb w
      = checkD2Core (NearSpecV3.D3.d3Hooks Wasm.pv86) true cb w
          (some NearSpecV3.D3.gAlpha) := rfl
  have hok : NearSpecV3.D3.checkD3 cb w = .ok () :=
    hchk ▸ ((coverage Wasm.pv86 cb w sa hagree) ▸ hstate)
  exact hok

end ZkFormal.PQ.Join
