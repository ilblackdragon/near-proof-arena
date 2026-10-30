# W12 tier refinement, obligations O1–O7 (workplan item 5, 2026-10-30)

Lean: `spec/lean/v3/NearSpecV3/Successor/{TierFloats,TierHooks,TierRefine}.lean`. `TierRefine` is a
default `lake build` target (`lakefile.toml`) and imports the other two. No `sorry`. The axiom
audit (`#print axioms` from the build log) is in `axioms.txt`: only `propext`, `Classical.choice`,
`Quot.sound`. Build log excerpt: `build.log`.

**No definition was changed and no verdict can move.** The new files add theorems and two
helper definitions, `Wasm.earlyPassWith` and `D3.functionCallWith`. Each is a verbatim copy of an
existing body with its configuration-dependent calls taken as parameters. `earlyPass_eq_with` and
`functionCall_eq_with` prove they equal the originals by `rfl`, so a drift breaks the build. The
checker binaries, `checkD3`/`RelD3` and every tier's checker are the same terms as before. For that
reason there are no new fixtures and no before/after verdict table. The rules ask for those only
for semantic changes, and this work makes none. `make pin-check` is unaffected (no oracle or signed
source touched).

## 1. Relation

`Refines x y` (`TierProofs.lean`, unchanged) means `x = y`, or `x` is an exclusion
(`out of domain …`). Where the lower checker accepts or rejects (error string included), the higher
one returns exactly the same result. `Tier.verdict_of_refines` is the verdict-level reading.

## 2. Status of O1–O7

| id | obligation | status | theorems |
|---|---|---|---|
| O1 | floats | **proved at every configuration** (2026-10-30: the whole-state engine too, §5) | `Lift.floats` (`TierWholeWalk.lean`), `Lift.floats_legacy`, `relSuccessor_floats_mono`, `relSuccessor_protoGas_floatsProtoGas`, `relSuccessor_genesis_genesisFloatsProtoGas` |
| O2 | curve hosts | open | — |
| O3 | global actions | open (unchanged: the routing part in `TierMono.lean`) | — |
| O4 | storage resolution | open | — |
| O5 | loading limits | **discharged for the named tiers**: every tier sets the flag, so no named pair differs in it | `Tier.cfg_loadingLimits`, `runtimeLimits_cfg_eq`, `relSuccessor_runtimeLimits_mono`, `relSuccessor_signed_runtimeLimits` |
| O6 | resharding, non-genesis | open | — |
| O7 | complete-code witness | open. `completeCodeGlobal` still refines no tier. The race arm is **fixed** (2026-10-30, `pipeline-race-fixtures/`); the rest is W08's policy plus a state-relating walk (§5) | `complete_untimely_ood`, `complete_untimely_ood_example` |

### O1, the proof chain

1. **Preparation** (`TierFloats.lean`). `PRef x y` is the preparation-monad (`PM`) form of
   `Refines`: on every input, `x` returns `.error (.ood _)` or the same result as `y`. Its bind,
   `forIn` (list, array, `[a:b]`) and `if` congruences give `pref_lockstep`, the PM analogue of
   `refines_lockstep`.
   * `sectionBody_floats`: for every section id, `sectionBody cfg ⊑ sectionBody {cfg with floats := true}`.
     The three guards `floatGuardImport/Global/Body` are `false` under floats
     (`floatGuard*_on`); the left either throws `.ood` there or continues identically.
   * `earlyPass_floats`: through `earlyPassWith` (section parser as a parameter). The section
     result `match` is handled by generalising both runs and relating them with `sectionBody_floats`.
   * **`prepare_floats`**: `prepare cfg code bl = prepare {cfg with floats := true} code bl ∨
     ∃ w, prepare cfg code bl = .outOfDomain w`, for every `cfg`, code blob and block level.
2. **Execution never reads the flag**: `exec_floats`, `step_floats`, `instantiate_floats` (`rfl`),
   `run_floats` (induction on fuel), `callEntry_floats`, `runCall_floats` and
   `runCallWithLimits_floats` (equal once preparation is equal).
3. **Hook**: `D3.functionCall cfg` reads `cfg` only through `contractOOD cfg code` and
   `runCallWithLimits cfg code …`, on the same blob. `functionCallWith_mono`: if two instantiations
   agree on every blob, or the first one excludes it (`CallRel`), the hook refines.
   `callRel_floats` discharges `CallRel` from `prepare_floats`. `functionCallD3_mono` passes the
   `unmodeled` wrapper, and `d3Hooks_floats` gives `HooksRefine (d3Hooks cfg) (d3Hooks {cfg with floats := true})`.
4. **Pipeline** (`TierHooks.lean`): `checkD2Core_hooks_mono` and `checkD2CoreG_hooks_mono`. For
   any hooks, `HooksRefine h h'` makes the legacy checker refine. The lockstep walk goes through
   `applyAction`, `actionLoop`, `applyActionReceipt`, `processReceipt`, `processWithTotals`,
   `processWithInstant` (and its `drain`), `processLocals`, `processDelayed`, `processIncoming`,
   `applyNewChunkD2` and `checkD2CoreObs`. The pipeline only binds the hook's result and never
   catches it.
5. **Configuration and tier** (`TierRefine.lean`): `Lift.floats_legacy` (with
   `checkSuccessor_legacy_eq`, the root on a legacy-engine configuration, and
   `ProtocolCfg.wasm_floats`). Named pairs: `.signed ⊑ .floats`, `.protoGas ⊑ .floatsProtoGas`,
   `.genesis ⊑ .genesisFloatsProtoGas`. Compositions: `.signed ⊑ .genesisFloatsProtoGas`,
   `.floats ⊑ .genesisFloatsProtoGas`, `.signed ⊑ .runtimeLimits`.

(Superseded 2026-10-30, §5: `Lift.floats` covers the whole-state engine.) What O1 did not cover: floats on the whole-state (recorder) engine. No named pair needs it,
because every whole-state tier already sets `floats`. The general `Lift cfg {cfg with floats := true}`
on a whole-state configuration needs the same walk through `StorageExecution`, whose monad threads
a `Recording` state.

### Why O2, O3, O4, O6 and O7 stay open

* **O2 (curve hosts)**: the selector lives in the interpreter state (`St.curveHosts`), not in
  `NearCfg`. The two runs' states differ in that field at every step, so the proof needs a
  commutation lemma `exec cfg p {s with curveHosts := b} … = (exec cfg p s …).withCurveHosts b` for
  every instruction arm and every host function in `Wasm/Host.lean` and `Wasm/CryptoHost.lean`.
  It also needs a `StorageExecution` walk, because every curve-host tier is whole-state. Neither
  exists yet.
* **O3 (global actions)**: it changes the witness codecs, routing, `Recording.globalActions` (read
  through `get` at 10 sites in `StorageExecution`) and the host action encodings in `Host.lean`.
  This needs a simulation with a state relation, not the equal-state lockstep used here.
* **O4 (storage resolution)**: an engine change (`applyNewChunkD2` → `StorageExecution.run`). It
  needs an agreement theorem between two runtimes, not a refinement walk.
* **O6 (resharding, non-genesis)**: `checkReshardCoreObs` restructures the shell (per-block layouts,
  `walkSegment`, split-gate recomputation). Only `VRefines` can hold (Finding 2 of
  `tier-proofs/`). This is a dedicated correspondence proof. A source read found no disagreement:
  with no split gate, both sides require the header's `proposed_split` to be none.
* **O7**: see §4.

## 3. Proof engineering notes

* `refines_lockstep`'s `exact Refines.refl _` at default transparency can unfold whole pipelines
  when two subterms differ. The `hooks_lockstep` closers (`hk_close`) are `with_reducible`. A
  default-transparency `exact Refines.refl _` runs only on the goals left at the end of a walk.
* `split` on a goal whose two sides have *different* discriminants splits them separately. For
  the hook, the abstraction `functionCallWith` (rather than a direct walk of `D3.functionCall`)
  keeps the two calls apart and lets `CallRel.none` rewrite the right side from the left side's
  `none` branch.

## 4. O7: what `completeCodeGlobal` would need

`.completeCodeGlobal` is `.globalActions` with `CodeWitnessPolicy.complete`. The policy is read once
per call, in `resolveCodeBytes`. Disagreements (census `tier-proofs/ccg.json`):

| CCG | GA | nearcore | n | cause |
|---|---|---|---|---|
| reject (`w.code_complete`) | accept | ok | 178 + 8 | code served by an in-chunk or rolled-back deploy (compiled cache) |
| reject (`w.code_complete`) | reject, other reason | err/ok | 704 + 224 | same verdict, different reason string |
| reject (`w.code_complete`) | out of domain | err | 4 + 95 | the 95 pipeline races |

So `CCG ⊑ GA` fails: CCG rejects 186 chunks that nearcore and GA accept. `GA ⊑ CCG` fails for the
same chunks. On those, nearcore agrees with GA. The CCG rejections are its documented cache-free
design ("reject incomplete code witnesses"), not a soundness problem.

Finding (resolve level, `complete_accepts_untimely` / `coldPartial_untimely_ood`): `.complete`
*accepts* code that only a committed in-chunk deploy serves, even when the call's preparation was
pipelined before that deploy (`timely = false`). On that step the cold validator is a thread race,
and `.coldPartial` reports it out of domain. Under the rule "nearcore nondeterminism is out of
domain, never an accept", that step is wrong. No corpus or fixture case reaches it: the census has
no CCG-accept / GA-out-of-domain row.

A fix that would make `CCG ⊑ GA` hold (`Refines`, exact strings) changes `resolveCompleteCode` as
follows:

* an incomplete or unauthenticated witness becomes `out of domain (w.code_complete): …`;
* a committed hit honours `timely`;
* code only in `attempted` becomes out of domain;
* code found nowhere gives `invalid: MissingTrieValue (contract code)`.

With those changes, `resolveCodeBytes .complete` refines `.coldPartial` pointwise. This was not
done here, for two reasons:

1. It is a semantic change: CCG would stop deciding about 1,000 corpus cases. The rules then
   require fixtures, a breakage control and a verdict table.
2. The chunk-level step needs a `StorageExecution` simulation whose two runs carry `Recording`
   states that differ in `codePolicy` (the same machinery as O3).

Whether CCG should keep its cache-free reject semantics or become an exclusion is a decision about
the statement's meaning. It is not a pre-approved soundness fix, so it is left to the owner.

## 5. Update 2026-10-30

### Race arm of completeCodeGlobal: fixed

The §4 finding was adopted as a soundness fix (pre-approved): `resolveCompleteCode` now sends the
untimely committed-deploy arm to the cold policy's race exclusion. Only that arm changed. Evidence,
fixtures (4 seeds, 3,853 cases, 23,118 replays), the breakage control and the before/after tables
are in `docs/evidence/lean-chunk-completion/pipeline-race-fixtures/`. The `complete_accepts_untimely`
lemma of §4 described the pre-fix behaviour and has been replaced by `complete_untimely_ood`.

### Refinement machinery for the whole-state engine (`TierWhole.lean`, `TierWholeWalk.lean`)

* **`MRef x y`** is `Refines` in `StorageExecution`'s monad
  `StateT Recording (ReaderT Env (Except String))`: from every state and environment, `x` reports an
  exclusion or returns exactly `y`'s value and final state. It comes with bind, throw, `tryCatch`,
  `if`, `foldlM`/`forIn`/`mapM` congruences.
* **`functionCallRecordedWith`** is an `rfl` copy of `functionCallRecorded` with `contractOOD`,
  `wasmFuel` and `runCallWithLimits` abstracted. `functionCallRecordedWith_mono` relates two
  instantiations under `CallRel`.
* **The walk:** `applyAction_rec_mono` … `applyNewChunkD2_rec_mono` lead to `run_rec_mono`, which
  says the recorder engine refines when its recorded call does (`RecRefine`).
* **Shells:** `checkD2CoreWithObs_apply_mono`, `checkD2CoreGWith_apply_mono` and
  `checkReshardCoreObs_apply_mono` refine whenever the driver's `apply` does.
* **`Lift.floats`:** switching floats on refines at every configuration.

Proof-engineering note: the `repeat`-based lockstep walk stops silently when it hits Lean's
recursion depth on long bodies (`repeat` is `first | (tac; repeat tac) | skip`). A second
`all_goals rec_lockstep` pass resumes it.

### What is still open, and why

O2, O3, O4, O6 and O7 at chunk level are **not** proved. The equal-state machinery above covers
configuration changes that only alter the Wasm configuration's reads in `NearCfg`. The remaining
obligations need more:

* **O2 (curve hosts) and O3 (global actions)** both change a flag held in the interpreter state
  (`St.curveHosts`, `St.globalActions`). The two runs' states differ in that field at every step.
  This needs a commutation lemma `f {s with flag := b} = (f s).withFlag b` for every instruction arm
  of `Wasm.exec` and every host function in `Wasm/Host.lean` and `Wasm/CryptoHost.lean`, about 300
  definitions in the `EStateM String St` monad. O3 additionally needs:
  * `managerGlobal` versus `manager` on action logs without global actions;
  * agreement of the global codecs with the D2 codecs on every input the D2 codecs decode;
  * the queue policies;
  * a state-relating walk for `Recording.globalActions`, which `get` reads at 10 sites.
* **O4 (storage resolution)** needs an agreement theorem between two engines (`applyNewChunkD2` and
  `StorageExecution.run`).
* **O6 (resharding, non-genesis)** needs a verdict-level correspondence proof between two
  differently structured shells.
* **O7 at chunk level** needs:
  * W08's code-resolution policy, which W08 owns;
  * an accept-preservation walk with states that differ in `Recording.codePolicy`. Its resolve-level
    step is proved: `complete_ok_coldPartial` (every `.complete` accept is a `.coldPartial` accept
    of the same bytes) and `complete_untimely_ood` (both policies exclude the race arm).
