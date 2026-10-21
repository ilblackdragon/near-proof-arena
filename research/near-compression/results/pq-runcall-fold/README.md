# pq-runcall-fold: the coverage theorem, from a joined proof to the D3 chunk relation

Lane `lane/pq-runcall-fold`, from `origin/main` @ `2336803ce` (2026-10-21). This is gap-analysis
§2.6 and `JOIN-INTERFACE.md` §4.3 step 4: the last structural item between the existing Wasm and
state pieces and an end-to-end claim.

Labels: **[K]** kernel-checked, **[P]** proved in another package (cited), **[S]** stated `Prop`,
**[O]** owner named.

## 0. One-paragraph summary

The fold is **done, and stronger than asked**: not just one receipt's action list but the whole
chunk pipeline (`applyNewChunkD2` — every receipt kind, the delayed/incoming/instant queues,
transactions, yield timeouts, the bandwidth scheduler, the header comparison) is shown to depend on
the `ActionHooks` **only through the `.fcall` arm**. The coverage theorem
(`Coverage.coverage_pv86`) then composes that with the two halves the lanes own. Two things are
*named obligations*, not proved: the Wasm half (`ArmAgrees`, owned by `pq-wasm-base`, blocked on
the code/`ctx` binding) and the state half (`StateSide`, owned by `pq-state-port`, blocked on the
D1→D3 witness-format lift below).

The main **finding** of the lane is that `JoinFold.JoinStmt` — the statement the previous lanes were
working against — is *vacuous*, and the coverage theorem cannot be a same-bytes `RelD1a → RelD3`.
§4 explains why and what replaced it.

## 1. What is proved [K]

Files: `zk-formal/ZkFormal/PQ/Join/Fold.lean` (the fold), `zk-formal/ZkFormal/PQ/Join/Coverage.lean`
(the theorem). Both build in the `ZkFormal` library; axiom sets are exactly
`{propext, Classical.choice, Quot.sound}` (`#print axioms`).

### 1.1 The fold — `Fold.lean`

`ActionHooks` is a **one-field structure** (`D2/Actions.lean:73-75`), so a hook *is* its
`functionCall`. `patchArm cfg f` keeps the spec's answer on every non-call action and replaces only
`.fcall` by `f`; `patchArm_eq_d3` proves that patch is `d3Hooks` as soon as it answers `.fcall` the
same way.

| theorem | statement |
|---|---|
| `patchArm_fc` | the patched hook's `.fcall` answer is `f`'s (definitional) |
| `patchArm_eq_d3` | a patch that agrees on `.fcall` **is** `d3Hooks` (one-field record ext) |
| `checkD2Core_patch` | `checkD2Core (patchArm cfg f) … = checkD2Core (d3Hooks cfg) …` |
| `checkD2Core_congr` | two hooks agreeing on `.fcall` give the same `checkD2Core` verdict |
| `checkD3_congr` | the same at the deployed parameters (`pv86`, code blobs, `G_α`) |
| `relD3_of_checkD2Core` | a check with a patched hook that agrees on `.fcall` yields `RelD3` |
| `applyAction_congr` | the hook is read **only** in `applyAction`'s `.fcall` arm |
| `actionLoop_congr` | **the action-list induction**, at the level the hook is consumed |

`actionLoop_congr` is the deliverable's "induction over the action list" and is kept because it is
*why* `patchArm_eq_d3` needs only `.fcall` agreement: the other nine base arms and the delegate arm
never read the hook. `checkD2Core_patch` then covers the whole chunk in one rewrite.

*Abandoned alternative.* A first draft proved one congruence per pipeline layer (`applyActionReceipt`,
`processReceipt`, `processWithTotals`, the instant-receipt drain, `processLocals`, `processIncoming`,
`processDelayed`, `applyNewChunkD2`). Those proofs hold but are unnecessary on a one-field structure,
and cost ~900 s of kernel time re-checking the 100,000-step unfolded instant drain (peaking at ~27 GB
RSS — above the 24 GB cap). The patch argument replaces all of it with two rewrites. This is recorded
so the next reader does not redo the layered version.

### 1.2 The coverage theorem — `Coverage.lean`

| theorem | statement |
|---|---|
| `runCall_eq_done` | `runCall`'s `.done` is the spec entry call's outcome, from the `prepare`/`link`/`resolve`/`instantiate` facts `functionCall` already established |
| `coverage` | `.fcall` agreement (`hagree`) ⇒ the patched check equals the D3 check |
| `coverage_pv86` | the same at the deployed parameters: `hagree` ∧ `StateSide` ⇒ `NearSpecV3.D3.RelD3` |
| `hchk` | `checkD3 cb w = checkD2Core (d3Hooks pv86) true cb w (some gAlpha)` (definitional) |

The theorem's conclusion is `RelD3`; its two hypotheses are exactly the two lanes' obligations, and
nothing else. `A-IC`, `NV-faithful`, `Base-faithful` and `T*` are **not** used at this level — they
enter above it (see §5).

## 2. The exact theorem and hypothesis table

```
coverage_pv86 (cb w : Bytes)
  (sa : ActCtx → ActSt → AR → Base → Except String (ActSt × AR))
  (hagree : ∀ c st ar m a g d,
      sa c st ar (.fcall m a g d)
        = (D3.d3Hooks pv86).functionCall c st ar (.fcall m a g d))
  (hstate : checkD2Core (patchArm pv86 sa) true cb w (some D3.gAlpha) = .ok ()) :
  D3.RelD3 cb w
```

| # | hypothesis | discharged by | status |
|---|---|---|---|
| H1 | `hagree` — the state proof's per-call answer equals the Wasm run's | `wasm_base_exec_host` [P] + `runCall_eq_done` [K] + `CodeBound` [S] | **stated**, owner `pq-wasm-base` |
| H2 | `hstate` — the chunk checks with those answers | `pq_d1_rel` [P] + D1→D3 witness lift (§4) | **stated**, owner `pq-state-port` |
| H3 | `ExtractD1StmtT` (D1 phase 2) | `ZkFormal.NearV3.D1.StmtsT` | **stated**, owner `v3-d1-*` |
| H4 | `ExtractV3StmtAt` (D0a phase 2) | `ZkFormal.NearV3.Assembly` | **stated**, owner `v3-d0a-*` |
| H5 | `SwirlRel ⇒ HoldsP` | `PQ/StatePort/Bridge.holdsP_of_swirl` | **proved** [K] |
| H6 | the D1→D3 witness-format lift (§4) | **absent** | **stated**, owner: this lane |
| H7 | `A-IC(τ)`, `NV-faithful`, `Base-faithful`, `T*` | recursion / NV lanes | **stated**, §5 |

Only H1 and H2 are new at this layer. H3/H4/H5 are pre-existing; H6 is the gap this lane uncovered;
H7 is above the chunk relation and untouched here.

## 3. What compiles, and the exact commands

```
HEAVY_MEM=24G taskset -c 14-15,28-29 /data/illia/nearproof-deps/bin/heavy \
  sh -c 'cd zk-formal && lake build ZkFormal.PQ.Join.Fold ZkFormal.PQ.Join.Coverage'
```
```
✔ [762/762] Built ZkFormal.PQ.Join.Fold (4.5s)
✔ [763/763] Built ZkFormal.PQ.Join.Coverage
Build completed successfully (763 jobs).
```

`#print axioms` on `coverage`, `coverage_pv86`, `checkD2Core_patch`, `patchArm_eq_d3`,
`runCall_eq_done`, `actionLoop_congr`: `[propext, Classical.choice, Quot.sound]` only. No `sorry`,
`native_decide` or `implemented_by` in either file.

`make pin-check` passes (16 classes; `challenges/`, `oracle/`, `nearAirV3`, `nearAirV3D1`, `spec/`
unmodified). **Caveat:** `make pin-check` deletes ~812 tracked files under
`research/near-compression/native/wasm-base/target/`; restore with
`git checkout -- research/near-compression/native/wasm-base/target` (this lane did, and the working
tree is clean apart from the two new files).

The full `lake build` (≈3,058 jobs) and the 46-minute recursion chain were **not** run (disk at
93%); the two new modules were built against the already-built dependency graph. Note: `HEAVY_MEM`
below ~28 GB caps out on the abandoned layered proof (see §1.1); the final files peak far lower.

## 4. The finding: `JoinStmt` is vacuous, and `RelD1a → RelD3` is not the right shape

`PQ/StatePort/JoinFold.JoinStmt` states

```
RelD1a B cb w → (∀ FunctionCall backed by a WasmRunStmt) → RelD1a B cb w
```

and `join_additive` proves it by `exact hrel`. It is vacuous, because **a `RelD1a` witness contains
no `FunctionCall` at all** — three independent decoder rejects:

| # | where | what it rejects |
|---|---|---|
| 1 | `spec/lean/v3/NearSpecV3/TxD1.lean:97` (`pTxD1`/`pTxFields`) | any transaction action tag ≠ `3` (Transfer) |
| 2 | `spec/lean/NearSpec/Codec.lean:75` (`pReceipt`) | any receipt action tag ≠ `3` |
| 3 | `spec/lean/v3/NearSpecV3/ChunkValidationD1.lean:63` (`checkD1`) | **any** contract code blob (`w.no_code`) |

So "every `FunctionCall` is backed by a Wasm run" is *vacuously true* on a `RelD1a` witness, which
is exactly why `join_additive` is one line.

`RelD3` is different: `checkD2Core (d3Hooks …) true …`
(`D3/FunctionCall.lean:398-403`) runs on the **D2** witness (`decodeStateWitnessD2`,
`ChunkValidationD2.lean:54-121`), which admits any action list and admits code blobs.

**Consequence.** The coverage theorem cannot be a same-bytes `RelD1a → RelD3`. It is stated instead
as "the state proof's answer function agrees with the Wasm run (`hagree`) and the chunk checks with
that answer (`hstate`)", and the D1→D3 witness lift is a named `Prop`, `H6`.

## 5. Remaining assumptions, with owners

| id | assumption | owner | state | note |
|---|---|---|---|---|
| H1 | `ArmAgrees`: the state tables' per-call answer = the Wasm run's | `pq-wasm-base` / `pq-host-chip` | open | `wasm_base_exec_host` proves the `run` half [P]; `runCall_eq_done` (this lane) converts it to the hook's branch [K]; the **code/`ctx` binding** (`Statement.lean` `CodeBound`: the module the Wasm proof certified is the one `prepare cfg codeB` built for the chunk's contract) is the open piece |
| H2/H6 | `StateSide` + the D1→D3 witness-format lift | `pq-state-port` | open | `pq_d1_rel` gives `RelD1a` [P]; `RelD1a` is Transfer-only and code-free (§4), `RelD3` is not; the lift is the missing link |
| H3 | `ExtractD1StmtT` (D1 phase 2) | `v3-d1-*` | stated | `NearV3/D1/StmtsT.lean` |
| H4 | `ExtractV3StmtAt` (D0a phase 2) | `v3-d0a-*` | stated | `NearV3/Assembly` |
| H5 | `SwirlRel ⇒ HoldsP` | `pq-state-port` | **proved** | `Bridge.holdsP_of_swirl` |
| H7a | `A-IC(τ)` — in-circuit SHA-384 is the random oracle | `pq-aic-research` | stated (necessary, negative result) | `aic-research/LEMMA.md`; user decision U-11/U-12 |
| H7b | `NV-faithful` — the NV circuit arithmetises `V_{i−1}` | `pq-nv-circuit-soundness` | stated | `pq-recursion-nv/FAITHFUL.md` |
| H7c | `Base-faithful` for the real segment AIR set | `pq-base-aggregation` | stated | `DESIGN-BASE.md` §10 BF1 |
| H7d | `T*` — counter-mode challenges + PoW on `B₁` | `pq-final-soundness` | stated | `final-soundness/PROOF.md` |

H1 and H2 are the only ones between the proved fold and an end-to-end D3 chunk claim. H7 is above
that claim (it bounds the *soundness error* of the recursion stack, not the chunk relation).

## 6. Why this file's theorem is not `rfl`

`d3Hooks` *is* `functionCallD3` wrapping `functionCall` (`D3/FunctionCall.lean:364-368`), so
"`d3Hooks`'s arm equals `functionCall`" is `rfl` and would prove nothing. The theorem quantifies over
an **arbitrary** `sa` — the state proof's answer function, computed from the D1 tables and from no
`runCall` — and takes agreement as a hypothesis. `patchArm` then builds the hook that keeps the
*spec's* answer on every non-call action and uses `sa` only at `.fcall`; `patchArm_eq_d3` proves that
hook is `d3Hooks`. The state proof cannot reach any other action through `sa`, which is the formal
content of "the join only touches the call".

## 7. File map

| path | what |
|---|---|
| `zk-formal/ZkFormal/PQ/Join/Fold.lean` | the fold (§1.1) |
| `zk-formal/ZkFormal/PQ/Join/Coverage.lean` | the theorem (§1.2) |
| `zk-formal/ZkFormal/PQ/Join/RunCallFold.lean` | the pre-existing `d3_only_execution` (kept; subsumed) |
| `zk-formal/ZkFormal/PQ/Join/Statement.lean` | the joint statement + `CodeBound` (H1's open piece) |
| `zk-formal/ZkFormal/PQ/StatePort/JoinFold.lean` | `JoinStmt`/`join_additive` — the vacuous statement of §4 |
| `research/near-compression/results/wasm-base-lean` | `wasm_base_exec_host`, `host_*` [P] |
| `research/near-compression/results/pq-state-port/JOIN-INTERFACE.md` | the interface this lane implements |
