# Verification of the 2026-10-21 lane claims, and where the PQ track stands

Written after merging `fix/pq-paper-soundness` and `lane/pq-nv-faithful`, when 21 commits from
parallel lanes arrived on `main` mid-session. Every claim below was checked against the artifact,
not the commit message. Labels: **[K]** kernel-checked here, **[M]** measured here, **[S]** stated
`Prop`, **[O]** open.

## 1. Lane-by-lane verdict

### `pq-host-memio` — claims hold, one caveat it states itself

| claim | verdict |
|---|---|
| `RegLenAgree` **was false**; refuted by `regLenAgree_lone_length` | **[K]** `regLenAgree_lone_length` axioms `[propext, Quot.sound]`. The counterexample is real: a `register_len` call emits one length row and no byte row, so the stated "byte count at the length's producer time = len" fails for every `len ≠ 0`. |
| correct obligation `regLenAgree_group` proved | **[K]** axioms `[propext, Classical.choice, Quot.sound]`, incl. the `L = 0` length-only case |
| `reg_group_walk`, `reg_pos_lt_len`, `reg_gap_wraparound`, `reg_byte_not_last`, `reg_group_bounds` | **[K]** all present, all clean axioms |
| HOSTB `pos`/`len` soundness hole closed | **[K]** `HostB.inters` now carries `r16 pos` and `r16 blen`, both `act·(1−reg)` |
| KAT 88/88 | **[M]** reproduced **97/97** on the current program set (88 → 97 programs) |
| tamper 101/101 | not independently re-run |

**Its own stated caveat, which I confirm is load-bearing:** `regLenAgree_group` takes `hsend` (the
R16 send-count bound) as a *hypothesis*, and it is not derivable from `Holds (wasmBaseRegAir)`
alone, because REG adds space-6 CH traffic so a REG trace does not satisfy `Holds (wasmBaseAir)`.
Without `hsend`, `gap = P−1` satisfies `cPosLtLen` at `pos = len` (`reg_gap_wraparound`) — so
termination of the walk genuinely depends on it.

**One thing the lane corrected in its own handoff:** `2e536d4b7`'s `r16 pos` is *not* what makes
`reg_pos_lt_len` provable; the load-bearing lookups are `r16 gap` and `pos ≤ r`. Rare and
commendable to see a lane retract its predecessor's justification.

### `pq-runcall-fold` — real theorem, and a real negative finding

| claim | verdict |
|---|---|
| the fold: `applyNewChunkD2` reads `ActionHooks` only at `.fcall` | **[K]** `patchArm_eq_d3`, `checkD2Core_patch`, `actionLoop_congr` |
| `Coverage.coverage_pv86 : … → RelD3 cb w` | **[K]** axioms `[propext, Classical.choice, Quot.sound]` |
| `runCall_eq_done` (a `WasmRunStmt` becomes the `functionCall` branch) | **[K]** clean axioms |
| **`JoinFold.JoinStmt` is vacuous** | **[K]** confirmed: `join_additive` is `intro … exact hrel` |

The vacuity finding is correct and important. Three independent decoder facts make "every
`FunctionCall` is backed by a Wasm run" trivially true on a `RelD1a` witness:
`TxD1.lean:97` rejects any tx action tag ≠ 3, `Codec.lean:75` rejects any receipt action tag ≠ 3,
and `ChunkValidationD1.lean:63` rejects any contract code blob (`w.no_code`). **So there is no
`FunctionCall` in a `RelD1a` witness at all.** `RelD3` runs on the D2 witness, which admits both.

Consequence for the earlier analysis: my `PQ/Join/Statement.lean` reading was right that `Compose`
was unproved, but the stronger point is that the `RelD1a → RelD3` *shape* was wrong, not merely
unfinished. The coverage theorem is now stated as `hagree` + `hstate ⇒ RelD3`, with the witness
lift as a named `Prop` (`H6`).

Still open, and named as such: `hagree` (the Wasm half, blocked on code/`ctx` binding) and
`hstate` (the state half, blocked on the D1→D3 witness-format lift).

### `pq-keccak-perm` — a definition, honestly labelled as one

| claim | verdict |
|---|---|
| Keccak-f round AIR as a row, 4,890 columns, degree ≤ 3 | **[K]** `ncols_eq`, `cols_len`, `deg_*` |
| per-step lemmas (theta parity, iota selection, rho/pi index) | **[K]** `KeccakSteps`, evaluation lemmas |
| differential vectors: 192 rounds, 9 permutations, 9 sponge | **[M]** reproduced from `lake build` output |
| chi soundness | **[K]** `chi_sound` in the pre-existing `ChiAir` |

But: **there is no `Holds ⇒ keccakF` refinement theorem**, and the file says so in a section
titled "What this file does not do". No interactions, no absorb/squeeze rows, no state bus. This is
a well-scoped definition plus vectors, not a usable hash chip yet.

### `pq-actionr-fc` — encoder lemmas real, two documented placeholders

| claim | verdict |
|---|---|
| FC + `promise_create` rows, per-field prefix index | **[K]** `pcPlan_eq_encode_tail`, `fcallActionsLen_eq`, `pcPlan_vector` — axioms `[propext, Quot.sound]` |
| `FCPlanIsTrace`, `PCPlanIsTrace` | **[S]** both are `Prop := True`, documented as unproved generator obligations, and unused |

The `:= True` is ugly but honest: named, commented as unproved, never used to close anything.

## 2. The paper's four blockers, re-scored

| blocker | before this batch | now | what moved |
|---|---|---|---|
| **Family-QROM instantiation** | skeleton checked, protocol absent | **unchanged, [O]** | nothing in this batch touches it |
| **Full WHIR composition** | adaptive conditioning proved for folds; 27 coverage transfers | **unchanged, [O]** | nothing in this batch |
| **NV / base semantics** | no Lean NV model; NV faithfulness a TCB entry | **better on the base side, [K]/[O]** | `wasm_base_exec_host` now `Holds`-plus-3-premises; `regLenAgree_group` proved (with `hsend` open); HOSTB hole closed. NV side unchanged |
| **Recursive hash bridge** | endpoint (c), named assumption, shape checked | **unchanged, [O]** | nothing in this batch |

So: **the base layer moved, the tail did not.** That is the correct reading. The paper's headline
— a ≤300 KB proof whose soundness reduces to `INNER-SOUND(c)` plus circuit faithfulness — is
exactly where it was.

## 3. Where the e2e goal actually stands

**Proved and usable now** (all kernel-clean, axioms ⊆ std3):

* the D0a/D1 state extraction on the PQ stack (`pq_d0a_rel`, `pq_d1_rel`, `holdsP_of_swirl`);
* `wasm_base_sound` for the F1 slice, and `wasm_base_exec_host` with `hst`/`hch` discharged;
* the base-layer register wire: group walk, `RegLenAgree` in its correct group-local form;
* the coverage *shape*: the chunk pipeline depends on hooks only at `.fcall`;
* the aggregation tree's semantics, statements, shape independence, node-count irrelevance;
* arbitrary-tree certified-root induction.

**Stated, not proved** (the honest TCB/assumption surface):

* `hsend` for REG traces (needed for `regLenAgree_group` termination);
* `NvFaithful`'s five non-LogUp components (declared TCB; composition and LogUp proved);
* `INNER-SOUND(c)`;
* `Replacement` (CFHL21 Cor 4.2);
* `hagree` (Wasm half of the join) and `hstate` (state half, needs the D1→D3 witness lift);
* `RealStoreMatchesTables`, `UpsV3AppliesLog`.

**Absent**:

* a Lean model of the NV AIR (so NV faithfulness cannot be stated against the real circuit);
* a hash chip with a refinement theorem (Keccak is a definition; SHA-384 lives outside `zk-formal`);
* the receipt AIR for the 23 promise/`promise_create` functions;
* the Ed25519 layer;
* any PQ-oriented game in `formal-core` (`RomSound` is a 2^256, 32-byte-answer game).

**Measured**:

* 293,077 B FINAL, binding on at every level, V_d accepts, forgery control rejects;
* KAT 97/97 (reproduced here);
* WHIR fold coverage 27 transfers, full FINAL + PARENT r1–r2, budgets ≤ 2^-280.11.

## 4. The binding number is still the query move

Nothing in this batch changes `ε_rbr = 2^-268.01`. The fold budgets remain 12–18 bits below it.
Any statement of the form "we improved the soundness bound" would be false; what improved is the
*set of obligations*, not the number.

## 5. Loose ends worth closing

1. **`RegWalk.lean` is not imported by `WasmBase.lean`.** Same trap as `SoundHost.lean` earlier: the
   theorems build standalone but never enter the library target, so `lake build WasmBase` and any
   axiom audit of the library miss them. Both should be imported.
2. **KAT failures from stale AIR JSON.** I hit a false 83/97 because `run_kat.sh` reuses
   `$OUT/air*-*.json` if present; after a Lean AIR change those files are stale and the check fails
   with confusing bus/height errors. The script should regenerate them when the tool is newer (the
   same guard `bin.sh` applies to the Rust binary).
3. **`hsend` for REG** is the one concrete follow-up `pq-host-memio` names: 13 chip tables × their
   `*_flags` lemmas, currently all stated against `Holds (wasmBaseAir)`.
4. **`JoinFold.JoinStmt` should be deleted or renamed**, not left as a `Prop` that reads like an
   obligation. `join_additive` proves it in one line because it is vacuous.
