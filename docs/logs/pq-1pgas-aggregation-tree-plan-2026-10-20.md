# Plan: aggregation tree over segments for a 1 Pgas chunk

Status: 2026-10-20. Planning document, no code written. Precedes any build.
Companion: `pq-arbitrary-aggregation-proof-obligations-2026-10-19.md` (theorem backlog),
`pq-gap-analysis-2026-10-19.md` (end-to-end gap), `pq-base-aggregation/DESIGN-BASE.md` (design G),
`pq-base-aggregation/ARBITRARY-AGGREGATION-LEAN.md` (what is already proved).

## 0. Scope decision needed before anything else

There are two different targets and this plan covers only the second.

| | **A. `G_α` chunk** | **B. 1 Pgas chunk** |
|---|---|---|
| gas | 3.451e12 | 1e15 (289.8×) |
| segments (`2^28.25` cells each) | ~13 | **~1,880–3,760** |
| design | G: one shared-transcript proof, **no aggregation layer** | needs a real tree |
| signed challenge | yes | **no** (`Scope.checkD3Peta` is a research definition) |

Design G is the measured, sound route for A, and it deliberately has **no per-segment aggregation**.
A 1 Pgas chunk is the only thing that actually needs the tree. Per `DESIGN-BASE.md` §0 and §9.1,
the tree is also the case where the conservative per-proof union bound **fails** (2^−126.5 at 295
proofs), so the tree claims rest on the single-database theorem (N1/N3), not on a union.

**This plan assumes the user wants B (1 Pgas) as a research build.** If A is the goal, `build_l1_linked`
already covers the only k-to-1 node needed and this plan is unnecessary.

## 1. What already exists (validated, not assumed)

All PQ lanes are **merged into main** (`git rev-list --count main..origin/lane/<pq-lane>` = 0 for all
seven checked). So "unmerged work" does not exist; the relevant work is in main. What it contains:

### 1.1 Lean: the semantic and structural half is proved

`zk-formal/ZkFormal/PQ/Aggregation/{Tree,Statement,Shape,Compose}.lean`, wired into `ZkFormal.lean`
(lines 365–368), no `sorry`, axioms ⊆ {propext, Classical.choice, Quot.sound}:

| theorem | content | value here |
|---|---|---|
| `RangeTree.run_eq_foldSegments` | any tree runs as the flat fold | shape is irrelevant to execution |
| `RangeTree.certified_root` | leaf witnesses + local validity + links ⇒ root | the tree adds nothing to the conclusion |
| `Stmt.compose_eq_root` | compose = (first ctx/a/sa, last e/se) | root statement is shape-free |
| `Stmt.compose_rejects` | non-chainable list ⇒ `none` | rules out ragged/dropped/swapped children |
| `Shape.tree_root_shape_irrelevant` | same leaves ⇒ same root/digest | `V_d`'s expected digest is shape-free |
| `ProofTree.certified_root` | node-step induction, any arity/depth | N3/N4 structural half |
| `ProofTree.node_count_irrelevant` | composed predicate mentions only the root | no per-node error accumulation |
| `ProofTree.arity_split` | a k-ary node ≡ nested binary nodes | a fixed binary circuit implements any arity |

**This is the single biggest asset and it is done.** The tree does not need new semantics.

### 1.2 Rust: a prototype k-to-1 node, with real proofs at level 1

`native/recursion/patches/openvm-recursion-agg.patch` (1,442 lines, 12 files, +919/−31) adds
`nv/agg.rs`: multi-chain transcript (`Builder::restart_transcript`, `replay2_multi`), `PvD` (op 31)
statement exposure, `TAG_RANGE = 9` range digest, `build_agg(children, kind, preimages)`,
`build_verifier` agg mode, `NvCircuit::generate_with`, and a `SegAir` Fibonacci fixture.

Measured (`logs/agg-chain-T10.log`, `logs/agg-node-debug.log`; **test parameters**, 10 query bits):

| item | result |
|---|---|
| N1a / N1b: 2-to-1 over real segment proofs | 139,609 B each, 19,030 program rows, 2 chain starts, 845–922 s, 4.8–5.4 GB |
| exposed PVs equal `check_range_statement` of the composed statement | yes |
| N2 (2-to-1 over two N1 proofs) | program 118,916 rows; **trace never proved** (OOM at 16 GB, or stacked-height error) |
| N2 logic in the debug checker | 136,988 rows, 166.5M cells, **passes all constraints and buses**, exposes the composed statement of segments [0,4) |
| N2 tampers rejected | wrong preimage, swapped children, duplicated child |
| k-ary node effect on circuit | 0 columns, 0 interactions, no degree change |

So **level 1 works end to end with real proofs, and level 2 is checked only in the debug checker.**

## 2. Prerequisite validation: what is actually missing

I checked each prerequisite against the current tree rather than against the lane docs. Results:

| # | prerequisite | status | evidence |
|---|---|---|---|
| P1 | Tree semantics (run/root/statement, shape independence) | **DONE** | Lean §1.1 |
| P2 | k-to-1 node circuit, multi-transcript, statement digest | **DONE (prototype)** | `agg.rs`, N1 real proofs |
| P3 | Level-1 node with real child proofs, tampers rejected | **DONE** | N1a/N1b, `agg_circuit_debug` |
| P4 | Level-2 node proof at real settings | **MISSING** | N2 only in debug checker; never proved as a real proof |
| P5 | **Program binding for NV children** | **MISSING — soundness hole** | `agg.rs` header: "program binding of NV children is not emitted (one BIND region per child needed)". Without it a node verifies *a* child proof, not the *pinned* child circuit |
| P6 | k-ary / unbalanced trees | **PARTIAL** | `arity_split` gives binary-only in circuit; Rust asserts all children at the same level. Ragged handled at statement level only |
| P7 | **Overlay applies to the current recursion tree** | **BROKEN** | `git apply --check` of the agg patch on the G2 tree fails in 10 files (builder, circuit, glue, isa, mod, tests, transcript2, uair, verifier, config). It was built on `openvm-recursion-sha384.patch` only, which has **no G2** (`select_anchor` count 0 in `pq-base-agg`, 2 in the current tree) |
| P8 | `TAG_RANGE`/`range_digest` in the recursion tree | **MISSING** | current tree has tags 0,2,3,4,5,6,7,8 — no 9 |
| P9 | A real segment prover for many segments (`seg-v1`) | **MISSING** | only the 4-opcode direct-Wasm slice. `SegAir` is a Fibonacci *fixture*, not NEAR |
| P10 | Segment split correctness for arbitrary `S` | **MISSING** | `Segment.lean` has `run_foldSegments`, but not on the PQ stack (B11 open) |
| P11 | Base-faithful for `seg-v1` | **MISSING** | B4/BF1 open; `ExtractV3Stmt` analogue unproved on PQ |
| P12 | Soundness: single-database tree theorem (N1/N3) | **MISSING** | semantic/structural halves done; QROM extraction premise `NodeOK` explicitly paper-level |
| P13 | Per-proof union bound | **FAILS** | 2^−126.5 at 295 proofs; tree needs N1 |
| P14 | 300 KB at the final layer | **PARTIAL** | 293,077 B measured, but for the *recursion tail only* (fib app), not a segment tree |

### 2.1 The three blocking findings

1. **P7 is a hard blocker and is new information.** The prototype cannot be merged as-is: it predates
   G2/stream/cpu-fast. Re-basing is mechanical but touches the exact files G2 changed (`builder.rs`,
   `circuit.rs`, `uair.rs`, `verifier.rs`). Every subsequent step depends on it.
2. **P5 is a soundness hole, not a missing feature.** A real level-2 node must bind each child's
   program, or it proves "some child proof verifies", which is worthless for the tree claim. This is
   the difference between a demo and the theorem.
3. **P9/P10/P11 mean there is no real segment to aggregate yet.** Even with a perfect tree, there is
   nothing to put in the leaves. This is the same blocker as the end-to-end gap: `seg-v1` does not
   exist, and the Wasm side has neither the HOST chip soundness (`g_after` invariant, ~112 sites) nor
   the D3 join.

## 3. Plan

Ordered so each step is decidable and nothing is built on an unvalidated base. Steps 1–4 build the
*tree machinery* on fixtures; steps 5–7 connect it to the real target. Step 4 is the first one that
can fail on soundness rather than mechanics, so it is a gate.

### Step 1 — Re-base the agg overlay onto the current recursion tree (P7, P8)

**Work.**
* Re-apply the agg overlay on top of the merged base (`openvm-recursion-sha384` + stream + cpu-fast +
  G2). Expect conflicts exactly where G2 added anchors/BIND/cached parts.
* Re-generate as `patches/openvm-recursion-agg.patch` with `make_*_patches.sh` conventions, so it
  stacks in the documented order (`sha384` → `stream` → `cpu-fast` → `agg`).
* Add `TAG_RANGE = 9`, `range_values`, `range_digest` to `sha384/config.rs`; extend the tag dispatch in
  `glue.rs` (the patch already lists tag 9 alongside the merkle-class tags).
* Make `setup_agg_deps.sh` verify base+overlay from a pristine tree, as it does today.

**Acceptance.** `git apply --check` clean on the current tree; `setup_agg_deps.sh` passes its
fresh-clone diff check; all 17 non-ignored `nv::` tests still pass; N1a/N1b reproduce their proof
bytes or their PVs at the recorded test settings.

**Risk.** Moderate. Conflicts are textual, but `builder.rs`/`circuit.rs` changed materially. Est. 2–4
days. **Blocks everything else.**

### Step 2 — Prove a real level-2 node (P4)

**Work.** The debug checker already shows the N2 logic is correct at 166.5M cells. Make it a real
proof instead of a debug run:
* raise the memory/time budget (the prototype was capped at 16 GB; `pq-stream-g2` runs use 60 GB);
* fix the stacked-height error by choosing `n_stack` from the measured program size (the same class of
  fix as the b=6 experiments: program 118,916 rows needs a taller stacked height);
* record N2 bytes, time, peak RSS, and verify natively.

**Acceptance.** A real N2 proof verifies; its exposed statement equals `RangeStmt::compose` of the two
N1 statements; the three tampers are rejected by the *verifier*, not only by the debug checker.

**Risk.** Low-moderate (mechanical sizing). Est. 2–3 days. Depends on Step 1.

### Step 3 — Generalise to depth ≥ 3 and ragged shapes (P6)

**Work.**
* Binary-only in circuit is fine (`arity_split` proves k-ary ≡ nested binary), so build the tree as a
  binary tree and let the Lean theorem cover general arity. Confirm this matches what `build_agg` emits.
* Remove/relax the "all children at the same level" assert where shapes are ragged; the statement layer
  already rejects ragged chains (`Stmt.compose_rejects`), so the circuit must expose enough for that
  check to be reachable.
* Single-child passthrough nodes (`run_node_single`) for non-power-of-two segment counts (1,880–3,760
  is not a power of two).

**Acceptance.** For S ∈ {3, 5, 8, 13} segments, a tree with mixed arity/depth proves and the root
statement is identical to the flat fold — which `Shape.tree_root_shape_irrelevant` predicts.

**Risk.** Low. Est. 2–3 days. Depends on Step 2.

### Step 4 — **GATE**: program binding for NV children (P5)

This is the step that decides whether the tree is sound. Do not proceed past it without it.

**Work (design already written, `DESIGN-BASE.md` §5.1/§5.3, README "Limits"):**
* the 2-region BIND design: ALU sends `(y, P)` with count 2, per-child E tables and per-child ACC
  rows, one role-flag column;
* reuse the existing BIND/app-binding roles from `pq-nv-preprocessed` (program ≡ native on 19,365
  elements) rather than inventing a new binding;
* or the preprocessed program commitment (§5.3), which is linear in k and is the better long-term
  choice for large fan-in.

**Acceptance.** A node whose child proof is valid but whose child *program* differs from the pinned
program is rejected by the native verifier (not the debug checker). This is the direct analogue of the
G2 forgery control, which is already measured (`forged FINAL accepted without the program check,
rejected with it`).

**Risk.** High. G2 took a measured chain and several commits to get binding right; this is the same
problem multiplied by k. Est. 5–10 days. **If this fails, the tree is a demo and the 1 Pgas claim
cannot be made.**

### Step 5 — A real segment (`seg-v1`): the actual blocker for any real leaf (P9, P10, P11)

Nothing above produces a NEAR leaf. This is the same work the end-to-end gap lists, and it is larger
than the tree itself.

**Work.** In dependency order:
1. **HOST chip soundness**: the `g_after` per-segment invariant (`JOIN-INTERFACE.md` §4.2a). The chip
   and 77/77 KATs exist (`lane/pq-host-chip`); the top-level `wasm_base_sound` is not extended because
   a host call resynchronises `g := remaining`, so `R·S + g = g0` is false across it. ~112 sites.
2. **D3 join**: `storage_write` needs `TrieKey::ContractData`, which D1 does not cover — a D3-join, not
   a D1-join (`pq-gap-analysis` §4, verified).
3. **Segment split correctness** for arbitrary `S` at receipt boundaries (`Segment.lean` fold lifted to
   the PQ stack). **Status corrected 2026-10-23 — the Lean half of this is DONE, and it is stronger
   than "receipt boundaries".** `spec/lean/v3/NearSpecV3/Wasm/Segment.lean` (111 lines) builds
   (`lake build NearSpecV3.Wasm.Segment`, exit 0, 24 jobs) and its four theorems depend only on
   `[propext, Classical.choice, Quot.sound]` — no `sorry`, no custom axioms:
   * `seg_add`: `seg (a+b) = seg a` then `seg b`
   * `run_seg`: `run (a+n) = seg a` then `run n`
   * `foldSegments_eq_seg`: the segments run in sequence equal one `seg (Σ ks)`
   * `run_foldSegments` (§3.1): `run (Σ ks + n) s = foldSegments ks s >>= run n` **for every split**
   * `foldSegments_stop`: a segment that ends early makes later segments irrelevant

   Two things follow. First, **the boundary rule is maximally permissive** — "a segment boundary may
   fall between any two steps", with host calls, gas charge points and traps each being a single
   `step`, so no step is ever split (`Segment.lean:15-18`). There is no receipt-boundary restriction
   to prove. Second, `Segment.lean` is **orphaned**: nothing imports it (`grep -r "import
   NearSpecV3.Wasm.Segment"` finds no file), so it is not in any default build target and had no
   `.olean` until this session built it explicitly. Wiring it into `NearSpecV3.lean` is one line and
   should be done so the result cannot silently rot.

   **What is still missing is the PQ-stack lift, and the gap is now quantified.** `Segment.lean`'s
   boundary state is the *whole* machine state `St` (`Machine.lean:278-303`): operand stack, frames,
   linear-memory pages, globals, tables, element/data segments, gas, registers, logs, promises,
   mock storage, action log, data-id counter. The aggregation layer's `RangeStmt` carries `ctx`,
   segment index `a`, and two boundary states of `n_state` field elements — 2 in every test. So the
   missing piece is an **injective encoding of `St` (a variable-length structure containing
   `ByteArray`s) into a fixed field-vector width**, and a proof that it commutes with the segment
   fold. That is a hash/commitment design, not a transcription exercise, which is why this is the
   expensive step.

   **Sharpened further:** the AIR itself has *no* segment concept — `near-air-v3.json`
   declares only `format/numBuses/numPub/tables/pubSegs/maxPub`, with no segment count, no range and no
   per-segment boundary declaration, and one base proof covers the whole chunk (25 tables, 3,391 used
   rows, `dump/heights.json`). The per-segment boundary state rides **bus 15**, which is a row-to-row
   chain inside `bnd`/`rcpt` and is **absent from `pubSegs`** — so it is not a public value today.
   Exposing it needs either a new public segment (which changes the vk, every stored proof and the
   trusted setup, invalidating the 299,967 B packet) or a boundary-commitment statement (item 4's
   territory). Evidence: `research/near-compression/results/pq-agg-depth-law/README.md`,
   "The boundary state is internal, not public".
4. **Base-faithful for seg-v1** (B4/BF1).

**Acceptance.** One real segment proof (ctx, j, pre, post) whose relation is `segRel`, with the
boundary-state encoding injective.

**Risk.** Very high; this is 2–3 months per the gap analysis and is *not* tree work. Est. 20–40 days
before the first real leaf exists.

### Step 6 — Many leaves: scale and measure (P13, P14)

**Work.**
* Build a tree over S = 13 (the `G_α` segmentation) with real leaves, measure time/bytes per node.
* Then extrapolate honestly to S = 1,880–3,760. Note the union-bound failure: at 295 proofs a per-proof
  union gives 2^−126.5, so the tree needs N1 (Step 7), or every layer's target raised ~8 bits.
* Verify the FINAL stays ≤ 300 KB. The measured 293,077 B is the *fib* recursion tail; it says nothing
  about a segment tree except that the final-layer shape is viable.

**Acceptance.** S = 13 measured end to end; a written extrapolation to 1 Pgas with the error accounting
stated per node and explicitly *not* a union.

**Risk.** Medium for S=13, unknown above.

### Step 7 — Soundness theorem (P12)

**Work.** Discharge `NodeOK` — i.e. apply Theorem 6.4 once to the family of vks, folding in NV-faithful
(F1)–(F6) and the `T*` refinement (T5). The Lean induction is already there (`ProofTree.certified_root`);
the missing piece is the single application of the extraction theorem, which the obligations doc records
as paper-level (S-19/S-28).

**Acceptance.** No per-node union; total error ≤ 2^−128 for ≤ 2^64 quantum queries; the statement names
S, arity, depth and shape as universally quantified.

**Risk.** Research. Est. unknown.

## 4. What I would do first, and why

**Step 1, then Step 4, before Step 2/3.** Re-basing (1) is a prerequisite by construction. Program
binding (4) is the soundness gate: if it is not achievable, the rest of the tree work is a demo and the
1 Pgas claim is not available, so the cheap nodes (2, 3) are only worth building once the expensive one
is known to work. Step 5 is the largest item and is *not* tree work; it should be started in parallel
on its own lane if the real segment is the actual goal.

A cheaper discriminator before committing to Step 1: **re-apply only the parts of the agg patch needed
for the soundness question** (`builder.rs` restart_transcript, `circuit.rs` generate_with, `agg.rs`,
the tag-9 config) and attempt the Step-4 BIND design on a 2-to-1 node with fixture children. That
answers "is per-child program binding tractable at k=2 in this circuit?" for ~3 days instead of ~15.

## 5. Honest sizing

| step | work | confidence | blocks |
|---|---|---|---|
| 1. re-base overlay | 2–4 d | high | all |
| 2. real L2 proof | 2–3 d | medium-high | 3 |
| 3. depth ≥3, ragged | 2–3 d | high | 6 |
| **4. program binding (gate)** | **5–10 d** | **medium** | **any sound tree** |
| 5. real seg-v1 leaf | 20–40 d | low | real 1 Pgas |
| 6. scale + measure to 1 Pgas | unknown | low | claim |
| 7. soundness theorem | research | low | claim |

Tree machinery on fixtures (1–4): **~2–3 weeks**, with the gate at ~1 week.
A real 1 Pgas chunk: **not reachable without Step 5**, which is the same 2–3 month blocker the
end-to-end gap already records, plus Step 6's unmeasured 290× scale and Step 7's open theory.

## 6. What must not be claimed

* "1 Pgas aggregation tree built" on fixtures alone — the leaves would be Fibonacci segments.
* "300 KB" for a segment tree — 293,077 B is the fib recursion tail.
* Soundness of a tree without Step 4 — an unbound node verifies *some* child.
* A per-proof union over ~295 proofs — it fails at 2^−126.5.

## 7. Re-base outcome (2026-10-21): measured, and it revises §2 and §3

Two things were learned by doing the work rather than reading the lanes.

### 7.1 The base dependency chain could not build at all, and that is now fixed

Before any aggregation work, `setup_cpu_fast_deps.sh` could not set up from a pristine checkout:
`openvm-recursion-sha384.patch` had duplicate file sections (so the setup's own
"tree equals patch" check can never pass), and the setup applied the already-folded-in P4 patch a
second time. Both are on main and independent of any lane. Fixed, verified on a pristine tree
(five layers set up, crate builds, program identity holds, 40/40 `nv::` tests), and merged.

Consequence for this plan: **Step 1 is therefore cheaper than estimated**, and any future
"the overlay does not apply" symptom should first be checked against the deps chain rather than
the overlay.

### 7.2 The known failure mode of the agg overlay is now precise

After rebasing, 4 of 6 aggregation tests pass (`agg_program_honest`, `agg_program_tamper`,
`agg_segment_chain_native`, `agg_shape`). The faithful evaluator reports
`bad_constraints=0, unbalanced_messages=14` — constraints hold, a **bus** is unbalanced.

One real bug was found and fixed on the way: `build_verifier` emitted its own app-statement `PvD`
row even in agg mode, so a node pushed two contradicting statement rows.

The remaining failure is the chain-start flag. G2 uses the Anchor `k2` field for the hash tag
(binds op → program, audit B6); the agg lane used the same field for the chain-start flag. Two
encodings were tried and both fail:

| approach | result |
|---|---|
| `k2 = tag + (is_first << 8)` | constraints fail at the PvD/anchor rows; faithful DOF disagrees |
| `k2 = tag` only (option (b): "declare on the chain bus") | `bad_constraints=0, unbalanced_messages=14` |

Why (b) is insufficient: the flag must be **bound by the program**, or `is_first` is a free column
and the number and position of chain starts is not a program constant — which is the entire
point of the prototype's design note. The chain bus carries `(job, state_in)` for link checking,
not a program-side declaration.

So §3's Step 1 needs one addition: **the chain start needs its own program row**. The cheapest
form, not yet implemented:

1. reuse the reserved op `Rsv27` (no interactions, `c = 0`) as `ChainStart`, job id in `k1`;
2. one new two-field bus `(job, 1)` in `NvBuses`/`TrBuses`; the ALU sends, the hash row receives
   with enable `is_first`;
3. `NUM_OPS` unchanged (`Rsv27` is renamed, not added).

This is a small ISA change, not a protocol change, and it is the prerequisite for Step 4 (the
program-binding gate) because binding an NV child requires the chain structure to be a program
constant in the first place.

### 7.3 What did not change

The gate (Step 4, program binding) is unaffected by the above and still unstarted. Step 5 (a real
`seg-v1` leaf) is untouched. The honest sizing in §5 stands, with Step 1 reduced by the deps fix
and increased by the `ChainStart` row.


## 8. Outcome (2026-10-21): steps 1-4 done, including the binding gate

The agg overlay is rebased onto G2 and **program binding works**. Five distinct defects were
between the overlay as written and a sound node; all are fixed and measured:

| # | defect | evidence |
|---|---|---|
| 1 | `build_verifier` emitted its own app-statement `PvD` row in agg mode (two contradicting rows) | row 1231 -> 26312 |
| 2 | the rebase took the pre-G1 `pow()`, emitting PoW witness rows from the program (14 phantom sends) | `nv_dof_*` 14 -> 0 unbalanced |
| 3 | chain-start flag shared the Anchor `k2` tag field (audit B6) | own `ChainStart` row (`Rsv27`), new bus allocated last |
| 4 | main's audit-B5 `is_first * ns == 0` vs the agg transcript's **global** squeeze counter | `when_first_row` instead; both chain tests pass |
| 5 | `Node` children were never program-bound | `bind_child` -> the G2 BIND block, per child |

Test state on the rebased overlay:

| test | result |
|---|---|
| `agg_circuit_debug`, `agg_g_l1_linked`, `agg_program_honest`, `agg_program_tamper`, `agg_segment_chain_native`, `agg_shape` | 6/6 pass |
| `agg_node_program_binding` (**the gate**) | pass, with a live positive control |
| `agg_node_debug` (2-to-1 over two real N1 proofs, 3 tampers) | pass |
| `agg_chain` (N1a/N1b/N2, final statement `[0,4)`) | pass |
| `nv::` non-heavy regression | 41/41 pass |

The gate is enforced by the circuit, not by a host assertion: at `PARENT_N_STACK=17` the honest
node verifies (85,584 program rows) and flipping one child program word makes the debug constraint
check fail at `NvAir row 0`.

### What this changes in §5

Steps 1-4 are done, so the remaining sizing is:

| step | status |
|---|---|
| 1. re-base overlay | **done** (plus the two base-deps fixes, merged to main) |
| 2. real L2 proof | **done** (`agg_chain`) |
| 3. depth >= 3, ragged | **partly**: `arity_split` gives binary-only circuits; ragged is handled at the statement layer only |
| 4. program binding (gate) | **done** |
| 5. real `seg-v1` leaf | **unchanged, still the blocker** (20-40 d) |
| 6. scale + measure to 1 Pgas | unstarted |
| 7. soundness theorem | unstarted |

The tree machinery now works on fixtures. A real 1 Pgas chunk is still gated on step 5: the leaves
are still Fibonacci/segment fixtures, not NEAR state transitions.

Sizing limits recorded while doing this, since they bite at every scale: level-2 traces are 2^20
NvAir rows (`n_stack >= 20` for the parent), N1 children need `n_stack >= 17`, and the NvAir height
cap is the same one that constrains the real chain.


## 9. Depth law measured (2026-10-22): P4 closed, bytes flat in depth, S=13 proved flat

Evidence: `research/near-compression/results/pq-agg-depth-law/` (README + `logs/`, hashes).
Tree: the rebased overlay in `/data/illia/nearproof-deps/pq-agg/openvm-sha384`,
**test query targets** (10 bits), CPU.

### 9.1 P4 is no longer missing

§2 recorded "P4 | Level-2 node proof at real settings | MISSING" and the README recorded N2
as never proved (stacked-height error at `n_stack` 16, OOM at 17). With
`PARENT2_N_STACK=20` the level-2 node proves on this host:

| depth | nodes at this depth | proof bytes | program rows | NvAir h | prove s | peak RSS |
|---:|---:|---:|---:|---:|---:|---:|
| 1 (App children) | 8 | 124,201 | 16,598 | 2^17 | 12.4–12.9 | 2.5–3.7 GB |
| 2 | 4 | **132,301** | 89,564 | 2^20 | 105.5–116.3 | 17.5–19.4 GB |
| 3 | 2 | **132,301** | 95,974 | 2^20 | 115.9–117.3 | 18.1–18.2 GB |
| 4 (root, 16 leaves) | 1 | **132,301** | 95,974 | 2^20 | 118.7 | 17.8 GB |

Counts are from the 16-leaf run (`agg_depth4.log`, 8+4+2+1 = 15 = 2^4 − 1 nodes, total
**890.47 s**); the separate 8-leaf run (`agg_depth3.log`, 4+2+1 = 7 = 2^3 − 1) reproduces the
same per-node numbers.

`AGG_CHAIN_OK` (segments `[0,4)`) and `AGG_DEPTH4_OK` (segments `[0,16)`) both verify the
composed statement natively. So **Step 2 of §3 is done**, at test targets.

### 9.2 The size law: flat in depth, linear in node count

Every node at depth ≥ 2 is byte-identical, including all four components
(`gkr=55,784 relations=27,168 stacking=4,192 whir=44,972`). The one-time step is
depth 1 → 2 (+6.5 %), i.e. verifying a *segment* proof versus verifying a *recursion*
proof. After that the node is a fixpoint — the same fixpoint the delivered chunk chain
shows (`L2`–`L5`: 137,196 rows, 372–375 KB each in `runs/opt-baseline-8`).

**Consequence for §3 Step 6's acceptance ("Verify the FINAL stays ≤ 300 KB"):** a wider or
deeper tree cannot push the root over the cap by itself. The root (132,301 B at test
targets) is *smaller* than the chunk chain's per-level proofs (~373 KB) because those set
`program_part = true` and the root does not (`main.rs:249` vs `:121`). The remaining size
risk is entirely the final layer's **shape** (query schedule, unwind factor, digest
width), which is exactly what the 299,967 B D0a packet already sits 33 B under.

Cost, however, is linear in node count and a depth-2 node is ~8.4× a depth-1 node
(106 s vs 12.6 s; 18 GB vs 3.5 GB). At test targets a binary tree over 1,880 leaves is
~31 h serial and over 3,760 leaves ~62 h; production targets are far worse.

> **Correction (2026-10-23): the leaf counts in the last paragraph are ~13× too large.**
> 1,880–3,760 divides a *width-equivalent* cell total by a *main*-cell segment size
> (`0.6e12 / 2^28.25`). The structural count is `1.22e9 ops / 2^23 ops-per-segment = `
> **146** (or 291 at the older 2^22). The ratio between the two is exactly the
> W-eq→main-cell exchange rate, `494/38 = 13.0` and `995/38 = 26.2`, which reproduces the
> published range from 146. Recomputed at the measured per-node costs, a binary tree over
> 146 leaves (padded to 256) is **~4.3 h serial** at test targets — 128 L1 nodes at 12.6 s
> plus 127 nodes at 107.8 s — and ~8.5 h for 291 leaves. The *shape* of every conclusion
> holds (cost is linear in node count, production is far worse); only the magnitude moves.
> Derivation and the self-consistency check: `docs/logs/pq-agg-tail-2026-10-22.md` §7 item 5.

### 9.3 The P5 gate is live here (contradicts §7.3)

`agg_node_program_binding` passes with a **live positive control**: the honest node is
accepted (89,000 program rows) and mutating a child program word in the trace is rejected
at the constraint layer (`air_builders/debug/mod.rs:75`). The full non-ignored suite is
**6/6 green**, not the 4/6 + `unbalanced_messages=14` recorded in §7.2 — the `ChainStart`
row from §7.2 is implemented (`isa.rs:78`, `uair.rs:615–617`, `transcript2.rs:540`) and the
bus balances. §7.3's "the gate is unstarted" is stale for this tree.

### 9.4 S=13 measured exactly, by a flat node (no padding, no new node kind)

A perfect binary tree needs `2^d` leaves and `run_node_single` does not exist, so the
binary route cannot hit 13. It is not needed: `build_agg` already accepts any arity, and
Lean's `arity_split` proves a k-ary node is the same statement as nested binary nodes. So
the exact S=13 point is **one flat 13-to-1 level-1 node** (`AGG_S=13`, `AGG_LOG_ROWS1=19`,
`PARENT_N_STACK=19`, `logs/agg_s13_lr19.log`):

| children | chain starts | proof bytes | program rows | NvAir h | prove s | peak RSS |
|---:|---:|---:|---:|---:|---:|---:|
| 13 | 13 | **133,357** | 104,614 | 2^19 | 75.5 | 12.2 GB |

`AGG_S13_OK`, statement = segments `[0, 13)` verified natively.
`gkr=51,848 relations=27,168 stacking=5,104 whir=49,052`. That is within 0.8 % of the
depth-2 binary root (132,301 B) and **cheaper in time** than the 16-leaf tree (75.5 s vs
890 s) because it is one trace instead of 15.

**Step 6's acceptance is therefore met on the size question at test targets**: an S=13
aggregation node is 133,357 B, so it fits under 300 KB with 2.25× headroom, and depth does
not erode it (§9.2).

Two negative results to keep, both `program exceeds 2^15 rows` (`builder.rs:303`):
`AGG_LOG_ROWS1=17` panics for a flat 13-to-1 node (level-1 is only "small" for k = 2–4),
and `AGG_LOG_ROWS=17` panics for any depth ≥ 2 node.

Still unchanged and still blocking: the leaves are `SegAir` Fibonacci fixtures, not
`seg-v1` (P9/P10/P11), and every number here is at 10 query bits, so byte counts are not
comparable to the 300 KB production target. **No production-target node has been proved.**

### 9.5 Order I would now use

1. Promote the three probes (`agg_chain_depth3`, `agg_chain_depth_n`, `agg_s13_flat`) into
   the overlay patch so the law reproduces from a pristine tree — today they are
   deps-tree-only edits to `/data/illia/nearproof-deps/pq-agg`, not in the patch.
2. **Measure one depth-2 node at production targets** (268-bit, z=32, 42 B, `m` per the
   pinned shape). This is the last unmeasured quantity on the size axis and the only one
   that can invalidate §9.2's "does not degrade" claim for a real root. Note the delivered
   chain already runs NvAir 2^20 (`shapes=[(1048576, 76), …]` in `runs/opt-baseline-8/chain.log`),
   so the tree adds no new height requirement. The "2^18 headroom" warning in `HANDOVER.md:69`
   is about `nv_chain` (262,572 rows) at a pinned 2^18, not about this tree.
3. Implement `run_node_single` for **ragged** trees only. It is not needed for S=13: the
   flat 13-to-1 node is exact (§9.4).
4. Do not buy larger-S runs before (2): wider trees cannot change the root's byte count,
   so more S only buys the same 132,301 B at linear cost.

