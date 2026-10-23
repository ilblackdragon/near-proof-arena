# A formally admitted STARK for v3 D3 (WASM execution): design

Status: **design phase**, 2026-10-23.  No decisions taken; §3 lists what the user must decide.
Statement: `spec/near-chunk-validation-d3.md`, `NearSpecV3.D3.RelD3`
(`spec/lean/v3/NearSpecV3/D3/FunctionCall.lean`; spec runtime `Wasm/*.lean`, 4 860 lines × 26
modules); tier `challengeParamsChunk .d3a` of `near-chunk-v3` (classes `d3-calls`,
`d3-callbacks`, `d3-nonwasm`, `d3-maxgas`).
Builds on `V3-D0-DESIGN.md` (§1 C/H/W split, §2 native verifier) and the companion
`V3-D2-DESIGN.md` (D3 = D2 + WASM, so **every D2 item is a D3 prerequisite**).

Labels: **measured** (run in this repo), **estimated** (arithmetic from a stated model),
**PROPOSAL** (a relation, spec, challenge or protocol change: **the user decides**; nothing in
this document changes any of them).

---

## 0. Summary and decisions requested

**Finding 1: D3's arithmetic already exists in a different tree, and it is not wired in.**
`research/near-compression/wasm-base-lean` (33 732 lines, 93 modules) proves
`wasm_base_sound` — the base 22-table AIR soundness theorem — and `wasm_base_sound_host`
(host-aware, parameterised). Eighteen `Row*` modules cover the opcode rows. The D3 *state* side
also exists: `zk-formal/ZkFormal/NearV3/D3/` (8 modules, 2 063 lines, 130 theorems, 0 `sorry`).
So D3 is **not** starting from zero like D2 is. What is missing is the *assembly*: no
`nearAirV3D3`, no `d3Hooks`↔AIR link, no join.

**Finding 2: D3 is strictly gated on D2. There is no D3 AIR without a D2 AIR.**
D3 = D2 with `e.wasm` lifted (`spec/near-chunk-validation-d3.md` §10). `checkD3` *is*
`checkD2Core (d3Hooks pv86) true … = .ok ()` (`D3/FunctionCall.lean:400-403`). Everything D2's AIR
must prove, D3's must prove too, plus the WASM execution. **No amount of WASM-AIR work produces a
D3 AIR while the D2 half is absent.**

**Finding 3: `RelTier .d3a = RelD3` is unbounded, and `G_α` is a *chunk-level* condition that
must be checked after the whole main transition.** `RelD3` carries no amendments and no
transaction/receipt bound. It does carry `G_α = 2²² · 822 756 ≈ 3.45 Tgas` (`D3.gAlpha`), but
per spec finding P2 that is evaluated *after* `finalize`, so the AIR cannot use it as a
row-count bound on the EXEC table — it bounds *gas*, and the row count is derived from
operators, which is a different quantity. A bounded tier (`D3a` already exists as a *name* but
maps to the unbounded `RelD3`) needs an explicit row/operator bound. PROPOSAL P-D3-1.

**Finding 4: the join is the hard part, and the current scaffolding is placeholder.**
`compose_pv86` is not a join — `compose_pv86_premise_iff_conclusion` proves its premise is
equivalent to its conclusion. `Statement.Compose`/`Joint`/`WasmHalf`/`StateHalf` are
`def … : Prop` with **no** theorem inhabiting any of them. Three placeholder relations were found
in this path (`JoinStmt`, `WasmRunStmt`'s tautological host clause, `Statement.Compose`). A D3
AIR does not by itself fix this; the join is separate work with its own design needs (§4).

| | **D3-N** (recommended) | **D3-S** |
|---|---|---|
| WASM execution | native re-execution (today's artifact) | in-AIR EXEC table |
| succinct? | no — witness re-execution, `D3a` as shipped | yes |
| proof size | 5 438 B proof for a 6 419 B claim (**measured**) | dominated by EXEC rows |
| new AIR work | D2 + join only | D2 + EXEC + host chips + join |
| formal effort | inherits D2's 65–130 k, plus join | +150–300 k |

**Decisions requested (PROPOSALS):**

| id | question | proposal |
|---|---|---|
| **P-D3-1** | Bounded tier | Restate `D3a` as `RelD3a := RelD3 ∧` the D0a amendments over the D3 decoder `∧ D2a's bounds ∧ T3 (operator bound)`. Today `.d3a` maps to unbounded `RelD3`, so the tier name overpromises. |
| **P-D3-2** | Which half first | **D2 AIR first.** No D3 AIR can exist without it (Finding 2). |
| **P-D3-3** | Succinct or re-execution | Keep the shipped `D3a` re-execution artifact as the admitted tier until a D3 AIR exists; do not represent it as succinct. |
| **P-D3-4** | `T3` operator bound | `Σ ops ≤ 2²²` (the EXEC table height), derived from the existing `G_α` argument (`D3/FunctionCall.lean:380-388`) rather than chosen. |
| **P-D3-5** | Join statement | State the join on artifact acceptance (`Read.check`), which is provably strictly stronger than `RelD3` (§4), not on `compose_pv86`. |

---

## 1. What `RelD3` requires beyond `RelD2a`: gap list

Per `spec/near-chunk-validation-d3.md`. `D3` lifts `e.wasm` for `FunctionCall` on `None`/`Local`
contracts and `w.no_code`; everything else is D2.

| # | area | spec § | what it adds | class |
|---|---|---|---|---|
| H1 | Code resolution | §2.1 | `contract_code.rs` resolution: `None` / `Local h` / globals out of domain / ETH-implicit legacy | C |
| H2 | Code bytes | §2.2 | blob from merged witness; cold-cache rule; deploy tracker; compile-cache out-of-domain | H (choice) + W (bytes) |
| H3 | `VMContext` | §3 | 20 fields from receipt, action, account, block, epoch | C |
| H4 | Preparation | §2, boundary | `prepare` (instrument + validate + gas), and the D3α domain conditions (no floats, no curve hosts) | **the AIR's job** |
| H5 | Execution | §1 | `runCall`: link, resolve, instantiate, start, method, ~75 host functions | **the AIR's job** |
| H6 | Outcome → action result | §4 | runner errors vs rejects; result handling; gas weights | C + W |
| H7 | Receipts | §5 | `ReceiptManager` → data/resume/action receipts, ids, ordering | H (structure) + W (bytes) |
| H8 | `apply_action_receipt` delta | §6 | merge, storage stake, refunds, commit/rollback, tokens burnt, receiver reward, output data receivers, status/outcome/compute | W |
| H9 | Outcome bytes hashed | §7 | exactly which bytes enter the receipt leaf | W |
| H10 | Domain conditions | §10 | `e.wasm` lifted; `e.code_cache`, `G_α`, H1–H14 of `near-wasm-boundary.md` §8 | C/H |
| H11 | D2 interface extensions | §8 | E1–E15: additive fields on `Env`/`ActCtx`/`ActSt`/`AR`/`RS`, new `Base` constructors | mechanical |

**H4 and H5 are the entire AIR delta over D2**, and both are already arithmetized outside
`zk-formal` (Finding 1).

### 1.1 The opcode coverage gap

`wasm-base-lean` has 18 `Row*` modules. `docs/HANDOVER.md` names the open coverage:
`loop`, `memory.grow`, `call_indirect`, and IF full-execution integration (conditional IF row
facts are on main; `if_rowfacts`/`if_rowSpec` landed in `e3cebec6c`). These are **spec-coverage**
gaps, not soundness gaps in what is covered: an uncovered opcode cannot appear in an admitted
chunk until it is covered, which costs liveness (`InD3α` narrows) but not soundness.

---

## 2. Architecture for D3

### 2.1 Two halves, two tables-of-tables

```
nearAirV3D3  =  nearAirV3D2                       -- the D2 half (V3-D2-DESIGN.md)
             ++ wasmBaseIfHostAir nloc ngl         -- the WASM half
```

Measured table counts (`rfl` lemmas in `wasm-base-lean`): `wasmBaseAir` = **22**,
`wasmBaseIfAir` = **23** (`if_air_len`), `wasmBaseHostAir` = **26** (`host_air_len`),
`wasmBaseIfHostAir` = **27** (22 + IF + HOST/HOSTO/HOSTT/HOSTB).

Table indices: the D2 tables keep their indices; the WASM tables start at
`nearTablesD2.length`. `wasmBaseIfHostAir` is the right choice over `wasmBaseHostAir` (26) because
IF is needed for ordinary contracts, and over `wasmBaseIfAir` (23) because host calls are needed
for storage/promise/register families.

### 2.2 Why the WASM half is not a drop-in

`wasm_base_sound` concludes about `run X.cfg X.p n s0` — the *spec* interpreter, from one entry
frame. `d3Hooks`' `functionCall` calls `runCall`, which does `prepare` → link → resolve →
instantiate → `callEntry`. The bridge between `runCall … = .done s err` and
`run … = .fin sN` **does not exist**. It is a real proof obligation, and it is where the current
`WasmRunStmt` scaffolding fails: its host clause was `∀ ts ∈ hostTimes, resp ts = resp ts`
(tautological — retired in `f49deaf7c`, with `wasmRunStmt_iff`/`wasmRunStmt_resp_inert` recording
that the relation never mentions its host argument).

The honest statement needs the **HOST message tape**: `WasmBase.HostChip` owns the host
interactions, and the correspondence is "the tape's messages are exactly the host calls the
machine made, with those answers", not an equation about a response function.

### 2.3 What "preparation is in the AIR" means

`H4` is subtle: `prepare` is a *compiler* (instrument, validate, charge gas). It cannot be
arithmetized literally without a compiler-correctness proof. The tractable statement is the one
`wasm-base-lean` already takes: the AIR proves properties of a **prepared program** (a `Prepared`
value whose module satisfies `CodeOK`), and the *link* from the contract's code bytes to that
prepared program is the domain condition (`InD3α` requires preparation to succeed) plus a
commitment. Proving `prepare` itself correct is a separate, much larger project and is **not**
proposed here.

---

## 3. `D3a` as a bounded tier (PROPOSAL)

Today `Tier.d3a ↦ D3.RelD3` (unbounded). Proposal:

```
RelD3a := RelD3
        ∧ a1 ∧ a2D3 ∧ canon0fD3 ∧ a7D3 B ∧ a8 ∧ a9D3 W ∧ a10D3 Dp ∧ a12   -- D0a restated
        ∧ NT2 ∧ DR2                                                      -- D2a's bounds
        ∧ T3                                                             -- Σ ops ≤ 2^22
```

`T3` is derived, not chosen: `G_α = 2²² · 822 756` is "at most `2²²` cheap operators"
(`D3/FunctionCall.lean:380-388`), so `Σ ops ≤ 2²²` is the same statement in the unit the EXEC
table counts. Note this is a *chunk-level* bound while the EXEC table is per-call, so the AIR needs
the sum across calls — a public accumulator, not a table height.

---

## 4. The join

### 4.1 What does not work, and why

`compose_pv86` was committed as "the non-vacuous join". It is not:
`compose_pv86_premise_iff_conclusion` (`Join/Compose.lean` §4) proves

```
ArmAgrees pv86 sa → (StateSide pv86 cb w sa ↔ RelD3 cb w)
```

so — under the agreement hypothesis it already assumes — the premise *is* the conclusion. The
same defect as `join_additive` (`RelD1a → RelD1a`, discharged `exact hrel`), one layer down.

### 4.2 What does work

The artifact's own acceptance predicate. `Read.check` (`examples/reexec-v3-d3`) accepts only when
the logged check succeeds **and** the witness is a fixed point of its own read-set encoding:

```
check cb w = match checkD3Reads cb w with
             | (.error _, _) => false
             | (.ok (), keys) => encodeReads cb w keys == w
```

`check_iff` (`ReexecV3D3/ReadCanonSplit.lean`, **[K]**) proves

```
check cb w = true ↔ RelD3 cb w ∧ encodeReads cb w (d3Reads cb w) = w
```

The second conjunct mentions `encodeReads`, which `RelD3` never does, so the premise is strictly
stronger **structurally**, and **[M]** by witness across the corpus: 172/172 `RelD3`-true raw
witnesses rejected by the shipped `out/verify`, 10/10 canonical forms accepted on identical claim
bytes. That is the non-vacuous composition. It is *artifact-bound*, which is the right scope for
this tier: the shipped tier is re-execution, and the composition that matters is "the binary
accepted ⇒ the relation holds".

### 4.3 The two-AIR join, if D3-S is ever built

For a succinct D3, the join is between the D2 AIR's state verdict and the WASM AIR's execution
verdict, over a shared host tape. Its statement is roughly: `Holds nearV3D3 … → RelD3`. It needs,
at minimum: the HOST tape correspondence (§2.2), `runCall`↔`run` (§2.2), and a `d3Hooks` answer
function that is *derived* from the AIR, not assumed. None of the three exists.

---

## 5. Cost model and effort

### 5.1 Measured facts

| fact | value | source |
|---|---|---|
| shipped D3a proof | 5 438 B proof for a 6 419 B claim | this repo, `out/prove` on `public-d2/d2/00-h10003-s0` |
| `Wasm/*` spec | 4 860 lines, 26 modules | `spec/lean/v3/NearSpecV3/Wasm/` |
| `wasm-base-lean` | 33 732 lines, 93 modules, 18 `Row*` | `research/near-compression/wasm-base-lean/` |
| D3 state modules | 2 063 lines, 130 theorems, 0 `sorry` | `zk-formal/ZkFormal/NearV3/D3/` |
| corpus | 407 case dirs (172 with `expected_rel_d3: true`), 244 rejection dirs | `oracle/fixtures/v3/public-chunk-v3/` |

### 5.2 Effort (estimated)

| block | est. Lean lines | risk |
|---|---|---|
| **D2 AIR (prerequisite)** | 65–130 k | high (see `V3-D2-DESIGN.md` §5.2) |
| `runCall`↔`run` bridge + host tape | 8–15 k | **high** — no scaffold exists |
| `d3Hooks` answer function from AIR | 10–20 k | high |
| assembling `nearAirV3D3` + admission | 5–10 k | medium |
| opcode coverage (`loop`, `memory.grow`, `call_indirect`, IF full) | 15–30 k | medium |
| `T3` accumulator + `D3a` tier restatement | 3–6 k | low |
| **D3 total on top of D2** | **≈ 40–80 k** | |

### 5.3 Judge budget

`V3-D2-DESIGN.md` §5.3 shows D2 alone lands at **3.4–4.7 h** against a **4 h** elaboration budget,
i.e. already over. D3 adds a WASM half on top. **A combined D2+D3 certificate cannot fit the
current budget under the per-table architecture.** Options are the same three as D2's §5.3
(split the certificate; coarsen; native-extract more), and D3 makes option 3 more attractive
because the shipped tier already *is* native re-execution.

---

## 6. Plan

| step | deliverable | gate |
|---|---|---|
| **D3-L0** | Decide P-D3-3: succinct or re-execution for the next admitted tier | user decision |
| **D3-L1** | `D3a` tier restatement with `T3` (no AIR needed) | `lake build`, `RelD3a → RelD3` proved |
| **D3-L2** | HOST tape + `runCall`↔`run` bridge statement | compiles, statement reviewed |
| **D3-L3** | `d3Hooks` answer function from the AIR | statement reviewed |
| **D3-L4** | opcode coverage closure | each row lemma `[K]` |
| **D3-L5** | `nearAirV3D3` assembly + admission | `nearV3D3_admission_final` |
| **(blocked on)** | **all of `V3-D2-DESIGN.md` §6 L0–L6** | D2 admission first |

D3-L1 is the only step that can be done *now* without D2, and it is worth doing: it removes a real
overpromise (the tier named `d3a` currently maps to an unbounded relation).

### Risks

* **D2 blocks everything** (Finding 2) — the dominant risk. D3 work not aimed at L1 is
  speculative until D2's AIR exists.
* **The `runCall`↔`run` bridge is unbounded in scope** — `runCall` does preparation, linking,
  instantiation; bridging it to `wasm_base_sound`'s `run` may expose missing spec lemmas.
* **Judge budget** — the combined certificate is already over budget at D2.
* **Join scope creep** — "join" has meant three different things in this path
  (`join_additive`, `compose_pv86`, `Statement.Compose`), all placeholder. Naming the join
  obligations as `Prop`s *before* proving them is the mitigation.

---

## 7. What this document does not claim

* No D3 AIR exists. No line of `nearAirV3D3` is written; `grep nearAirV3D3` returns zero hits.
* D3 is **not** achievable before D2's AIR. This document does not substitute for
  `V3-D2-DESIGN.md`.
* The shipped `D3a` tier is witness re-execution, not a succinct proof. Nothing here changes that.
* All effort figures are **estimated** from the D1/D0a calibration, not measured.
* `RelD3` is unbounded today, so completeness on `.d3a` is not achievable at its current statement.
