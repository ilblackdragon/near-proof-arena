# Gap analysis: an end-to-end 1 Pgas proof under 300 KB

Status: 2026-10-19, after the G2 gate passed and the D0a/D1 port experiments landed.
Companion artifacts: `tools/d1-pq-envelope/` (per-table envelope), `lane/pq-stream-commit`
`g2-gate/` (measured final), `lane/pq-state-port` (D0a port), `lane/pq-wasm-base` §14 (join
design), `lane/pq-d1-envelope` (D1 envelope).

## 0. Two different goals, usually conflated

Both are called "the target". They differ by 290× in workload and need different machinery.

| | **A. chunk at `G_α`** | **B. chunk at 1 Pgas** |
|---|---|---|
| gas | `2^22 · 822,756` = 3.451e12 (2^41.65) | 1e15 = **289.8×** A |
| status | the signed challenge's cap (`e.g_alpha`) | research definition only (`Scope.checkD3Peta`) |
| base cells [E] | 2.1–4.2 G (494–995/op × 4.19 M ops) | 0.6–1.2 **T** (D3A study §3) |
| segments at 2^28.25 main cells | ~13 | **~1,880–3,760** *(corrected 2026-10-23: **~146**, see note)* |
| one proof? | no (W would be ~200) | no (W would be **35,000–71,000**; pin is 24) |
| needs | the join (G3) | the join **plus** segmentation/recursion beyond `G_α` |

The 300 KB proof size does **not** grow with workload — only the stacking height does. So B is not
"harder to keep small"; it is harder because it needs a 1,880–3,760-segment aggregation tree that has
never been built or measured, and because the sealed challenge excludes it (`e.g_alpha`).

> **Correction (2026-10-23) on the segment count.** The **1,880–3,760** figure in the table and
> in the paragraph above mixes units: it divides a width-equivalent (W-eq) cell total by a
> **main**-cell segment size (`0.6e12 / 2^28.25`). W-eq is a cost unit, not a row count. The
> structural count is `1.22e9 ops / 2^23 ops-per-segment = ` **146** (291 at the older
> 2^22 ops/segment), and `146 × 494/38 = 1,898`, `146 × 995/38 = 3,823` reproduces the
> published range exactly. Every conclusion that follows is unaffected — the tree is still
> never built, the challenge still excludes B, and the per-proof union still fails from
> S ≈ 103–118, which **146 already exceeds**. Derivation: `docs/logs/pq-agg-tail-2026-10-22.md`
> §7 item 5.

**Recommendation:** finish A first. B is a second project, not a scale-up of A.

## 1. What is done and measured

| item | evidence |
|---|---|
| Recursion tail: 5-level G2 chain, FINAL **293,077 B**, V_d accept + forgery control | `pq-stream-commit/g2-gate/` (measured, 46 min, 17 GB) |
| Fast CPU prover: 147×, byte-identical; L1 over real base 152 s / 10 GB (was 190–230 GB est.) | `pq-cpu-prover` README §6 |
| D0a state tables on SWIRL: all 25, no stand-in, tamper 19/19, 1.02–1.60 MB | `pq-state-port` §1 |
| D1 envelope: 23/30 tables proven; per-table data cross-checked | `pq-d1-envelope`, `tools/d1-pq-envelope` |
| Direct-Wasm base: F1+div+locals+memory+globals+calls, Lean `wasm_base_sound` | `pq-wasm-base` §11–13 |
| Lean bridge ingredients for SWIRL⇒`HoldsP`, `multBoundP < p` kernel-checked | `pq-state-port` §2 |
| **Full** SWIRL⇒`HoldsP` (`holdsP_of_swirl`), D0a/D1 composition, vk⇔Lean difftest | `pq-state-port` §2.1 |
| D1 on PQ: all 30 tables, no stand-in, tamper 23/23 | `pq-state-port` §3 |
| TAPE canonical table + `tapeNet_canon`; TAPE root as a statement component | `pq-state-port` §2.2 |
| Wasm join: bus partition proved; interface + coverage statement fixed | `pq-state-port` §5 |

## 2. What is missing, ordered by what blocks A

### 2.1 HOST chip and buses — **first slice built** (`lane/pq-host-chip` `dfc18d04d`)
A call of a declared import is now representable end to end: HOST chip (`HostChip.lean`), host-aware
checker (`checkModuleH`), `step_host_ok`/`step_host_abort` under an abstract response oracle,
`host_rowfacts`, Rust trace generation, and 77/77 KATs plus HOST tamper suites. `wasmBaseHostAir`
appends HOST/HOSTO/HOSTT, so every proved F1/memory/globals/calls index is unchanged.

Still open in this lane: the top-level `wasm_base_sound` is **not** extended, because a host call
resynchronises `g := remaining`, so the invariant `R·S + g = g0` is false across it. The fix is a
per-segment invariant carrying `g_after` between host boundaries; it appears in ~112 places, so it
is mechanical but broad. Also unbuilt: `HOSTB` byte movement / MEMIO, the space-6 register space,
and any state-side response.

Bus ids were reconciled to **208/209** (`HOSTQ`/`HOSTR`) after a real three-way conflict
(7/8/9 vs 200/201/202 vs 208/209/210); 200/201/202 *collided* with classical buses 72/73/74 after
the port's `+128` shift, because the occupied range is 128–203, not 128–199.
See `lane/pq-d3-join:research/near-compression/results/pq-d3-join/BUS-NUMBERING.md`.

### 2.2 Ed25519 / SHA-512 in-circuit — **costed, recommended against in-AIR per chunk**
`lane/pq-ed25519-air` (`7f0f927d3`) censused `Ed25519.verify` from the Lean spec with an executable
transcription that reproduces all 7,265 oracle verdicts: **9,434 field muls typical / 12,217 worst**,
6,114 / 8,143 add-sub, 1 inversion, 1 `sqrtRatio`, 512 doublings, 764 / 1,017 point adds, **1**
SHA-512 invocation (not two — the second hash in the D1 path is SHA-256 of the tx body, outside
`verify`).

At a 149-cell `F_p` mul: **1,514,194 cells / 27,163 interactions per signature** typical,
1,961,245 / 34,753 worst ≈ 143 SHA-512 compressions. Field arithmetic is 99.3 % of the cost.

A working `FpChip.lean` prototype exists (15×17-bit limbs, 149 cells, 61 degree-2 constraints, two
carry chains for `a·b = q·p + r`); `mul_identity` and the chain lemmas are proved under
`[propext, Quot.sound]`, but the two exact recombination identities are **hypotheses**, and the
trace generator / `r = a*b % p` are tested, not proved.

Recommendation: a **separate signature proof layer**, not in-AIR per chunk (16–26 agent-days).
Paying 1.5 M cells per signature in the chunk AIR would dominate it.

### 2.3 The join (blocking, 15–25 agent-days [E])
Wasm proof + state proof over shared buses (`HOSTQ`/`HOSTR`/`HOSTB`), plus `code_root`/`func_root`/
`data_root` = the state side's code hash. Requires the `runCall` fold over the D1 extraction and
`wasm_base_sound` (D3α-style). Neither side's theorem covers the joined system.

*Bus partition and the interface are now fixed* (`lane/pq-state-port`): classical buses `< 128`
(kernel-proved) vs Wasm `0–6`, so `+128` separates them and 200/201/202 are the new host buses
(`Join.lean`, `JOIN-INTERFACE.md`).  The coverage statement is `JoinFold.lean` (`HostAnswer`,
`HostResp`, `WasmRunStmt`, `JoinStmt`, `join_additive`).  Still missing: the HOST chip itself.

### 2.4 The remaining D1 tables on PQ — **done**
All 30 tables now, with **no `EXT` stand-in** (`lane/pq-state-port`, `4cb4a5f88`): the natural-height
re-cut handles the six fixed-2^22 renders, 4.47 M cells, 1,289,274 B, prove 20.3 s, tamper 23/23,
V_d statement check OK.  The `EXT` stand-in described here was the envelope demo's, not the port's.
The tamper suite also documents one honest case: `rid` is all-zero padding on the fixtures, so its
payload is legitimately unconstrained (multiplicity 0); the suite reports it as skipped rather than
claiming a vacuous rejection.

### 2.5 Statement plumbing (medium, enumerated)
* **TAPE**: the public-message table's cached commitment must be carried up through every NV level
  to V_d (M2). *Lean side done* (`lane/pq-state-port`: `tapeCanon`/`tapeNet_canon` —
  `HoldsP` from SWIRL is proved, and the canonical TAPE's net-multiplicity identity is proved, so
  `VdChecks.tape` is discharged under commitment binding). The **NV passthrough** of the cached
  root (Rust, across L1…FINAL) is the remaining part.
* **`max_interaction_count` 2^28 → 2^30**: D1's N = 2^29.59. Two LogUp bits. D0a needs it too (M8).
  *Done in the demo driver* (`1 << 30` in `pq-state-port`), not yet in the production shape.
* **Per-table height cap** (`log_height ≤ maxLog_t`) enforced in vk/NV/V_d (M4). *Check done in the
  demo driver*; the vk/NV/V_d enforcement is still open.
* ~~**`holdsP_of_swirl`**: the final list-sum aggregation of the Lean bridge.~~ **Done**
  (`lane/pq-state-port` `Bridge.lean`, `426b73deb`): `holdsP_of_swirl` is proved with no `sorry`,
  and `pq_d0a_good`/`pq_d0a_rel`/`pq_d1_rel` compose it with `extractV3`/`ExtractD1Stmt`. This
  entry was stale when written.

### 2.6 Coverage theorem (medium)
`wasm_base_sound` proves execution. There is no theorem from (Wasm proof ∧ state proof) to the chunk
relation, and `ChunkStmtAir` has no Lean refinement. G4 in `pq-e2e-slice`.

*Shape fixed*: `JoinFold.JoinStmt` states it — `RelD1a` is preserved when every `FunctionCall`
action is backed by a `WasmRunStmt` whose host answers are the state tables'.  `join_additive`
records that the join only *requires* the Wasm backing and does not change the state relation.
The proof needs the HOST chip and the `d3Hooks`/`runCall` correspondence.

## 3. What is missing for B (1 Pgas) beyond A

1. **Segmentation + recursion over segments.** ~1,880–3,760 segments at `2^28.25` cells each
   (*corrected 2026-10-23: **~146** at 2^23 ops/segment — see the note in §0*); the
   aggregation tree (`build_l1_linked` k-to-1, design G) has been designed and partly prototyped
   (N1 proofs, 2-proof node debug) but never at that many leaves.
2. **The per-segment statement.** Each segment needs its own boundary state commitment and a
   cross-segment bus balance; `Segment.lean` has the fold, but not on the PQ stack.
3. **A 290× cost measurement.** No AIR has been run above `G_α`. The 12–25 h / 2–7 TB figures are
   extrapolations from the D3A study; with the 147× prover they are still hours and tens of GB per
   segment, and the tree multiplies the sequential depth.
4. **A decision** to reopen the gas cap, which the signed challenge explicitly excludes.

## 4. The single most useful next experiment

Not another model. **Prove one real D1 state shard and one real Wasm call, then join them on one
bus.** Concretely:

1. Pick the `storage_write` host call as the only bridge. It is the highest-gas call with a
   *single-write* state side. **Correction (verified 2026-10-19):** the D1 tables do **not** cover
   contract storage. `RelD1` is transfer-only (`TxD1.lean:97` rejects any action that is not
   `Transfer`), and `RuntimeD1.txKeys` walks only `accountKeyPath` and `keyAccessKey` — never
   `TrieKey::ContractData`. No AIR table references `ContractData`. So the state half of a
   `storage_write` is **new work** (a `ContractData` key prefix in `walkV3`/`kibV3` plus the
   D3 `RealStore` overlay), not something the port inherits. That makes the join a
   **D3-join**, not a D1-join, and it should be priced accordingly.
2. Prove the Wasm side with one `call` of `storage_write` (needs 2.1), and the state side with the
   trie tables (D0a port already works).
3. Check the joint `HOSTQ`/`HOSTR`/`HOSTB` balance over the two proofs.
4. Only then measure size and time.

That one experiment decides whether the join is 15 agent-days or a rewrite, and it does not require
Ed25519 (no signature if the transaction is a system receipt or the witness is supplied).

## 4a. State after the 2026-10-20 merge

All 25 PQ lanes are on main. What changed for this list:

* §2.3's *bus partition and interface* are proved and merged (`PQ/StatePort/{Join,JoinFold}.lean`),
  and `holdsP_of_swirl` is proved and composed into `extractV3`/`ExtractD1Stmt`. The bus ids are
  fixed at **208/209/210** after a real collision was found and corrected (200-202 hit classical
  buses 72-74 under the +128 shift).
* §2.4 (D1's remaining tables) is **done**: all 30, no stand-in.
* §2.5's TAPE Lean side, the **NV passthrough** and the **production parameter** are now done
  (`results/pq-nv-tape/README.md`): the cached root is in the statement V_d checks, `maxLog` is a vk
  field enforced in the proof shape / NV / V_d, and the production LogUp budget is 2^30.  What
  remains is wiring `maxLog` from the ported tables and the host-wire tables' commitments.
* §2.1's HOST chip is a **first slice**; the gas-invariant generalisation and `HOSTB` remain.
* §2.2 is **decided**: separate signature layer.
* §2.6's shape is stated (`JoinFold.JoinStmt`); the proof needs the HOST work.

So the critical path is now: **host gas invariant -> host bytes -> contract-data storage ->
runCall fold -> NV tape passthrough.** That ordering is the lane table in `docs/HANDOVER.md`.

## 5. Honest sizing

| milestone | work | confidence |
|---|---|---|
| D1's 7 tables on PQ + natural heights | 3–5 days | high |
| statement plumbing (TAPE, interaction cap, height caps) | 3–5 days | high |
| `holdsP_of_swirl` composition | 4–6 days | high |
| HOST chip + buses + spec simulation | 10–15 days; **first slice done**, gas-invariant generalisation remains | medium |
| Ed25519/SHA-512 AIR | weeks; **costed at 1.5 M cells/sig**, separate-layer recommended | medium |
| the join + coverage theorem | 15–25 days | low |
| **A: `G_α` chunk, <300 KB, end to end** | **~2–3 months** | medium |
| segmentation/recursion to 1 Pgas + a 290× measurement | unknown, research | low |

The 293,077 B number is real, but it is the **recursion tail only**. Stating "1 Pgas under 300 KB"
as achieved would be false by the join (2.1–2.3) and by 290× of unmeasured scale (B).
