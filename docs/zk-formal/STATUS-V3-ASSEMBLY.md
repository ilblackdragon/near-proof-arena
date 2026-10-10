# Assembly of the v3 succinct proof — status (2026-10-09, `agent/v3-assembly`)

This lane turns the large body of conditional v3 lemmas into a single assembled
AIR and a single admission certificate.  Read `docs/zk-formal/V3-D0-DESIGN.md`
and `docs/HANDOVER.md` first.

## 1. What is now proved

* **`nearAirV3` exists** (`zk-formal/ZkFormal/NearV3/Assembly/NearAir.lean`): the
  concrete `AirP` every obligation is stated about.  25 tables in fixed order —
  two SHA-256 instances (needed for `B0 = 2,000,000`, V3-D0-DESIGN §3.1), the six
  trie tables (`nodeV3 … upsV3`), three ChaCha tables, five scheduler tables, six
  receipt tables, the queue-value parser `qvV3`, and v1 `mrk`
  (public-index-translated to `PH_N`/`PH_OUT`) and `sort` at v3 heights.
  `pubSegs = Public.preparedSegments` (the nine concrete prepared-statement
  segments), `maxPub = 64 MiB`, `numBuses = 77`, `numPub = 202`.
* **Static facts** (`Assembly/NearAirCheck.lean`): `nearAirV3.wf 16 = true` and
  `nearAirV3_npOkPg g` for `1 ≤ g ≤ 3` (P2 `auxGroup`), by kernel evaluation.
* **Size** (`Assembly/NearAirSize.lean`): the aligned deduplicated bound at
  `auxGroup = 2` is `6,276,897` bytes; `nearV3_size` gives
  `sizeBoundD ≤ 6,276,897` on every admissible roll-in-aligned header.
* **Wire codec** (`Assembly/HintCodec.lean`): `Hint.encode = u32 n ‖ borshBytes body`,
  round trip `Hint.decode_encode`; `split`/`join` framing with `split_join`.
* **The admission certificate** (`Assembly/NearAdmission.lean`):
  `nearV3_admission` composes `Prover.Np.G.admission_v2H` at `auxGroup = 2` with
  the concrete codec, the size bound, and the kernel-checked `NpOkPg`/`NVu`/profile
  numerics.  `nearV3_admission_with_extract_b` additionally discharges the
  semantic **soundness** premise from `ExtractV3Stmt` through the proved
  `factorSound` (`Assembly/FactorSound.lean`, axioms `{propext, Classical.choice,
  Quot.sound}`).  All new theorems have exactly those axioms.

## 2. Decisions taken (item 0)

The ChaCha word bound and Merkle-path budget were **already decided** on
`lane/v3-domain-bounds` and are merged here:

* **A9 `e.chacha_words`, `W0 = 770,000`.**
* **A10 `w.path_depth`, `Dp0 = 32`.**
* **`B0 = 2,000,000`** (user decision), **two SHA instances**, **`auxGroup = 2`**,
  honest roll-in-aligned traces so `nearV3_size` applies with a ≥ 700 KB margin.
* `ZkFormal.NearV3.Rcpt.SrcpDepth` and `ZkFormal.NearV3.Sched.Complete.WordBound`
  carry the A9/A10 height arithmetic.

## 3. Remaining obligations (the whole end-to-end gap)

Exactly **three** named statements, all about `nearAirV3`, plus the Rust prover.

### 3.1 `ExtractV3Stmt` (soundness; `Assembly/NearAdmission.lean`)
```
∀ B cb h p oh tr, prepD0 cb h = .ok p →
  HoldsP nearAirV3 (Udr.pubOf Fp (Public.preparedBytes p oh)) tr → ∃ k x, GoodV3 B cb k h p x
```
This is v1's `extract_of_views` scaled to 25 tables.  **Done:**
* `TableLocal` for every table from `HoldsP` (`Assembly/ExtractV3.lean`, the
  `*Local` lemmas);
* all eleven per-table views instantiated at the fixed table indices
  (`Assembly/ViewsV3.lean`, `Assembly/ExtractV3.lean:rcptV3_view_nearAir`) —
  `node3_view`, `walk3_view`, `head_view`, `val_view`, `uniq_view`, `ups_view`,
  `acctV3_view`, `akey_view`, `bnd_view`, `size_view`, plus `RcptV3ViewStmt` for
  `nearAirV3` from `RcptV3Proof.extract_prepared_view`.

**Remaining:** the `LinkV3Stmt` (`Assembly/LinkV3.lean`) joining the view records
into `GoodV3`, using the `Link/` folder (`root_tau`, `build_tau`, `walks_tau`,
`post_tau`, `store_hashFunctional`, `post_sets_tau`, `Chain3`, `PerTau3`) and the
`Assembly/` semantic modules (`Execution`, `ImplicitComplete`, `SourceComplete`,
`HeaderCompose`, `NativeGoodGap`).  This is v1's `Near/Extract/Statements.lean`
`LinkStmt`; it is the `link` work package.

### 3.2 `RenderV3Stmt` (completeness)
```
∀ B cb w, checkD0a B cb w = .ok () →
  ∃ h p tr, prepD0 cb h = .ok p ∧ HoldsP nearAirV3 (Udr.pubOf Fp (Prep.encode p)) tr
    ∧ (Hint.encode h).length < 2^32 ∧ (VdP nearAirV3).headerOk (trHdr nearAirV3.toAir tr) = true
```
Honest trace construction.  `Render/Padded*.lean` has aligned generators for
head/value/boundary/access-key/node/uniq/walk; the remaining tables
(`rcptV3`, `srcpV3`, `qvV3`, `upsV3` render M7d, `mrk`/`sort`, ChaCha/scheduler)
and the whole-trace assembly are **missing**.

### 3.3 `AlignedV3Stmt` (roll-in alignment)
The honest trace's headers land on regular arity-8 commit layers
(`Size/PadHeader.lean` has `rollAligned_of_trace_mod3`); needs the concrete
`traceOf` from 3.2.

### 3.4 Heights (item 5)
`honestTrace_fits`/`FitsV3Stmt`: derive each `tr.log t ≤ nearAirV3.tables[t].maxLog`
from `InD0a` (A1/A7/A8/A9/A10).  The scheduler arithmetic exists
(`Sched/Complete/Height.lean`, `heights_prep`); the trie/rcpt height bounds are
carried in the view types (`NodeWf3.rows`, `WalkWf3`, …).  Downstream of 3.1/3.2.

### 3.5 Rust prover (item 8)
`np-udr-stark-v2` does not exist in Rust: no `AirP`/`pubSegs`, no `nearAirV3`
trace generators, no candidate package.  The only v3 packages are re-execution.

## 4. How it fits

`HoldsP nearAirV3 ⇒ GoodV3 ⇒ RelD0a` (`extract` + `factorSound`) is soundness;
`RelD0a ⇒ HoldsP` is completeness; both feed `nearV3_admission_with_extract_b`.
Everything protocol-level, size-level and static is already discharged.  The
remaining work is the per-table view/link/render volume (items 2–5), the Rust
prover (item 8), and governance (item 9).

## 5. Parallelisation: work packages for other agents

The assembly layer is **frozen**; every package below plugs into a fixed
interface in `Assembly/NearAir.lean` (`nearAirV3`, its table indices in
`Assembly/ExtractV3.lean`) and the three statements in `Assembly/NearAdmission.lean`
(`ExtractV3Stmt`, `RenderV3Stmt`, `AlignedV3Stmt`).  None of the packages below
needs to change the frozen AIR, the spec (`NearSpecV3`) or a signed challenge.
Work in one worktree per agent, one lane branch; integrate to `agent/v3-assembly`.

| pkg | item | deliverable | interface it fills | self-contained in | deps |
|---|---|---|---|---|---|
| **Rust prover** | 8 | `np-udr-stark-v2` Rust prover + a candidate package that emits a real proof | the model `npVerifierP … nearAirV3 split prepV3b` (already exist); table `Air` export format in `docs/zk-formal/FORMATS.md` | `examples/np-udr-stark-v2/` (new), `runners/` | **none** — the AIR, buses and public segments are frozen |
| **rcpt-view** | 2 | `RcptV3ViewStmt` (`Rcpt/Extract/RcptView.lean:215`) | per-table view | `zk-formal/…/Rcpt/Extract/` | none |
| **srcp-render** | 2 | `srcpV3` render (`Rcpt/Render/Srcp/**`) | render for `T_SRCP` | `zk-formal/…/Rcpt/Render/` | none |
| **qv-render** | 2 | `qvV3` render (`Qv/Candidates/**`) | render for `T_QV` | `zk-formal/…/Qv/` | none |
| **ups-render** | 2 | `upsV3` render M7d (`Render/Ups/**`, `cPlan/cFields/cBytes/cMem`) | render for `T_UPS` | `zk-formal/…/Render/Ups/` | none |
| **link** | 3 | `LinkV3Stmt` + `goodOfViews` ⇒ `ExtractV3Stmt`, composing `Link/*` into `GoodV3` | `ExtractV3Stmt` | `zk-formal/…/Assembly/` | needs the per-table views (already: node/walk/head/val/uniq/ups/acct/akey/bnd/size) |
| **heights** | 5 | `FitsV3Stmt` = `honestTrace_fits` for `nearAirV3`, from `InD0a` (A1/A7/A8/A9/A10) | the `maxInner` side condition of `admission_v2H` | `zk-formal/…/Assembly/` | view types (frozen); `Sched/Complete/Height.lean` exists |
| **render-assembly** | 4 | `renderV3` + `RenderV3Stmt` + `AlignedV3Stmt` | completeness half | `zk-formal/…/Assembly/`, `Render/` | per-table renders (head/val/bnd/akey/node/uniq/walk exist; others from pkg above) |
| **governance** | 9 | add D0a tier + weights, freeze once, sign/register/deploy, judge run | — | `challenges/`, `oracle/`, `docs/` | a candidate (pkg Rust prover) |

The **critical path** is `link` → `render-assembly` → governance; the **Rust
prover** is fully independent and can start immediately.  The two integration
targets are `lake build ZkFormal.V3.Integration` (proofs) and the candidate
build recipe (Rust).
