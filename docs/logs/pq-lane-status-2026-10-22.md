# Lane status audit, 2026-10-22 04:30 UTC

Checked against artifacts (builds, `.olean` presence, axiom audits, git state), not commit
messages. This corrects two verdicts in `pq-d3-chain-gap-2026-10-21.md`.

## Live activity right now

| where | state |
|---|---|
| `pq-host-memio` worktree | **actively editing**, 22 uncommitted files, `HostChip.lean` and `MemIO.lean` touched within 8 min. MEMIO link (`BufOK`, `HeapOK`, `heap_retime`, `ch_pair_vacuous`). Nothing committed; branch tip is still `c6761629d`. |
| `pq-hostfinal` worktree | **actively editing**, one untracked file `RipemdAir.lean` (680 lines), written 4 min before this audit. |
| all other worktrees | clean or stale (see table) |

Two lanes are live. Everything else is parked.

## The six links, re-scored

| # | link | 2026-10-21 | now |
|---|---|---|---|
| 1 | real D3 contract in the Wasm domain | missing | **half done**: storage hosts landed; `if` spec steps landed; `if` AIR/checker **not started by anyone** |
| 2 | storage hosts | absent | **done** (`ce968bfc3`, KAT 98/98, tamper 90/90) |
| 3 | D2/D3 chunk AIR | missing | **unchanged, absent** — no `nearAirV3D2/D3`, no `rcptV3D2/D3` in any worktree |
| 4 | D3 state render | Lean-only | **unchanged** — `RealStoreMatchesTables` still stated; `upsert` still `[0,15]` |
| 5 | the join Wasm ⇄ state | "vacuous, does not compile" | **corrected: it is a real conditional and it compiles** |
| 6 | recursion over a D3 base | blocked | **unchanged** — `Variant` is `D0a \| D1` only; D0a packet 299,967 B stands |

## Correction 1: the join is not vacuous any more

The gap log said `coverage : ArmAgrees → StateSide → RelD3` "assumes its own conclusion" and
"does not compile". Both were true of the **untracked worktree draft** on 2026-10-21 15:00. What
landed as `f8c4ceb91` (16:07, on main) is different:

```lean
theorem coverage (cfg) (cb w) (sa : ActCtx → ActSt → AR → Base → Except String (ActSt × AR))
    (hagree : ∀ …, sa c st ar (.fcall m a g d) = (d3Hooks cfg).functionCall c st ar (.fcall m a g d)) :
    checkD2Core (patchArm cfg sa) … = checkD2Core (d3Hooks cfg) …
```

`sa` is **arbitrary** — it is the state proof's answer function, not `d3Hooks`. `patchArm` builds
the hook that keeps the spec's answer everywhere except `.fcall`, and `patchArm_eq_d3` shows the
patched hook *is* `d3Hooks`. So the theorem's content is "the chunk pipeline reaches the call arm
only at `.fcall`", which is the real fold, and it is not `rfl`.

Verified here [K]: `coverage` and `coverage_pv86` compile, axioms
`[propext, Classical.choice, Quot.sound]`; `Coverage.olean` exists and the module is in the root
import list (`ZkFormal.lean:378`). The earlier `maxHeartbeats` timeout is gone.

**What is still not proved** (and the file says so): `hagree` (the Wasm half — needs the
code/`ctx` binding `CodeBound`) and `hstate` (the state half — needs the D1→D3 witness lift, since
`RelD1a`'s witness is Transfer-only and code-free). Those are the two named obligations, not
hidden assumptions. That is a materially better state than "vacuous".

## Correction 2: `pq-hostfinal` closed the receipt encoder, and the claim holds

`bdf80d018` claims the eleven `promise_*` encodings are done. Verified here [K]:

| lemma | axioms |
|---|---|
| `encReceipt_eq_encode` | `[propext, Quot.sound]` |
| `encReceipt_len` | `[propext, Quot.sound]` |
| `promise_encodings_cover` | **none** |
| `promise_encodings_cover_discriminates` | `[propext]` |
| `remaining_eleven_closed` | `[propext, Quot.sound]` |

`Receipt.olean` and `Encoder.olean` exist and both modules are in the root import list
(`ZkFormal.lean:395,398`), so the root-import trap does not apply here. The structural finding is
real and worth keeping: the whole receipt body is one `BField` list, so the envelope is a single
`flatMap` and the `PBE` table needed no change — the "empty class row" is a new *instance*, not a
new class kind.

Still stated, unchanged: `FCPlanIsTrace`/`PCPlanIsTrace` (generator obligations), `ActionBytesAre
HostBytes` (needs the HOSTB→MEMIO binding), `ActionEncodingIsBorsh` (entry direction only), and the
`RIDS`/`SRC`/`RCL` + SHA half — which the README prices at 69 % of the cost.

## What nobody is working on (the actual critical path)

**The `if` AIR half.** Confirmed by search across every worktree and the main checkout: no
`IfAir`, no `fIf`, no `analyzeIf`, no `checkModuleIf`, and **no consumer of `step_if`/`step_else`**
anywhere. `StepIf.lean` is still only on `lane/pq-if2`, not merged to main.

This is the single change that turns "storage works but no real contract is in domain" into "a real
D3 contract is in domain", and it is unclaimed. The four remaining pieces are enumerated in
`pq-d3-chain-gap-2026-10-21.md` §7 and `pq-d3-air-2026-10-22.md` §3.

## Also unclaimed

* **D2/D3 chunk AIR** (link 3) — the long pole. `Variant` in the prover is `D0a | D1` only, so
  even the *driver* has no D3 path.
* **D3 state render + `upsert` parameterisation** (link 4) — needs a render/AIR change, not a proof.
* **`hagree` / `hstate`** — the two open obligations of the join, each owned by a different side.

## In-flight lanes that need a merge decision

| branch | tip | what it is |
|---|---|---|
| `lane/pq-d3-air` | `81206a072` | storage hosts + HOSTB payload fix + `storkat`; **green**, pushed |
| `lane/pq-if2` | `55fab1e0f` | `StepIf` proved; **green**, pushed |
| `lane/pq-hostfinal` | `bdf80d018` | eleven promise encodings; **verified green here** |
| `lane/pq-chunk-perf` | `b38d91e09` | D0a recursion packet + profiling replays |
| `lane/pq-host-ctx` | `0594bba49` | content already on main via `586a7adcf`; branch not an ancestor but files agree |

`pq-hostfinal` and `pq-d3-air` are independent (different files, different families) and both are
verified green, so they can merge in either order. `pq-host-memio`'s uncommitted MEMIO work will
conflict with `pq-d3-air`'s `HostChip.lean` **only** if it also edits the `hostFns` line — it does
not today (it edits the HOSTB section at line 399+), but it is live, so merge it after it commits.
