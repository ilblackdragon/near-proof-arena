# Extrapolation to 1 Pgas: per-node accounting, and why it is not a per-proof union

Task `p2-tail`/`t5`. Companion to `../pq-agg-depth-law/README.md` (the measurements) and
`docs/logs/pq-1pgas-aggregation-tree-plan-2026-10-20.md` §8.

**Scope warning first.** Everything measured in this lane is at **test query targets**
(10 query bits) and over **Fibonacci `SegAir` fixture leaves**. The two measured artifacts
that *are* at production targets are the delivered chunk chain (`runs/opt-baseline-8`,
L1–L5) and the final packet (299,967 B). Any number below is labelled with which of the
two it rests on. **No production-target aggregation node has ever been proved.**

## 1. The measured anchors

### 1.1 Node geometry (test targets, 10 query bits)

| node | children kind | proof B | program rows | NvAir h | prove s | peak RSS |
|---|---|---:|---:|---:|---:|---:|
| N1 | App (segment) | 124,201 | 16,598 | 2^17 | 12.6 | 3.5 GB |
| N2 | Node | 132,301 | 89,564 | 2^20 | 106 | 18 GB |
| N3 | Node | 132,301 | 95,974 | 2^20 | 107 | 17.6 GB |
| N4 (root) | Node | 132,301 | 95,974 | 2^20 | 119 | 17.8 GB |
| flat 13-to-1 | App | 133,357 | 104,614 | 2^19 | 75.5 | 12.2 GB |

Depth ≥ 2 is a **fixpoint**: proof bytes are identical to the byte at depths 2, 3 and 4,
as are all four components. Only the first transition (N1 → N2, +6.5 %) moves the size.

### 1.2 Per-node cost at production targets (the real anchor)

The delivered chunk chain is a 1-child NV chain at production targets. Its per-level
numbers are the only production-accurate per-node costs that exist:

| level | proof B | prove s |
|---|---:|---:|
| L1 | 374,105 | 462.30 |
| L2 | 374,563 | 481.78 |
| L3 | 372,001 | 552.92 |
| L4 | 373,177 | 459.38 |
| L5 | 374,521 | 582.17 |

**mean 507.7 s, range 459.4–582.2 s, and ~373 KB per level.** Two facts follow and they
are the crux of the whole extrapolation:

1. A production NV node is **~40× slower** than a test-target depth-1 node (507.7 s vs 12.6 s).
   Using test-target times to extrapolate 1 Pgas understates the cost by roughly that
   factor. Both are given below, clearly labelled.
2. A production NV proof is **~373 KB — already 24 % over the 300 KB cap.** The only
   artifact under the cap is the *final* layer (299,935 B), and it is under the cap because
   it sets `program_part = false` (`main.rs:249`) while every chain level sets
   `program_part = true` (`main.rs:121`). The root of a tree behaves like the final layer,
   not like a chain level.

## 2. Per-node accounting at S

For a binary tree over S leaves padded to `2^d`, the node count is:

* level-1 nodes (App children): `2^(d-1)`
* level ≥ 2 nodes (Node children): `2^(d-1) − 1`
* total: `2^d − 1`

Serial cost and RAM-bound makespan (6 nodes concurrently at 18 GB on this 125 GB host):

| target | S | padded leaves | depth | nodes | serial @ test | serial @ prod (507.7 s) | makespan @ prod, 6-way |
|---|---:|---:|---:|---:|---:|---:|---:|
| `G_α` exact | 13 | 13 (flat) | 1 | **1** | **75.5 s** | not measured | — |
| 1 Pgas, 2^23 ops/seg | **146** | 256 | 8 | 255 | 4.2 h | **36 h** | **6.0 h** |
| 1 Pgas, 2^22 ops/seg | 291 | 512 | 9 | 511 | 8.5 h | **72 h** | **12 h** |

**Only 146 and 291 are live counts.** The 1,880 / 3,760 rows that used to sit here were a
units error: they divided a width-equivalent cell total by a *main*-cell segment size, and the
ratio between the two is exactly the W-eq→main-cell exchange rate (494/38 = 13.0, 995/38 =
26.2). `146 × 13.0 = 1,898` and `146 × 26.2 = 3,823` reproduce the old range exactly. Derivation:
`docs/logs/pq-agg-tail-2026-10-22.md` §7 item 5. Both live counts are far past the per-proof
union bound's failure point (S ≈ 103–118), so the correction changes labour, not soundness.

Production columns are `nodes × 507.7 s` (the measured mean of L1–L5), rounded to whole hours;
an earlier draft computed them at a flat 500 s and is corrected here. The `serial @ test`
column mixes both measured node classes: `2^(d-1)` level-1 nodes at 12.6 s plus `2^(d-1) − 1`
level ≥ 2 nodes at ~106 s.

Critical path (one node per depth level, unlimited RAM): **13 min / 18 min** for
S = 146 / 291 — i.e. **the tree is embarrassingly parallel; it is RAM-bound, not
depth-bound.** At 6 concurrent nodes the makespan is ~1/6 of serial; with 64 GB/node
headroom (the `pq-stream-g2` runs use 60 GB) concurrency drops and the makespan doubles.

**The honest 1 Pgas statement at production targets: 48–96 h on this one host, or ~6 h
for the model's S=146 shape — and that is with zero production-target node measurement,
so the ±2× from `m`/query schedule is live.** This is a schedule, not a proof.

### 2.1 Bytes at S

**Bytes do not grow with S or depth.** The root is a single fixpoint node: 132,301 B at
test targets, and it would be the final-layer shape at production targets (~300 KB class,
because it drops `program_part`). So:

> the 300 KB bound is **not** a function of segment count or tree depth. It is a function
> of the **final layer's shape** only (query schedule, unwind factor `m`, digest width,
> program-part inclusion).

The measured D0a packet already sits **33 B** under the cap, and the two valid packets we
hold straddle it (299,967 B and 300,765 B). So the size risk is entirely in that final
shape, not in the tree. Widening the tree cannot fix a 33 B margin, and it cannot break it
either.

## 3. Why this must not be accounted as a per-proof union

Doing it as a union is the natural, wrong thing: each node proof is independently
extracted, so with `n` of them the failure probability adds.

The measured per-proof figures are **2^−134.88** (`bound-base.out`; base and inner z = 24,
final z = 32) and **2^−134.68** (uniform z = 32, `bound-base-z32.out`), both on the pinned
`seg-v1` shape. A union over `n` nodes gives `2^−(per-proof − log2 n)`:

| nodes `n` | S | union (z split) | union (uniform z=32) | verdict vs 2^−128 |
|---:|---:|---|---|---|
| **1** | 13 | **2^−134.88** | **2^−134.68** | pass — *this is the measured flat node* |
| 12 | 13 | 2^−131.30 | 2^−131.10 | pass — same S as a padded binary tree |
| 102 | 103 | 2^−128.24 | 2^−128.00 | borderline (uniform) |
| 117 | 118 | 2^−128.01 | 2^−127.81 | **FAIL** (uniform) |
| 145 | 146 | 2^−127.70 | 2^−127.50 | **FAIL** |
| 295 | 296 | 2^−126.68 | 2^−126.48 | **FAIL** |
| 291 | 292 | 2^−126.69 | 2^−126.49 | **FAIL** |

(An earlier version of this table also listed 1,880 and 3,760. Those are not live segment
counts — see the note in §2 — so they are dropped here; the trend they illustrated is already
established by 118 and 146.)

**The union dies at 103–118 nodes (S ≈ 103–118), not at 295.** The plan, the obligations
doc and the base README all quote "2^−126.5 at 295 proofs". That number is arithmetically
right (it is the *uniform*-z figure at n = 295: 134.68 − log2 295 = 126.48) but it is not
the failure point — it is a point well past it. The crossover is
`2^(134.88−128) = 117.8` nodes with the z split, `2^(134.68−128) = 102.5` with uniform
z = 32. So:

* the union is valid for `G_α` (S = 13, 12 nodes: 2^−131.30 ✓);
* the union is invalid for **every** 1 Pgas shape, including the model's smallest
  (S = 146, 145 nodes), not only the largest.

That sharpens the plan's claim in the direction that matters: there is no "small-ish
1 Pgas tree" for which the cheap accounting works. It also means the ~8-bit target raise
the plan contemplates has to be applied from S ≈ 103 upward, not only at the top of the range.

Why it is not a union, and what has to replace it:

* Every node proof certifies a statement about the **same** chunk's segment range, and the
  root statement is a fold over one database of leaves. The tree is a *proof
  transformation*, not `n` independent claims. A union over it charges the same
  knowledge-soundness error `n` times for one statement.
* The correct accounting applies the extraction theorem **once** to the family of vks
  (`NodeOK`, DESIGN §9.1), giving a single `2^−128` for ≤ 2^64 quantum queries — what the
  plan calls N1/N3.
* That theorem is **not proved**. `pq-arbitrary-aggregation-proof-obligations-2026-10-19.md`
  records it as paper-level (S-19/S-28); the Lean induction
  (`ProofTree.certified_root`, `node_count_irrelevant`) is done, but the single application
  of the QROM extraction theorem is not.
* Therefore: **until `NodeOK` is discharged, the honest soundness claim for any tree above
  S ≈ 118 is "fails" — the union is the only *proved* accounting we have, and it fails.**
  The tree's byte economy is real and measured; its soundness at 1 Pgas is currently an
  open obligation, not a result.

An alternative that does not need the theorem: raise every layer's target ~8 bits so the
union clears 1 Pgas. That costs bytes and time at every node, and it is not free. Note the
crossover correction above: the raise has to hold from S ≈ 103 upward, so it is a change to
every production node, not a tail fix.

## 4. What the honest summary is

| claim | status |
|---|---|
| S=13 (`G_α`) aggregation node is 133,357 B at test targets | **measured** (flat 13-to-1) |
| Node bytes are flat in depth (depth 2 = 3 = 4, to the byte) | **measured** |
| Node cost is linear in node count; depth is a fixpoint | **measured** (test targets) |
| Tree is RAM-bound, ~6 concurrent nodes on this host | **measured** (18 GB/node) |
| A production-target aggregation node exists | **NO — never proved** |
| A production node is ~507.7 s mean (459.4–582.2 s) and ~373 KB (from the chunk chain) | **measured, 1-child** |
| 1 Pgas tree ≈ 48–96 h serial-equivalent-makespan on one host | **extrapolated from the 1-child anchor, ±2×** |
| 1 Pgas root fits 300 KB | **plausible, not measured** — depends on final shape only |
| Per-proof union soundness at 1 Pgas | **FAILS from S ≈ 103–118 upward** |
| Single-database theorem (`NodeOK`) | **not proved** |
| Leaves are real NEAR segments | **NO — Fibonacci fixtures** (P9/P10/P11) |

The one-line version: **the tree's *size* problem is solved and its *soundness* problem is
not; the two are independent, and 1 Pgas is blocked on the second, not the first.**
