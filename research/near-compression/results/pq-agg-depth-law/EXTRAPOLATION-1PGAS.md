# Extrapolation to 1 Pgas: per-node accounting, and why it is not a per-proof union

Task `p2-tail`/`t5`. Companion to `../pq-agg-depth-law/README.md` (the measurements) and
`docs/logs/pq-1pgas-aggregation-tree-plan-2026-10-20.md` §8.

**Scope warning first.** Most of what is measured in this lane is at **test query targets**
(10 query bits) and over **Fibonacci `SegAir` fixture leaves**. The measured artifacts that
*are* at production targets are the delivered chunk chain (`runs/opt-baseline-8`, L1–L5),
the final packet (299,967 B), and — as of 2026-10-24 — **two production-target aggregation
nodes at depth 2 and one at depth 3** (§1.3). Leaves are still fixtures in every aggregation
run; §1.3's numbers say nothing about real NEAR segments. Any number below is labelled with
which artifact it rests on.

**CORRECTION 2026-10-24: "no production-target aggregation node has ever been proved" is
falsified, and so is the depth-8 size model that grew out of it.** A 2-child production
node at depth 2 proves and verifies (`AGG_DEPTH2_OK leaves=4`, **315,913 B**, 700.5 s,
18.76 GB) and depth 3 does too (`AGG_DEPTH3_OK leaves=8`, **322,027 B**, 752.2 s, 21.45 GB).
See `docs/logs/pq-agg-depth2-legal-2026-10-24.md` and logs
`results/pq-agg-prod-target/agg-d2-geom-ns19lb6.log`, `agg-d3-geom.log`. The measured depth
ladder in §1.3 replaces the "~16 KB per level, ~412 KB at depth 8" projection in this file's
earlier draft: the only measured same-tree increment is **4–6 KB, once**, because the
production depth law reaches its fixpoint at depth 3, not at depth 8.

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
This is a `log_blowup=3` result; it does **not** transfer to production, where the same
fixpoint argument lands one level later and at ~322 KB instead of 132 KB (§1.3, §2.2).

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
   not like a chain level — **but "behaves like" is not "is as small as"**: the measured
   depth-2 root also drops `program_part`, and still comes out at 315,913 B (§1.3). The
   difference between those two final-layer-shaped objects is 12 queries in the root's own
   schedule, not the `program_part` flag.

### 1.3 The production depth ladder (measured 2026-10-24)

Two production-target aggregation nodes now exist, and with them the first measured
per-depth increment at production geometry. Same lever set throughout (`NEARPROOF_DIGEST_BYTES=42`,
`NEARPROOF_COSET_LEAF=1`, 268-bit target); `ns18/lb7` at level 1, `ns19/lb6` from level 2 up.

| level | children | child's own schedule | its own schedule | proof B | comps | AIR `a1h` | prove s | peak GB |
|---|---|---|---:|---:|---:|---:|---:|---:|
| L1 | App, `2^18` | `[10,4,2]` | `[41,38,29,23]` = 131 | **254,863–256,879** | 309 | 17 | 447.2–569.6 | 9.4 |
| L2 | Node, `2^20` | `[41,38,29,23]` | `[46,41,31,25]` = 143 | **315,913 / 317,845** | 8,747 | 21 | 700.5 (d2 run), 717.0 / 903.5 (d3 run) | 19.6 / 18.6 |
| L3 | Node, `2^20` | `[46,41,31,25]` | `[46,41,31,25]` = 143 | **322,027** | 9,911 | 21 | 752.2 | 21.5 |

Sources: `results/pq-agg-prod-target/agg-d3-geom.log` (L1_0–L1_3, L2_0, L2_1, L3_0) and
`agg-d2-geom-ns19lb6.log` (the same L2_0, **byte-identical at 315,913 B** — prover
determinism on identical input). L2_0's components are `gkr=37592 relations=24772
stacking=5920 whir=247430`; the base final layer's are `gkr=37592 relations=24292
stacking=6976 whir=230876`. Its **non-WHIR sections total 68,483 B against the base final
layer's 69,059 B** (both = total − whir, including the 199 B of framing and public values),
so the agg root is final-layer-shaped rather than chain-level-shaped — a chain level is
~373 KB in total. That is the measured confirmation of §1.2 item 2, but only in aggregate:
`gkr` is byte-identical at 37,592 while `relations` is +480 B and `stacking` is −1,056 B, so
the agreement is in total, not section by section. The whole 15,978 B gap to the base final
layer is the WHIR section (+16,554 B, offset by −1,056 stacking and +480 relations).

Two readings in that table matter, because they are why the naive depth-8 extrapolation is
wrong:

* **`NV_QCOST` is the cost of verifying the children, not the node's own proof.** L2 prints
  `NV_QCOST ... queries=41,38,29,23`, which is its *children's* schedule; its own is the
  `PARAMS` line's `[46,41,31,25]`. So `merkle_nodes = 7,320 = 2 × 3,660` is 2 children × 131
  child queries, and the node's own 143 queries appear in its WHIR byte count, not in its
  SHA compressions. Reading these the other way round makes the 143→131 query lever look
  double-countable, which it is not: the child schedule sets `comps`, the node's own schedule
  sets `whir` bytes.
* **The depth increment is a schedule transition, not a depth cost.** L2's children run 131
  queries and L3's run 143, and the query schedule — hence the SHA AIR — is a property of the
  *child's* params. So L2→L3 moves by +1,164 comps for exactly one reason: the child schedule
  changed from `[41,38,29,23]` to `[46,41,31,25]`. Every level ≥ 3 uses `[46,41,31,25]` for its
  children, so the production fixpoint is reached **at depth 3**, not at depth 8. This is the
  same argument the test-target law used (§1.1), arriving one level later because production
  adds a second query schedule.

Measured per-level byte increments at production geometry, therefore:

```
L1 -> L2 :  315,913 - 255,913 =  60,000 B   shape change: App 2^18 -> Node 2^20, 131 -> 143
            315,913 - 256,879 =  59,034 B   (against the largest measured L1 sibling)
L2 -> L3 :  322,027 - 317,845 =   4,182 B   same-tree, L3's larger child  (L2_1)
            322,027 - 315,913 =   6,114 B   same-tree, L3's smaller child (L2_0)
```

The L2→L3 rows are the only like-for-like depth steps and the increment is **4–6 KB, incurred
once**. The L1→L2 row is 59–60 KB but it is *not* a depth cost: it changes child kind (App
segment proofs → Node recursion proofs) and child stacking height (`2^18` → `2^20`) as well as
the query schedule, and it happens once at the bottom of the tree.

The "≈16 KB per level" figure that produced a 412 KB depth-8 projection is
`315,913 − 299,935`: the L2 node minus the *base packet's final layer*. Those two differ by
12 queries in a single node's own schedule — a size lever — not by one level of depth. It is a
seductive subtraction because both numbers are final-layer-shaped (§1.2 item 2), but the base
final layer is not a depth-1 tree node; it is the packet's own top layer over a chain.

## 2. Per-node accounting at S

For a binary tree over S leaves padded to `2^d`, the node count is:

* level-1 nodes (App children): `2^(d-1)`
* level ≥ 2 nodes (Node children): `2^(d-1) − 1`
* total: `2^d − 1`

Serial cost and RAM-bound makespan (6 nodes concurrently at 18 GB on this 125 GB host):

| target | S | padded leaves | depth | nodes | serial @ test | serial @ prod (507.7 s) | makespan @ prod, 6-way |
|---|---:|---:|---:|---:|---:|---:|---:|
| `G_α` exact | 13 | 13 (flat) | 1 | **1** | **75.5 s** | not measured | — |
| 1 Pgas, 2^23 ops/seg | **146** | 256 | 8 | 255 | 4.2 h | **36 h** → **45.6 h** (§2 correction) | **6.0 h** → **8–9 h** |
| 1 Pgas, 2^22 ops/seg | 291 | 512 | 9 | 511 | 8.5 h | **72 h** → **91 h** | **12 h** → **15–18 h** |

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

**CORRECTION 2026-10-24: the 507.7 s column is a 1-child anchor and understates a 2-child
node.** Measured 2-child production times are 717.0 / 903.5 s (two L2 nodes, same geometry,
byte-different children) and 752.2 s (L3) at 18.6–21.5 GB peak. So for S = 146 / depth 8 the
schedule is, per class: 128 L1 at 447.2–569.6 s (**65,075 s** at the 508.4 s mean), 64 L2 at
810.3 s (**51,856 s**), and 63 nodes at level ≥ 3 at 752.2 s (**47,376 s**) — total
**164,307 s ≈ 45.6 h serial**. At 5 concurrent nodes (21.5 GB peak against 114 GB available)
that is **≈9.1 h**, and at 6-way **≈7.6 h**. So the "36 h serial / 6.0 h makespan" row above is
low by ~27 % in serial and ~1.5 h in makespan. Use **≈46 h serial / ≈8–9 h at 5–6-way**, and
treat the L2 spread (717 → 904 s, +26 % at identical geometry) as the honest uncertainty on
every level ≥ 2. Concurrency is 5, not 6: the 21.45 GB L3 peak leaves no room for a sixth.

Critical path (one node per depth level, unlimited RAM): **13 min / 18 min** for
S = 146 / 291 — i.e. **the tree is embarrassingly parallel; it is RAM-bound, not
depth-bound.** At 6 concurrent nodes the makespan is ~1/6 of serial; with 64 GB/node
headroom (the `pq-stream-g2` runs use 60 GB) concurrency drops and the makespan doubles.
The measured 21.45 GB peak for a depth-3 node is the binding number: on 114 GB available that
is **5 concurrent**, so the tree's practical makespan is serial/5, not serial/6 — which is what
the §2 correction above uses.

**The honest 1 Pgas statement at production targets: ~46 h serial / ~8–9 h at 5–6-way for
the S=146 shape.** The earlier "48–96 h serial, ~6 h makespan" band bracketed a 1-child anchor
(507.7 s) that understates a 2-child node by ~27 %; with the measured 2-child times the serial
figure is 45.6 h and the makespan is 8–9 h, not 6 h. The ±2× from `m`/query schedule remains
live on top of that (the L2 sibling pair alone spans 717 → 904 s at identical geometry), and
levels ≥ 4 are still pure projection. This is a schedule, not a proof.

### 2.1 Bytes at S

**Bytes do not grow with S, and at test targets they do not grow with depth either.** The
root is a single fixpoint node: 132,301 B at test targets. So:

> the 300 KB bound is **not** a function of segment count. At production geometry it is also
> not a function of depth beyond level 3; it is a function of the **node's own query
> schedule and stacking height**, i.e. of the final layer's shape (query schedule, unwind
> factor `m`, digest width, program-part inclusion).

The measured D0a packet already sits **33 B** under the cap, and the two valid packets we
hold straddle it (299,967 B and 300,765 B). So the size risk is in that final shape, not in
the number of leaves. Widening the tree cannot fix a 33 B margin, and it cannot break it
either.

### 2.2 CORRECTION 2026-10-24: at production geometry the law is flat from depth 3, at ~322 KB

The test-target fixpoint above is real but its *value* does not transfer: it was measured at
`log_blowup=3`. The production ladder (§1.3) gives the production fixpoint, and it is not
132,301 B and not 412 KB:

| depth | root proof | basis |
|---:|---|---|
| 1 | 254,863–256,879 B | measured (App-child nodes, 131 queries, `2^18`) |
| 2 | **315,913 / 317,845 B** | measured (`L2_0` / `L2_1`) |
| 3 | **322,027 B** | measured (`L3_0`) |
| 4–8 | **≈322 KB, band 318–355 KB** | projected — `comps` flat at 9,911 from L3 up |

Why flat from 3, in one line: `L3_0_GEOM merkle_nodes=7998 leaf_blocks=1913 comps=9911` is
exactly `2 × (46·30 + (41+31+25)·27)` = 2 children at 143 queries, and every level ≥ 3 feeds
its parent the same 143-query child. So `comps` — and therefore the AIR height — is a
fixpoint at 9,911 from depth 3 upward. Bytes follow `comps`, so they are flat too, up to the
measured ~2 KB transcript/program-row wobble that makes `L2_0` 315,913 B and `L2_1` 317,845 B
at identical geometry.

**The depth-8 model to quote is this one, not the 412 KB linear model:**

```
A(d) = A(3) + sum_{k>=4..d} delta_k ,  delta_k -> 0 as the child schedule stops changing
     = 322,027 B + (d - 3) * ~0 B   =>   A(8) ~= 322 KB   (band 318-355 KB)
```

Against the "linear, Δ = 16 KB/step" model circulated on 2026-10-24:

```
A(d) = A(1) + (d - 1) * 16,000  =>  A(8) ~= 412,000 B          REFUTED as a size law
```

It is refuted on two counts. First, its anchor `A(1) = 299,935 B` is the **base packet's
final layer**, a 1-child node at `2^20` that drops `program_part`; a depth-1 *aggregation*
node measures 254,863–256,879 B at the same production levers. Second, its `Δ = 16 KB` is
`315,913 − 299,935`, which is 12 queries in one node's own schedule — a lever — not a depth
step. The only measured same-tree step is L2→L3 at 4,182 B (against the larger child), and
it does not repeat because the child schedule stops changing at L3. Even the most pessimistic
reading of the measured data — re-applying the full 6,114 B at every level — gives
`322,027 + 5 × 6,114 = 352,597 B`, still ~60 KB below 412 KB and, more importantly, still a
**bounded** result rather than an extrapolation that grows without a mechanism.

Three consequences the objective should take from this:

1. **Depth does not compound the size problem; it bounds it.** Depth 2 is already 15,913 B
   over cap. Depth 8 projects ~22 KB over, not ~112 KB. The over-cap gap is set at depth 2
   and then stops growing.
2. **Depth does not compound the legality problem either, in the favourable direction.**
   `comps = 9,911` against the `2^21` ceiling's 16,384 leaves is **39.5 % headroom**, and it
   is a fixpoint. The `2^21` geometry is legal through depth 8 by this model — a projection
   from one measured point plus an exact compression model, not a measurement.
3. **A separate final layer does not automatically fix the size.** The base final layer is
   299,935 B because its child is a `2^20`-stacked chain level with `program_part=true`, and
   it drops `program_part` itself. A final layer over a depth-8 root would verify a
   `2^21`-stacked child at 143 queries, so it lands in the same ~316–322 KB class. Whether a
   *1-child* final layer over a `2^21` root fits the cheaper `2^20` schedule (its compression
   count would be roughly half of a 2-child node's, ~4,956 against 8,747) is the single
   untested question that would decide it. **Untested.**

### 2.3 Verify time: measured for the artifact, NOT for any aggregation node

The objective treats verify time as first-class, so the honest state is:

* **The delivered artifact verifies in 1.46–1.58 s** at 32 threads (7.65–7.72 s pinned to one
  core), 365–496 MB peak — `VERIFY-PROFILE.md`, measured on the 299,967 B packet. That is the
  only verify time in this lane that is a *shipped* cost.
* **No aggregation node's verify time has been measured.** `AGG_DEPTH2_OK` / `AGG_DEPTH3_OK`
  include `engine.verify` (`crates/recursion/src/nv/circuit.rs`) but the test prints no timer
  around it, so the logs prove verification *happened* and say nothing about how long it took.
  A 2^21-stacked, 143-query, 315,913 B proof is the largest object this lane has ever verified,
  and its verify cost is an open measurement.

The bounded statement available without a new run: verify scales with the WHIR query count and
the section sizes, so an artifact at 143 queries and ~316 KB would be expected within ~10–20 %
of the measured 1.46–1.58 s at 131 queries and 299,935 B — i.e. **~1.6–1.9 s at 32 threads**.
That is a projection from the measured band, not a measurement. Note also that only the
*shipped* artifact's verify time matters: intermediate node verify time is prove-side
engineering cost, paid inside `build_agg`, not part of the final verify path.

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
| Node bytes are flat in depth at test targets (2 = 3 = 4, to the byte) | **measured**, `log_blowup=3` only |
| Node bytes are flat in depth at **production** geometry from depth 3 | **projected** from 2 measured points (315,913 / 317,845 → 322,027) + exact comps model |
| Node cost is linear in node count; depth is a fixpoint | **measured** (test targets); production fixpoint at depth 3 by projection |
| Tree is RAM-bound, ~5–6 concurrent nodes on this host | **measured** (18–21.5 GB/node) |
| A production-target aggregation node exists | **YES — measured**: depth 2 `AGG_DEPTH2_OK`, 315,913 B; depth 3 `AGG_DEPTH3_OK`, 322,027 B |
| A production node is ~507.7 s mean (459.4–582.2 s) and ~373 KB | **measured**, 1-child chain levels only |
| Production 2-child node cost | **measured**: 717.0 / 903.5 s (L2), 752.2 s (L3), 18.6–21.5 GB |
| 1 Pgas tree ≈ 46 h serial / 8–9 h at 5–6-way on one host | **extrapolated** from measured 2-child times (508/810/752 s per class); supersedes the earlier "48–96 h / 6 h" band, which used the 1-child 507.7 s anchor |
| 1 Pgas (depth 8) root fits 300 KB | **NO — measured at depth 2 (315,913 B, +15,913 B) and projected at depth 8 (~322 KB, +22 KB)** |
| Depth 8 is legal at production geometry | **projected legal** — `comps` fixpoint 9,911 vs 16,384 ceiling (39.5 % headroom) |
| The 15,913 B depth-2 gap closes by dropping queries to 131 | **NO, not alone** — 143→131 saves ~16 KB but only at `2^20`, and the `2^20` schedule is illegal until the 555-compression (6.8 %) cut lands; that cut is unimplemented |
| Per-proof union soundness at 1 Pgas | **FAILS from S ≈ 103–118 upward** |
| Single-database theorem (`NodeOK`) | **not proved** |
| Leaves are real NEAR segments | **NO — Fibonacci fixtures** (P9/P10/P11) |

The one-line version: **the tree's *legality* problem is solved and neither its *size* nor
its *soundness* problem is; all three are independent, and 1 Pgas is blocked on the last two.**
Depth 2 proving and verifying at 315,913 B removes the geometry wall and leaves a **15,913 B**
size gap that no measured lever currently closes (§2.2, and
`docs/logs/pq-agg-depth2-legal-2026-10-24.md` §5). An earlier version of this sentence said
the size problem was solved; that was written when "root fits 300 KB" was assumed from the
test-target fixpoint and had never been measured. It has now been measured, and it does not fit.
