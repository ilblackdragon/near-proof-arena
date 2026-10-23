# The aggregation tree's depth law, measured (2026-10-22)

Lane: `lane/pq-chunk-perf`, task `p2-tail`/`t3`. Purpose: the plan
(`docs/logs/pq-1pgas-aggregation-tree-plan-2026-10-20.md` §3 Step 6) asks for an S=13
tree measured with real proofs. This is that measurement, plus the two levels below it,
so the *law* is measured rather than one point extrapolated.

Status: **tree machinery measured to depth 4 (16 leaves) and the exact S=13 flat node
proved: 133,357 B.** The root byte count is flat in depth. The P5 program-binding gate is
live.

## What was measured

All runs: CPU, 32 threads, `cargo test --release` on the rebased overlay in
`/data/illia/nearproof-deps/pq-agg/openvm-sha384`, **test query targets** (10 query bits,
not 268-bit). `PARENT*_N_STACK` set per level; `AGG_LOG_ROWS{1,2,3,4}` = 17/20/20/20.
Logs in `logs/`, hashes below.

### Exact S=13 (the number the plan asked for)

One flat 13-to-1 level-1 node over 13 Fib segments, `AGG_S=13`, `AGG_LOG_ROWS1=19`,
`PARENT_N_STACK=19` (`logs/agg_s13_lr19.log`):

| children | chain starts | proof bytes | program rows | NvAir h | prove s | peak RSS |
|---:|---:|---:|---:|---:|---:|---:|
| 13 | 13 | **133,357** | 104,614 | 2^19 | 75.5 | 12.2 GB |

`AGG_S13_OK`, statement = segments `[0, 13)` verified natively against
`RangeStmt::compose` of all 13 leaf statements. Components:
`gkr=51,848 relations=27,168 stacking=5,104 whir=49,052`.

This is exact, not padded: a flat k-ary node is the same statement as any binary tree over
the same leaves (`arity_split` in the Lean tree development), and it avoids the missing
single-child passthrough. It is the S=13 point, at **test query targets**.

Note the flat node is *cheaper in time* than a binary tree over 16 leaves (75.5 s vs 890 s
total) because it has one trace instead of 15. Its bytes (133,357) are within 0.8 % of the
depth-2 root (132,301).

### Depth sweep (perfect binary trees)

All numbers below are per-node, read from the `*_SUMMARY` lines in `logs/`. The "prove s" and
"peak RSS" columns are ranges **across the individual nodes at that depth in the 16-leaf run**
(`agg_depth4.log`), not across separate runs — so they measure per-node variance, not run
variance. A separate 8-leaf run (`agg_depth3.log`) is reported underneath as a cross-run check.

| depth | leaves | node kind | nodes at this depth (16-leaf run) | proof bytes | program rows | NvAir h | prove s | peak RSS |
|---:|---:|---|---:|---:|---:|---:|---:|---:|
| 1 | 2 | App → N1 | 8 (`L1_0..7`) | **124,201** | 16,598 | 2^17 | 12.4–12.9 | 2.5–3.7 GB |
| 2 | 4 | Node → N2 | 4 (`L2_0..3`) | **132,301** | 89,564 | 2^20 | 105.5–116.3 | 17.5–19.4 GB |
| 3 | 8 | Node → N3 | 2 (`L3_0..1`) | **132,301** | 95,974 | 2^20 | 115.9–117.3 | 18.1–18.2 GB |
| 4 | 16 | Node → N4 (root) | 1 (`L4_0`) | **132,301** | 95,974 | 2^20 | 118.7 | 17.8 GB |

These counts are from the 16-leaf run (`agg_depth4.log`: 8 + 4 + 2 + 1 = 15 nodes = 2^4 − 1).
The separate 8-leaf run (`agg_depth3.log`: labels `N10..N13`, `N20`, `N21`, `N3`) has
4 + 2 + 1 = 7 nodes = 2^3 − 1 and reproduces the same **byte** counts at each depth to the
byte. Its *times* differ run to run: its depth-3 node (`N3`) took **107.4 s / 17.63 GB** against
115.9–117.3 s for the depth-4 run's two depth-3 nodes. So bytes are the law; wall time has
±10 % noise on a shared host.

Every node at a given depth prints byte-identical proof sizes, including the four
sub-fields (`gkr=55,784 relations=27,168 stacking=4,192 whir=44,972` at depths 2–4).
The depth-4 root covers segments `[0, 16)` and its exposed statement equals
`RangeStmt::compose` of all 16 leaf statements (`AGG_DEPTH4_OK`).

### The law

**Bytes are flat in depth from depth 2 onward: 132,301 B at depth 2, 3 and 4, to the byte.**
The jump is depth 1 → 2 (124,201 → 132,301, +6.5 %), i.e. the one-time step from verifying
*a segment proof* to verifying *a recursion proof*. After that the node is a fixpoint:
its child is always the same shape, so the verifier program is the same size, so the trace
buckets are the same, so the proof is the same size.

This is the same fixpoint the delivered chunk chain already shows
(`L2`–`L5` all 137,196 rows, 372–375 KB per level, base run `opt-baseline-8`). The tree and
the chain converge to the same per-node geometry; they differ only in topology.

**Cost is linear in node count, not flat.** A depth-2 node costs ~106 s and ~18 GB where a
depth-1 node costs ~12.6 s and ~3.5 GB. So for a tree over S leaves:

| | nodes | serial prove time (test targets) | peak RSS |
|---|---:|---:|---:|
| binary tree over 16 leaves (depth 4) | 15 | **890.47 s measured** (`finished in 890.47s`); estimate 8×12.6 + 4×108 + 2×117 + 1×119 ≈ 885 s | 19 GB |
| binary tree over 256 leaves (depth 8, S=146) | 255 | 128×12.6 + 127×106 ≈ 4.2 h | 19 GB |
| binary tree over 512 leaves (depth 9, S=291) | 511 | 256×12.6 + 255×106 ≈ 8.4 h | 19 GB |

Those are **test-target** times. At production query targets a node is ~1.5–2 orders of
magnitude more expensive (the model's `[L]` numbers put one real segment child at
624,636 program rows / 2^28.04 cells), so the 1 Pgas tree is a ~weeks-of-serial-CPU
proposition at best, and that is the honest reading of the model, not a measurement.

## The two things this settles

1. **`N2_PROOF_BYTES` is no longer missing.** P4 (a real level-2 node proof) was
   "MISSING — never proved" in the plan (§2, and README "Limits"). It now proves:
   132,301 B / 107.8 s / 16.8 GB, statement verified natively, `AGG_CHAIN_OK` for
   segments `[0, 4)`. The Oct-18 attempt died at a stacked-height error
   (`N2_PARAMS n_stack=17` in `agg-chain-T10.log`, `error: test failed`) and then an OOM;
   with `PARENT2_N_STACK=20` and 125 GB available it passes with 19 GB headroom.

2. **The 300 KB bound does not degrade with depth.** Since every level above the first is
   a fixpoint at 132,301 B, a deeper tree cannot push the root over the cap by itself.
   The root is *smaller* than the per-level NV proofs of the delivered chunk chain
   (~373 KB) because those carry `program_part = true` and the root does not. The size
   risk lives entirely in the **final layer's shape** (query schedule, unwind factor,
   digest width), which is what the 299,967 B D0a packet already sits 33 B under.

## What this does *not* settle

* **Production query targets.** Everything above is 10 query bits. Byte counts are not
  comparable to the 300 KB target at production targets; only the *shape* of the law is.
  The S=13 node is 133,357 B at 10 bits — it says nothing about its size at 268 bits.
* **A real leaf.** The leaves are `SegAir` Fibonacci fixtures, not `seg-v1`. P9/P10/P11
  are untouched. A tree over fixture leaves says nothing about a NEAR chunk's leaves.
* **Any 1 Pgas run.** Per the plan §0, `G_α` (3.451e12 gas) needs no tree at all under
  design G; 1 Pgas is **~146 segments** at 2^23 ops/segment (291 at 2^22) and remains a
  research build. The 1,880–3,760 figure that appeared here was a units error (a
  width-equivalent total divided by a main-cell segment size); see
  `docs/logs/pq-agg-tail-2026-10-22.md` §7 item 5.
* **Ragged / repeated-child trees.** Only perfect binary and flat k-ary shapes were proved.
  The statement layer rejects ragged chains (`Stmt.compose_rejects`), but no *proof* was
  built for a ragged shape, and single-child passthrough does not exist.

## The P5 gate is live (previously recorded as "unstarted")

`agg_node_program_binding` (`PARENT_N_STACK=17`), `logs/agg_bind.log`:

* honest node accepted, `program rows=89000`, `AGG_BIND honest node accepted`;
* BIND region really emitted (Zero rows present, NvAir ≥ 1.5× program rows);
* **positive control**: mutating a child program word in the trace is rejected at the
  constraint layer (`air_builders/debug/mod.rs:75`), `AGG_BIND tampered child program
  rejected`. That is the soundness hole from plan §2 P5, closed in this tree.

The full non-ignored suite is **6/6 green** (`logs/agg_suite.log`, 68.82 s). Note this
contradicts the plan §7.2 record of 4/6 with `unbalanced_messages=14`: the `ChainStart`
row (op 27, `isa.rs:78`, sent in `uair.rs:615–617`, received in `transcript2.rs:540`) is
present here and the bus balances.

## Evidence

```
c18a6bc073b328969de166e63fda8975ab01f9d13e8a33e3fe4871ea765dbe3f  logs/agg_bind.log
a25c5d3b46497880ef166bf42c2bfd5562f95e50b90c1aacbaf27da7898aadf0  logs/agg_chain.log
6833f0dea043aabcceb09c44575ae77f9b6be927592acadf145e7dd1a1facfba  logs/agg_depth3.log
71c73a4febb344662c5963894523eb46f7e92a8e11dc80a739749d6770853476  logs/agg_depth4.log
c7cd075aea84f1e2a3df3b78ef770d126097205274bae0fe8797a9b412675b18  logs/agg_suite.log
37f869c1a90174dc777044e3ca06dd1d772ba4de6030fbbbed95a373862300da  logs/agg_depth3_lr17.log
d32b410ebb706e2acadd5b7eb7b87b8ef7ea310fe41555abf52cf1e9fde9d2f9  logs/agg_s13_lr19.log
e5912b5044398106d36b64a1785f2ebcbefb31d6ab069c629fd18cbe4fba4cb0  logs/agg_s13_lr17_negative.log
```

Two **negative results worth keeping**, both `program exceeds 2^15 rows`
(`builder.rs:303`):

* `logs/agg_depth3_lr17.log` — forcing `AGG_LOG_ROWS=17` on a depth-3 node panics. Depth ≥ 2
  nodes genuinely need the 2^20 bucket; 17 only works at depth 1 (program 16,598 rows).
* `logs/agg_s13_lr17_negative.log` — a flat 13-to-1 node at `AGG_LOG_ROWS1=17` panics even
  though it is a *level-1* node, because 13 children push the program past 2^15. It needs
  `AGG_LOG_ROWS1=19` (program 104,614 rows). So "level 1 is small" holds only for k = 2–4.

## How to reproduce

```sh
cd /data/illia/nearproof-deps/pq-agg/openvm-sha384
export CARGO_TARGET_DIR=/data/illia/nearproof-deps/pq-agg/target-agg

# the three extra probes this lane added to the deps tree (NOT in the overlay patch)
#   agg_chain_depth3          depth 3 over 8 leaves, fixed shape
#   agg_chain_depth_n         AGG_DEPTH=n, perfect binary tree over 2^n leaves
#   agg_s13_flat              AGG_S=n, one flat n-to-1 level-1 node (exact S, no padding)

AGG_S=13 PARENT_N_STACK=19 AGG_LOG_ROWS1=19 PARENT_BITS=10 PARENT_LOG_BLOWUP=3 \
  cargo test --release -p openvm-recursion-circuit --lib -- agg_s13_flat --ignored --nocapture

AGG_DEPTH=4 PARENT_N_STACK=16 PARENT_LOG_BLOWUP=3 AGG_LOG_ROWS1=17 \
  PARENT_BITS=10 PARENT2_BITS=10 PARENT2_N_STACK=20 AGG_LOG_ROWS2=20 \
  PARENT3_BITS=10 PARENT3_N_STACK=20 AGG_LOG_ROWS3=20 \
  PARENT4_BITS=10 PARENT4_N_STACK=20 AGG_LOG_ROWS4=20 \
  cargo test --release -p openvm-recursion-circuit --lib -- agg_chain_depth_n --ignored --nocapture

PARENT_N_STACK=17 \
  cargo test --release -p openvm-recursion-circuit --lib -- agg_node_program_binding --ignored --nocapture
```

The extra tests are edits to the **deps tree only** and are not part of
`patches/openvm-recursion-agg.patch`. Promoting them into the overlay is a separate,
deliberate change.

## What I would do next, in order

1. **Promote the three probes into the overlay patch** and commit them, so the law is
   reproducible from a pristine tree instead of living in a mutated deps checkout.
2. **Production-target node measurement**: one depth-2 node at the pinned 268-bit /
   z=32 / 42 B shape. This is the number that decides whether an aggregation node fits
   under 300 KB at all, and it is the only remaining unmeasured quantity on the size axis.
3. **Single-child passthrough** (`run_node_single`), so S=13 needs no padding and the
   statement indices stay exact.
4. Do **not** invest in larger-S runs before (2): a wider tree cannot change the root's
   byte count, so more S only buys more of the same 132,301 B at a linear time cost.

## Leaf-adapter gap (verified 2026-10-23)

The aggregation code cannot consume a real chunk base proof, and this is a type mismatch
rather than an unfinished feature. Two shapes:

| | `SegAir` fixture (what works) | real chunk base proof |
|---|---|---|
| AIR width | 2 columns (`l`, `r`) | 26 AIRs, widths 263/57/52/60 on the four with pvs |
| public values | one flat slice `[ctx…, j, pre, post]` | per-AIR `Vec<Vec<F>>` (`StatementClaim`) |
| where pvs live | AIR 0 | AIRs 16/21/22/23 (198/202/30/178); **none on AIR 0** |
| consumer | `ChildKind::App` reads `pv[0]`, asserts `len == n_ctx + 1 + 2·n_state` | — |

Evidence:
* `SegFixture::rows` / `of_segment` — `nv/agg.rs:355-362`, `:53-63`
* `ChildKind::App` assertion — `nv/agg.rs:169-172`
* `StatementClaim.public_values: Vec<Vec<F>>` — `nv/circuit.rs:299-304`, filled at
  `pq-state-port/src/chunk_bridge.rs:164-167`
* `BASE.vk.json` / `BASE.proof` in `runs/opt-baseline-8/` as above

**"No adapter exists" is checked, not assumed:** a tree-wide search for `RangeStmt` /
`of_segment` finds them only in `nv/agg.rs` and `nv/agg_tests.rs` (plus the same files in
`pq-agg`). Nothing in `pq-chunk-e2e`, `public-tape-protocol`, or the tracked repo constructs
a `RangeStmt` from a real base proof.

What the adapter would have to do, none of which is implemented:
1. flatten the four pv-bearing AIRs into one `(ctx, segment index, incoming state,
   outgoing state)` tuple;
2. decide which commitment plays the role of the segment's `cached_roots` entry — the base
   proof carries one (`cached_roots` length 1), while the fixture has none;
3. state and prove that the flattened tuple really is the chunk relation's boundary, which
   is the `G_α` coverage obligation, not a plumbing task.

## The leaf adapter is smaller than it first looked (checked 2026-10-23)

The correction above says a real base proof's statement is `Vec<Vec<F>>` (per AIR) while
`RangeStmt` wants one flat slice. That sounds like a merge problem. It is not: every AIR
reads a **prefix of the same public tape**.

* `near-air-v3.json` declares `numPub = 202` and `maxPub = 2^26` — a fixed 202-element
  prefix plus a variable-length tail the `pubSegs` buses range over.
* `pv_of(t, pubs)` (`pq-state-port/src/main.rs:413-417`) returns `pubs[0..t.num_pub]`,
  i.e. a prefix of that one tape, for every AIR.
* The four pv-bearing AIRs are therefore nested prefixes, not disjoint records:

  | AIR | table | `num_pub` | reads |
  |---:|---|---:|---|
  | 16 | `rcpt` | 198 | `tape[0..198]` |
  | 21 | `size` | 202 | `tape[0..202]` |
  | 22 | `qv` | 30 | `tape[0..30]` |
  | 23 | `mrk` | 178 | `tape[0..178]` |

So the adapter reads **one 202-element tape** and projects it — it never has to reconcile
four independent records. That removes the hardest-looking part of the job.

What still has to be decided (and is not decided anywhere in the tree):
1. **Which tape elements are the segment boundary state?** `pubSegs` feeds buses
   0/10/14/28/51/52/56 with widths 34/3/1/7/11/5/5/33/33 starting at tape offset 206 —
   i.e. the boundary/context data plausibly lives in the *variable tail*, not the fixed 202.
   Mapping that onto `(ctx, a, s_a, s_e)` is a spec question, not a code question.
2. **What plays `cached_roots`?** The base proof carries one cached root; the fixture has
   none. Whether a segment's range statement should pin that root is unstated.
3. **The coverage obligation.** Even with (1) and (2), stating that the projected tuple is
   the chunk relation's boundary is the `G_α` coverage theorem, which is separate work.

Item 1 is the real blocker, and it is a *specification* gap: `near-air-v3.json` gives the
tape layout for bus range-checks but nothing in the tree maps tape positions to the
"segment index / incoming state / outgoing state" triple that `RangeStmt` requires.

## A flat 146-to-1 node is infeasible; only the binary tree is (checked 2026-10-23)

`agg_s13_flat` takes `AGG_S` from the environment, so S=146 is directly runnable in
principle — but the measured slope says it cannot run on this host, and the reason is
instructive.

Measured flat-node points (`logs/agg_depth4.log`, `logs/agg_s13_lr19.log`):

| S | program_rows | `nvair_h` | prove | peak RSS |
|---:|---:|---:|---:|---:|
| 2 | 16,598 | 2^17 | 12.8 s | 2.52 GB |
| 13 | 104,614 | 2^19 | 75.5 s | 12.16 GB |

Slope = (104,614 − 16,598) / 11 ≈ **8,001 program rows per added child**. Extrapolating to
S=146 gives ≈ **1,168,807 program rows**, which needs `nvair_h = 2^21`.

The time/RAM projection depends on which measured node is used as the anchor, so both are
given rather than one:

| anchor | cells ratio | projected prove | projected RSS |
|---|---:|---:|---:|
| S=13 flat node (127.2 G cells, 75.5 s, 12.16 GB) | 44.7× | 3,374 s | **543 GB** |
| depth-4 `Node` child (100.6 G cells, 105.5 s, 17.65 GB) | 24.4× | 2,570 s | **430 GB** |

Either way it is **3.4–4.3× this host's 125 GB**, so the conclusion does not depend on the
choice of anchor — but the honest number is the range **430–543 GB**, not a single figure.

The binary tree has none of that problem, but the reason is subtler than "every node has 2
children". A 2-child node's size depends on **what kind** of children it has, and the depth-4
sweep separates the two classes cleanly (`logs/agg_depth4.log`):

| node class | children | `program_rows` | `nvair_h` | prove | peak RSS |
|---|---|---:|---:|---:|---:|
| level 1 (`App` = fixture segment proofs) | 2 | **16,598** | 2^17 | 12.4–12.9 s | 2.5–3.7 GB |
| level ≥ 2 (`Node` = NV child proofs) | 2 | **89,564–95,974** | 2^20 | 105.5–118.7 s | 17.5–19.4 GB |

and both are **flat in depth** (8 level-1 nodes all 16,598; level-2/3/4 nodes all 89,564 or
95,974). So a tree node never grows with the leaf count — it grows with the *child class*,
once, at the first NV-child level. S=146 is therefore reachable as a **255-node tree**
(4.19 h serial at test targets) and not as one flat 146-to-1 node.

The earlier sentence in this section said every node is 16,598 rows at 2^17 — **wrong**: that
is only the level-1 (`App`-child) class. The 2^20 / ~90k-row class is what most of the tree
actually runs.

Consequence for the flat shape's role: `agg_s13_flat` is a device for stating an **exact
segment count without padding** (it avoids the non-existent single-child passthrough), not a
template for the 1 Pgas node. Any "one big k-ary node" design at S=146 is ruled out by
memory, and that should be said before anyone tries it.
