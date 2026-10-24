# Production-target aggregation: depth-2 attempt, the geometry wall, and the size law (2026-10-24)

Session: `lane/pq-chunk-perf`. Supersedes the depth-2 readings in
`docs/logs/pq-agg-tail-2026-10-22.md` rows 18/20/21/22/23 and in
`research/near-compression/results/pq-agg-prod-target/FINDING.md`.

**Scope of this file.** It records the production-target aggregation measurements, the exact
reason depth 2 cannot be proved at production parameters, and the digest-width/size arithmetic.
Everything is measured from a named log unless it is explicitly labelled a projection. Nothing
here is a 1 Pgas size result: all measured nodes are depth 1 (2 children), and every depth-2
attempt at production parameters panicked before producing a proof.

## 0. The correction this file exists to make

The previous headline was **"a full-lever 2-child production node is 267,513 B, 32,487 B under
the cap, the widest production margin"**. That number is real but it was measured with
**`k_first = 2`**, which is the *chain* lever. The delivered final layer — the shape a 1 Pgas
root would take — uses **`k_first = 1`**. Read from the run's own VKs
(`runs/opt-baseline-8/*.vk.json`, `SETUP.json`):

| artifact | `k_first` | WHIR queries | rounds | `n_stack` | `log_blowup` |
|---|---:|---|---:|---:|---:|
| `BASE` | 2 | `[44, 37, 28]` = 109 | 3 | 14 | 7 |
| `L1` … `L5` (chain) | 2 | `[44, 35, 27, 23]` = 129 | 4 | 18 | 7 |
| `FINAL` (delivered artifact) | **1** | **`[41, 38, 29, 23]` = 131** | 4 | 18 | 7 |

So there are two distinct depth-1 measurements, and they must not be quoted interchangeably:

| node lever | queries | 2-child App node bytes | under cap (proof B) | log |
|---|---:|---:|---:|---|
| `k_first = 1` (**final-layer / root shape**) | 131 | **276,269 B** (whir 220,068) | **+23,731** | `agg-prod-qpow32.log` |
| `k_first = 1`, second run | 131 | **276,789 B** (whir 220,540) | +23,211 | `agg-d2-prod.log` |
| `k_first = 2` (chain shape) | 126 | **267,513 B** (whir 211,264) | +32,487 | `agg-d2-l2prod.log`, `agg-d2-l2prod-ns18.log` |

All three sit at the same total soundness, `total=268.2` (`L1_0_SOUNDNESS` in each log), so
`k_first = 1` is not a soundness trade — it is the delivered final layer's own setting. The
8,756 B gap between the 131-query and 126-query rows is the 5 extra queries at ~1,751 B/query
(≈42 digests × 42 B), i.e. the lever, not a geometry change.

Note the **520 B spread between the two 131-query runs** (276,269 vs 276,789). Both print the
same query list, but their `program_rows` differ (16,662 vs 17,558) and so do their WHIR digests —
the same transcript-sampled `D` effect that makes the 300 KB cap non-structural (§3). So the
honest form is a **range: 276,269–276,789 B, i.e. 23.2–23.7 KB under the cap**, not a point value.

**Corrected statement for the objective:** the *root-shaped* 2-child production node measures
**276,269–276,789 B at 268.2 bits**, **23.2–23.7 KB under the cap**. The 32,487 B margin belongs
to a chain-shaped node and must carry that label.

## 1. Depth 1 is measured; depth 2 is not provable at production parameters

Every depth-2 attempt at production targets panicked before producing a proof. The failure is a
**layout height limit**, not memory, not time:

```
StackedPcs(LayoutHeightExceeded { log_height: <h>, log_stacked_height: <s> })
```

with `s = l_skip + n_stack = 2 + 18 = 20` at production, and the offending AIR being the **SHA
compression AIR**. The invariant is the field's 2-adicity:

```
l_skip + n_stack + log_blowup <= 27   (BabyBear two-adicity; panics at monty_31.rs:654)
=> log_stacked_height <= 27 - log_blowup
```

so at production `log_blowup = 7` no AIR may exceed `2^20` rows.

### 1.1 The measured panic table

| `lb` | `n_stack` | stacked height | SHA `log_height` | deficit | queries | outcome | log |
|---:|---:|---:|---:|---:|---:|---|---|
| 7 | 18 | 20 | **21** | **1** | 126 (`k_first=2`) | `circuit.rs:458` | `agg-d2-l2prod-ns18.log` |
| 7 | 18 | 20 | 22 | 2 | 131 (`k_first=1`) | `circuit.rs:458` | `agg-d2-streaming-qpow32.log` |
| 7 | 18 | 20 | 22 | 2 | 296 (`k=3`, X15=1) | `circuit.rs:458` | `agg-prod-d2-r2.log` |
| 7 | 18 | 20 | — | — | 296 (`k=3`, X15=1) | `builder.rs:303` program exceeds 2^18 rows | `agg-prod-d2.log` |
| 6 | 19 | 21 | 22 | 1 | 138 | `circuit.rs:458` | `agg-d2-lb6.log` |
| 5 | 20 | 22 | **23** | **1** | 260 | `circuit.rs:458` | `agg-d2-lb5-wwide.log` |
| 7 | **20** | *illegal* | — | — | 135 | `monty_31.rs:654` (2+20+7 = 29 > 27) | `agg-d2-l2prod.log` |

Two corrections to earlier readings:

* The commonly quoted pair **`log_height (23) > log_stacked_height (22)` is the `lb = 5` row**,
  not production. At production `lb = 7` the deficit is **1 bit** (`21 > 20`) at the 126-query
  schedule, and 2 bits only at the inflated 296-query schedule.
* **`n_stack = 20` is not a layout failure, it is a field failure.** `l_skip + n_stack +
  log_blowup = 2 + 20 + 7 = 29 > 27` trips the two-adicity assert in `monty_31.rs`, so the
  stacked height cannot be raised from the `n_stack` side at production blowup.

### 1.2 Why lowering `log_blowup` does not buy the bit

Buying stacked height with a smaller blowup also costs queries for the same 236-bit target, and
more queries grow the SHA AIR. Measured end to end, the deficit stays at exactly 1:

| `lb` | stacked height | SHA needs | deficit | queries for 236 bits |
|---:|---:|---:|---:|---:|
| 7 | 20 | 21 | 1 | 126 |
| 6 | 21 | 22 | 1 | 138 |
| 5 | 22 | 23 | 1 | 260 |

Only `lb = 3` fits (its stacked height is 24 and the test schedule needs 20), and `lb = 3` **is**
the test-target soundness — i.e. depth 2 fits only where the soundness is insufficient. This is
why the earlier "bytes flat in depth" result (depths 2/3/4 byte-identical at 132,301 B) must be
quoted as a `log_blowup = 3` result and does not transfer to production.

## 2. The exact size of the surviving structural exit: 18.3% of SHA compressions

Because the limit is per-AIR, the only structural escape is to make the 2-child node's SHA AIR
fit in `2^20` rows. The compression model is validated on both known levels:

```
comps  = merkle_nodes + leaf_blocks
rows   = 128 * comps   (ROWS = 128; main_height = (n*ROWS).next_power_of_two())
```

| level | `merkle_nodes` | `leaf_blocks` | comps | rows | rounded | measured SHA AIR | match |
|---|---:|---:|---:|---:|---:|---:|---|
| L1 (2 App children) | 464 | 257 | 721 | 92,288 | 2^17 | `DIAG_TRACE air=1 log_height=17` | **match** |
| L2 (2 NV children) | 9,764 | 257 | 10,021 | 1,282,688 | 2^21 | `log_height 21` / `22` | **match** |

`2^20` rows admits `1,048,576 / 128 = 8,192` compressions, so depth 2 needs

```
10,021 - 8,192 = 1,829 compressions removed = 18.3%
```

and since **both** children shrink, each child must lose **18.3% of its own compressions**
(914.5 of its own ~5,010.5). An earlier revision said "~9.5% per child"; that divided the cut by
two while leaving the denominator at the total, which is a units error.

**`multiproof` does not help.** `merkle_nodes` and `leaf_blocks` are identical (`464`/`257`)
across every lever configuration measured, including runs with the levers off
(`agg-prod-d2.log`, `program_rows=16662`) and on (`agg-d2-l2prod.log`,
`program_rows=17558`). The reduction has to come from the circuit, not from the WHIR query
strategy. **Not implemented.**

## 3. The size law, the cap, and the two width routes

`proof_bytes = 42·D + C` holds on 7/7 delivered proofs. At `D = 2,869`, `C = 179,437`:

```
proof  = 42*2869 + 179437 = 299,935 B
bundle = proof + 32        = 299,967 B      <- RESULT.json bundle_bytes
margin = 300,000 - 299,967 = 33 B = 0.79 digest
```

The cap is on the **bundle**, and it is transcript-sampled, not structural: a second valid proof
(`replay-l4`, which wraps `L4` instead of `L5`) sits at `D = 2,888` → 300,765 B bundle, **765 B
over**. Same configuration, same geometry; only the wrapped child differs.

### 3.1 41-byte digests: measured to fail in the NV tree

The base layer *does* prove at `d = 41`: `BASE_PROOF total=456003` vs 459,984 at 42 B, and
`BASE_VERIFIED bytes=456003` (`d41-chain/prove41.log:29-30`). The **recursion chain then dies**:

```
assertion `left == right` failed
  left: 104
 right: 90
   at crates/recursion/src/nv/hash.rs:262
```

3,568 occurrences across 16 worker threads. The cause is structural, not a one-line flag: `U2`
units are 8 B (`Word`) or 2 B (`Half`), so a digest length must be `8a + 2b`. `48 = 6·8` and
`42 = 5·8 + 2` are representable; **`41 = 5·8 + 1` is not**. `digest_units`
(`nv/hash.rs:236-240`) special-cases only `== 42` and otherwise emits six `Word`s = 48 B, so the
node message becomes `8 + 2·48 = 104` against the asserted `8 + 2·41 = 90`. The separate
`d41-margin` run failed even earlier, with `UnexpectedEof` in the proof codec (`main.rs:70:35`),
so it produced no usable artifact.

### 3.2 40-byte digests: representable, but a projection and no help to depth 2

`d = 40` is 5 words exactly, so it *is* representable in `U2` — but it needs a new `digest_units`
branch, because the current fall-through emits 48 B and trips the same assert.

| estimate | bytes | margin vs 300,000 (bundle) |
|---|---:|---:|
| size law alone, `D` held at 2,869 (`40·2869 + 179437`) | 294,197 B proof | 5,771 B |
| projection including the digest-count drop | ~293,077 B proof | ~6,923 B |

**Both are projections from measured base-layer deltas, not measurements.** And `d = 40` does
**not** rescue depth 2 at all: a node job's message is `8 + 2·d` bytes = 88–104 across widths
40–48, which always pads to **one** 128 B block (`num_blocks = (len+17).div_ceil(128)`), so the
compression count is unchanged. The 12 → 10 change is an **in-circuit unit** reduction (16.7%),
not a compression reduction; the wall needs 18.3% of *compressions*.

## 4. Segment count `S`: two different quantities, both legitimate

* **`S = 146` is the structural segment count.** From `results/pq-base-aggregation/model.out`:
  `1.22e9 ops / 2^23 ops-per-segment = 145.4 → 146` (291 at the older 2^22). The plan's
  `1,880–3,760` is that count mis-divided by the W-eq→main-cell exchange rate
  (`494/38 = 13.0`, `995/38 = 26.2`), i.e. a units error, not a conflicting measurement.
* **`S ≈ 103–118` is the empirical per-proof union-bound failure point** (117.8 z-split, 102.5
  uniform z=32), measured per-proof at `2^-134.88` / `2^-134.68`.

These measure different things: 146 is how many segments the workload needs; 103–118 is how many
proofs one union bound tolerates. Because `146 > 118`, a 1 Pgas tree needs the single-database
`NodeOK` theorem regardless of how small the proof is. `NodeOK` is **unproved** (Lean induction
done, QROM application paper-level, S-19/S-28).

## 5. Logs that must not be cited

Four depth-2 launches on 2026-10-24 produced no byte totals and ran at **5 WHIR rounds**, so they
are neither complete nor production-shaped (`LOG_FINAL` was not set for the `PARENT` prefix, whose
default gives 5 rounds, not the final layer's 4). All four were killed mid-run:

| log | queries | X15 domain `n` | state |
|---|---|---|---|
| `agg-d2-kf1.log` | `[44,35,27,23,19]` | 2013265920 | killed after `L1_0`/`L1_1` tracegen |
| `agg-d2-kf1b.log` | `[44,31,25,21,18]` | 2013265920 | killed, same point |
| `agg-d2-l2few.log` | `[68,48,37,30,25]` | 134217728 (X15=1) | killed, same point |
| `agg-d2-l2n20.log` | `[41,34,28,24,21]` | mixed (halving) | killed, same point |

`agg-d2-materialised.log`, `agg-d2-nodechild-qpow32.log`, `agg-prod-final.log`,
`agg-prod-prop-sched.log` and `agg-prod-shape-proper.log` are likewise params-only captures with
no `SUMMARY`/`PROOF_BYTES`. `agg-d2-prod.log` is a **partial** run: `L1_0` completed at 276,789 B,
`L1_1` did not.

## 6. What this means for the objective

1. **The 300 KB cap is met at depth 1 for the root shape**, at 276,269 B / 268.2 bits — 23,731 B
   of margin, comfortably beyond the 798 B transcript spread. That is a real result.
2. **The tree is not buildable at production parameters in this configuration.** Two NV children
   need one more bit of stacked height than the field can supply at `log_blowup = 7`, and every
   blowup step down costs the bit it buys. This is a domain limit, not a tuning problem.
3. **The only structural exit is a circuit change**: remove 18.3% of the SHA compressions per
   child. `multiproof` and digest narrowing are both measured to be unable to do it.
4. **1 Pgas additionally needs two things this file cannot supply**: real `seg-v1` leaves (the
   tree's leaves are `SegAir` Fibonacci fixtures) and the unproved `NodeOK` theorem.
5. **Merge gate:** keep `lane/pq-agg-rebase` unmerged until a depth-2 target measurement or a
   1 Pgas target measurement exists. No depth-2 or 1 Pgas size result exists today.

## Reproduce

```
# depth-2 at the delivered final layer's own schedule (k_first=1, LOG_FINAL=7, K1=1, COMMITS=1)
results/pq-agg-prod-target/launch-d2-prod.sh

# depth-2 at the chain schedule (k_first=2) — the 267,513 B depth-1 node
results/pq-agg-prod-target/launch-l2prod.sh

# the log_blowup sweep
results/pq-agg-prod-target/launch-lb6.sh
results/pq-agg-prod-target/launch-lb5-correct.sh
```

Binary: `/data/illia/nearproof-deps/pq-agg/target-agg/release/deps/openvm_recursion_circuit-e8a84b4284f8a0d7`,
test `agg_chain_depth_n --ignored --nocapture`. The overlay must be installed with
`research/near-compression/native/recursion/setup_agg_deps.sh`; patch provenance is in
`patches/README-agg-patch.md`.
