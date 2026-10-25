# The depth-2 SHA compression budget: exact accounting, and a 2× correction (2026-10-24)

Session: `lane/pq-chunk-perf`. Corrects the compression model in
`docs/HANDOVER.md` §"Depth-2 production measurement" item 5 and in
`docs/logs/pq-agg-depth2-production-2026-10-24.md` §2.

> ## CORRECTION 2026-10-24: the deficit is 555 compressions (6.8 %), and depth 2 is LEGAL
>
> Measured on production hash levers (`d=42, coset_leaf=1`):
> `L2_0_GEOM merkle_nodes=7320 leaf_blocks=1427 comps=8747 rows=1119616 log_rows=21`
> (`agg-d2-geom-ns19lb6.log:71`). Against the 8,192 legal maximum the deficit is
> **555 compressions (6.77 %)**, not 4,621 (36.1 %). And depth 2 **proves and verifies** at that
> geometry — `AGG_DEPTH2_OK leaves=4`, 315,913 B, 700.5 s, 18.76 GB — because `n_stack=19,
> log_blowup=6` raises the stacked ceiling to `2^21` while holding `l_skip+n_stack+log_blowup=27`.
> See `docs/logs/pq-agg-depth2-legal-2026-10-24.md`.
>
> **Both errors in this file's §4 prediction come from the same place: `leaf_blocks`.** §4 assumed
> `coset_leaf=1` "packs the same rows into one longer message, so the block count moves only
> slightly" and kept the leaf term at 3,048. Measured it is **1,427** — a 1,621-block over-count.
> Concretely, the predicted per-child leaf term `41·4 + 35·16 + 27·16 + 23·16 = 1,524` assumes all
> `2^k` coset rows are hashed separately; with `coset_leaf=1` they pack into ~**713** blocks per
> child (**5.44** per query, not 11.63). `merkle_nodes` was also under-predicted, by 352
> (predicted 6,968, measured **7,320**) — so the leaf over-count is partly offset. Net error
> **−1,270 compressions**, which is why the deficit is 6.8 % rather than 36.1 %.
>
> **The "must still be applied" advice in §4 is now done**, and the result is in: with the lever
> applied depth 2 fits. The 6.8 % cut described below as "the honest target" would additionally
> let depth 2 run on the *cheaper* `2^20` schedules (126–131 queries instead of 143), which is
> what brings its proof under the 300 KB cap — a size argument, not a legality argument.

**Bottom line.** The depth-2 deficit is **4,621 compressions (36.1% of 12,813)**, not
1,829 (18.3% of 10,021). The earlier figure added L1's `leaf_blocks` (257) to L2's
`merkle_nodes` (9,764) — but a node's `leaf_blocks` scale with **its own** queried leaves, and
L2 verifies two *production-sized* children, so its leaf term is **3,048**, not 257. Separately,
every depth-2 run to date used the **default hash levers** (`d=48`, `coset_leaf=0`), while the
delivered production chain uses `d=42, coset_leaf=1`; `coset_leaf=1` removes 2,796 compressions
but still leaves the node at 10,017 comps = 2^21, i.e. it does **not** close the gap either.

## 1. The model, validated on 18 measurements

Two counters, both printed by the agg tests:

* `merkle_nodes` — SHA compressions for Merkle path steps, accumulated by `Builder`
  (`nv/builder.rs:767` in `node()`, `:814` in `merkle_path`). One per level per query.
* `leaf_blocks` — SHA blocks for hashing the queried leaves, `Σ_jobs num_blocks()`
  (`nv/agg_tests.rs`, `b.jobs().iter().filter(|j| !j.node).map(|j| j.num_blocks())`).

and the AIR height follows `rows = 128 · (merkle_nodes + leaf_blocks)`
(`compress4_air::ROWS = 128`, `main_height = (n·ROWS).next_power_of_two()`).

**Merkle nodes per query** decompose exactly as

```
nodes/query = (2^k − 1 if coset_leaf == 0 else 0)  +  nbits  +  ceil_log2(domain_odd_factor)
```

where `nbits = log_rs − k` and the odd factor is 15 → `ceil_log2(15) = 4` in the WHIR rounds.

Validated against every level we have measured:

| level | queries/round | `k` | `nbits` | odd term | coset term | nodes/query | total | measured |
|---|---|---|---:|---:|---:|---:|---:|---:|
| L1 (children at small params) | 10/4/2 | 3 | 8/7/6 | 0 | 7 | 15/14/13 | 232 per child | **464 for 2 children — exact** |
| L2 round 0 | 41 | 2 | 25 | 4 | 3 | **32** | 1,312 | **1,312 — exact** |
| L2 round 1 | 35 | 4 | 23 | 4 | 15 | **42** | 1,470 | 1,470 (cum. 2,782) |
| L2 round 2 | 27 | 4 | 23 | 4 | 15 | **42** | 1,134 | 1,134 (cum. 3,916) |
| L2 round 3 | 23 | 4 | 23 | 4 | 15 | **42** | 966 | 966 (cum. 4,882) |

So L2 costs **4,882 merkle nodes per child**, and 9,764 for two — matching the log's cumulative
`merkle_nodes=9764` exactly.

**Leaf blocks** are one per queried leaf row plus one: `Σ_rounds nq · 2^k + 1`, because with
`coset_leaf = 0` each of the `2^k` rows of a query's coset is hashed as its own `TAG_LEAF` message
of `41 + 4·width` bytes, which fits one 128 B block.

* L1: 2 children × (10·8 + 4·8 + 2·8) + 1 = **257** — measured `leaf_blocks=257`, exact.
* L2: 2 children × (41·4 + 35·16 + 27·16 + 23·16) + 1 = 2 × 1,524 + 1 = **3,049**.

## 2. The correction

| quantity | earlier doc | this file | why |
|---|---:|---:|---|
| L2 `merkle_nodes` | 9,764 | 9,764 | agreed (exact) |
| L2 `leaf_blocks` | **257** | **3,048** | 257 is L1's leaf count; L2 verifies 2 production children |
| total comps | **10,021** | **12,813** | |
| rows (`128·comps`) | 1,282,688 | 1,640,064 | |
| AIR height | 2^21 | 2^21 | both round up to the same power |
| ceiling | 8,192 comps (2^20) | same | |
| **deficit** | **1,829 (18.3 %)** | **4,621 (36.1 %)** | |
| per child | 915 (18.3 %) | 2,310 (36.1 %) | |

Both totals round to `2^21`, which is why the wrong decomposition still "matched" the measured
`log_height 21`. The AIR height never distinguished them; only the deficit does.

**The 36.1 % figure is the honest target.** The earlier 18.3 % is arithmetically the *merkle-only*
ratio (`1,829/10,021` where both numerator and denominator omitted L2's leaf term), and acting on
it would have produced a circuit change ~2.5× too small.

## 3. Every depth-2 run used non-production hash levers

`sha_levers()` (`sha384/config.rs:122-133`) reads three process-global env values with these
defaults: `NEARPROOF_DIGEST_BYTES=48`, `NEARPROOF_COSET_LEAF=0`, `NEARPROOF_TSTAR=1`.
The delivered production chain sets them explicitly — `run_cpu_chain.sh` and the stream/g2 launch
scripts all pass `NEARPROOF_DIGEST_BYTES=42 NEARPROOF_COSET_LEAF=1`. **No agg launch script sets
either** (`grep -l 'DIGEST_BYTES\|COSET_LEAF' results/pq-agg-prod-target/*.sh` → no matches), so
every depth-2 measurement ran at `d=48, coset_leaf=0`.

This is visible in the measured node counts, independent of reading any script:

| run | `nbits` in rounds 1–3 | nodes/query | implies |
|---|---:|---:|---|
| delivered chain `L1..L5`, `FINAL` (`chain.log`) | 23 | **27** = 23 + 4 | `coset_leaf = 1` |
| every depth-2 agg log | 23 | **42** = 15 + 23 + 4 | `coset_leaf = 0` |

So the two families are hashing different leaf formats, and their byte counts are not directly
comparable: the agg node's digests are 48 B (`prefix v6-w48-c0`) where production's are 42 B
(`v6-w42-c1`).

## 4. `coset_leaf = 1` is not sufficient either

Turning the lever on removes the `2^k − 1` term: L2 drops from 4,882 to 3,484 merkle nodes per
child, i.e. **−2,796** total. Holding the leaf term at 3,048 (coset hashing packs the same rows into
one longer message, so the block count moves only slightly):

```
9,764 + 3,048 = 12,813   (measured, coset_leaf = 0)
6,968 + 3,048 = 10,017   (coset_leaf = 1)
ceiling       =  8,192
```

`10,017 > 8,192`, so depth 2 is still `2^21`. The lever is worth ~22 % of the budget, not enough on
its own. **It must still be applied before any further depth-2 work**, because otherwise a
"successful" fit would be for a configuration production does not use — but it does not decide the
question.

## 5. What this changes in the plan

* The surviving structural exit is unchanged in kind but **2.5× larger**: remove **4,621**
  compressions per 2-child node (36.1 %), i.e. 2,310 per child.
* The cheapest legitimate component of that is `coset_leaf = 1` (−2,796, free — it is a lever the
  production chain already uses, not a circuit change). That takes the remaining ask to
  **−1,825 compressions (18.2 % of 10,017)** — which, notably, is where the old 18.3 % figure
  lands once you start from the *correct* levers.
* `multiproof` remains measured as not helping `merkle_nodes` (464 in every lever config).
* Digest width remains irrelevant here: every width 40–48 pads a node message to one 128 B block.

## 5a. First measurement on production hash levers (in flight at time of writing)

Launched `results/pq-agg-prod-target/launch-d2-hashprod.sh` — the first depth-2 run ever to set
`NEARPROOF_DIGEST_BYTES=42 NEARPROOF_COSET_LEAF=1` alongside the production WHIR params. It
rebuilt from source into `/var/tmp/pq-prod-target` because the earlier `target-agg` tree had been
reclaimed by disk cleanup (build: **35.5 s** warm sccache, all 12 agg tests present).

**The L1 counters already validate the lever and the model.** On the two small-parameter children
(10/4/2 queries at `nbits` 8/7/6, `k=3`, no odd factor):

| | per child | two children | log |
|---|---:|---:|---|
| `coset_leaf = 0` (all earlier runs) | 232 | **464** | `agg-d2-l2prod*.log`, and 16 more |
| `coset_leaf = 1` (this run) | **120** | **240** | `agg-d2-hashprod.log` |
| model prediction for `coset_leaf=1` | 80+28+12 = **120** | 240 | — |

Predicted and measured agree exactly, so the `(2^k−1)` term is confirmed removable and the
`nodes/query = nbits (+ odd)` form is right. By the same model L2's two production children should
land at **6,968** merkle nodes instead of 9,764.

**What will settle it.** The run is expected to still panic at `log_height 21` (10,017 > 8,192);
if it panics at 20 then this file is wrong and the measurement wins. Either way the panic's
`log_height` plus the measured `merkle_nodes` close the model.

**Status: L1_0 still proving at the time this file was written; the L2 verdict is not in.**

## 6. Reproduce the counters

```
# merkle_nodes per round (cumulative), plus the AIR height panic
grep NV_QCOST results/pq-agg-prod-target/agg-d2-l2prod-ns18.log
# leaf_blocks for a node whose children are small
grep L1_0_SUMMARY results/pq-agg-prod-target/agg-d2-l2prod-ns18.log
# the production chain's 27-nodes/query signature (coset_leaf=1)
grep NV_QCOST runs/opt-baseline-8/chain.log | head -8
```
