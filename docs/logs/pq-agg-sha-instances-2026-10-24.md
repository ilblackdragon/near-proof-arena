# The geometry wall has an implemented-in-design exit: `sha_instances = 2`

Date: 2026-10-24. Session lane `pq-chunk-perf`.

**Bottom line.** The depth-2 `LayoutHeightExceeded { log_height: 21, log_stacked_height: 20 }`
wall is a **per-AIR** height limit (`stark-backend/prover/stacked_pcs.rs:294`,
`if log_ht > log_stacked_height`). The NV circuit currently forces every SHA-384 compression
into **one** AIR (`nv/circuit.rs:149`, `assert_eq!(self.sha_instances, 1, "NV v1 uses one
compression AIR")`), so all `merkle_nodes + leaf_blocks` compressions must fit in `2^20`.
The stack already supports **two** compression AIRs, split by compression index into disjoint
cid ranges, with distinct `cid_offset`s. At two instances the measured depth-2 compression
count splits as **8,192 + remainder**, and both halves land at or below `2^20`.

This does **not** reduce the compression count. It removes the per-AIR height constraint
that currently blocks depth 2. It is unimplemented in the NV path and is therefore a
**projection**, labelled as such below.

## 1. What is measured

From `results/pq-agg-prod-target/agg-d2-geom.log` (first run with the pre-prove geometry
print, production hash levers `d=42`, `coset_leaf=1`):

```
L1_0_GEOM merkle_nodes=240 leaf_blocks=69 comps=309 rows=39552 log_rows=16 \
  a0h=18 a1h=17 a2h=7 a3h=16
```

Four things are confirmed by this single line, all previously model-only:

* `comps = merkle_nodes + leaf_blocks` is the actual AIR input: `240 + 69 = 309`.
* `rows = 128 * comps = 39,552` and the AIR height is `next_power_of_two(rows) = 2^16`,
  matching the printed `log_rows=16`.
* AIR 3 (`a3h=16`) **is** the SHA AIR. AIR 0 (`a0h=18`) is the program AIR, so the earlier
  `nvair_h=262144` figure is AIR 0 and says nothing about the SHA height.
* The measured `coset_leaf=1` leaf term is `69` for these children, versus `257` measured at
  `coset_leaf=0` (`agg-d2-l2prod-ns18.log`). That is a **3.7× drop**, not the "moves only
  slightly" assumption in `pq-agg-sha-compression-accounting-2026-10-24.md` §4.

## 2. The split arithmetic

`CompressSplit::new(n)` (`sha384/jobs.rs:105-111`) gives instance 0 the largest power-of-two
number of rows not exceeding the total, and the remainder to instance 1. Row count is
`128 * comps`; height is `next_power_of_two(128 * comps)`.

Using the measured `merkle_nodes = 7,320` for two production children at `coset_leaf=1`
(`agg-d2-hashprod.log`, cumulative through round 3) and three leaf-term candidates:

| leaf/child | total comps | single AIR | split (inst 0 + inst 1) | both ≤ 2^20? |
|---:|---:|---|---|---|
| 1,122 | 9,565 | 2^21 ✗ | 8,192 (2^20) + 1,373 (2^18) | **yes** |
| 1,589 | 10,499 | 2^21 ✗ | 8,192 (2^20) + 2,307 (2^19) | **yes** |
| 2,245 | 11,811 | 2^21 ✗ | 8,192 (2^20) + 3,619 (2^19) | **yes** |

The single-AIR column is why depth 2 panics today. The split column shows the same
compressions fitting under the ceiling. Even the largest candidate leaves 2^19 headroom on
the second instance.

## 3. Why this is a projection, not a measurement

Three facts make it a real design path rather than a lever flip:

* The field already exists: `NvCircuit.sha_instances` (`nv/circuit.rs:90`), constructed at
  `:121`, and `NvCircuit::new(k, log_rows, sha_instances)` is already called with 1 by the
  aggregation tests.
* The AIR already takes an instance offset: `Sha512Air4.cid_offset`
  (`compress4_air.rs:533`), used at `:655` as `cid = g - r + cid_offset`. The transcript
  module's own AIR list instantiates a second `Sha512Air` with
  `cid_offset: CID_OFFSET_1` (`transcript/mod.rs:110-118`).
* The bus inventory already has the second lookup bus: `ShaBusInventory.lb1`
  (`sha384/airs.rs:41`) and `compress_instance(1)` (`:70-75`) which swaps `lb = lb1`.
* The design intent is stated in the source: `VerifierConfig.sha_instances`
  (`system/mod.rs:73-75`) — *"Number of SHA-512 compression AIR instances (1 or 2). One
  minimises columns ... two halve power-of-two padding."*

What is missing in the NV path:

* `nv/circuit.rs:149` hard-asserts 1.
* `nv/hash.rs:311 generate2` returns a **single** `compress: RowMajorMatrix<F>`, and
  `nv/circuit.rs:268-283` builds `mats = vec![nv, sha.compress, sha.table, byte_table2(..)]`
  — one compression matrix, no split, no `cid_offset` wiring.
* `nv/glue.rs:501 glue_rows` numbers compressions sequentially from `cid_base` with no
  instance split, so cids would need remapping into the two ranges
  (`idx*ROWS` vs `CID_OFFSET_1 + (idx-n0)*ROWS`, as `CompressSplit::cid` does at
  `sha384/jobs.rs:112-118`).

So the work is: thread `sha_instances` through `generate2`/`glue_rows`, emit two compression
matrices via `CompressSplit`, instantiate the second AIR with `cid_offset = CID_OFFSET_1`,
and return both matrices in `mats`. That is a contained change in the NV hashing path — the
same split the transcript module already performs — but it is **not implemented**, and its
cost/soundness are unmeasured.

## 4. What this changes

* The "18.3% SHA-compression cut" is **not** the only structural exit. Splitting the AIR
  costs **zero** compressions and closes the same 1-bit gap. The earlier conclusion that a
  compression *reduction* is required was correct only for a single-instance AIR.
* The geometry wall is therefore an **implementation gap, not an information-theoretic one**:
  the total work fits, the single AIR cannot express it.
* Consequences to verify before trusting the projection:
  1. Does `next_power_of_two(128*8192) = 2^20` exactly, and does the stacked PCS accept an AIR
     at exactly `log_stacked_height` (rather than strictly below)? The panic compares
     `log_ht > log_stacked_height`, so equality is legal — but that needs a measured run.
  2. The second instance costs ~442 opened columns, which grows the proof and the aggregation
     node's own program. Byte impact is unmeasured.
  3. Soundness: the split does not change compressions, so per-proof bits are unchanged.

## 5. Status

Unimplemented and unmeasured. The depth-2 geometry run with production levers is in flight
(`agg-d2-geom.log`) and is expected to panic at `log_height 21`, which would confirm the
single-AIR ceiling is what blocks depth 2. No proof bytes exist for a depth-2 production node.
