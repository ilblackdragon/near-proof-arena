# Production-target aggregation: first measurement (268-bit, z=32, m=64)

**Status: level 1 measured; depth 2 still running. This file records a decisive negative
result on the size axis.**

## Why this run matters

Every tree number in `pq-agg-depth-law/README.md` was measured at **10 query bits**. The
objective's criterion #2 asks for the tail measured "at the segment count needed for the
target workload". Production targets are `BITS=268`, `LOG_BLOWUP=7`, `LIST_M=64`,
`N_STACK=18`. This run is the first production-target aggregation node ever proved.

## Measured: level 1 (a 2-leaf node), production targets

Source: `agg-prod-d2.log`, sha256-pinned below.

```
L1_0_PARAMS l_skip=2 n_stack=18 k=3 log_blowup=7 queries=[77, 60, 49, 42, 36, 32]
L1_0_SUMMARY children=2 cols=173 opened=346 interactions=15139072 cells=31130752
              program_rows=16662 merkle_nodes=464 leaf_blocks=257 chain_starts=2
              nvair_h=262144 prove_s=66.2 peak_rss_gb=25.94
L1_0_PROOF_BYTES total=547657 gkr=44408 relations=26208 stacking=3520 whir=473336
```

`L1_1` is the same geometry: `prove_s=65.7 peak_rss_gb=25.91`, byte-identical size
(`total=547657`), so the node is deterministic in size as at 10 bits.

## The decisive comparison

| | 10 query bits | 268 query bits | ratio |
|---|---|---|---|
| depth-1 node bytes | 124,201 | **547,657** | **4.41x** |
| depth-1 node `whir` bytes | — | 473,336 | 86.4 % of total |
| prove seconds | 12.4–12.9 | 66.2 | ~5.2x |
| peak RSS | 28.13–28.26 GB | 25.94 GB | ~0.92x |

**A single level-1 node at production targets is 547,657 B — already 1.83x the 300 KB cap.**
No aggregation tree of depth >= 1 can meet 300 KB at 268-bit targets, because the *cheapest*
node in the tree already exceeds it. The cap is not a matter of tuning depth or S: the WHIR
payload of one node at production soundness is 473,336 B on its own.

This is measured, not modelled. It should be checked against the extrapolation in
`EXTRAPOLATION-1PGAS.md`, which projected per-node bytes by scaling the 10-bit numbers; the
observed 4.41x is the number to reconcile against that projection.

## What this means for the objective

The 300 KB bound and 268-bit soundness are **mutually exclusive for the aggregation tail as
currently constructed**. The measured facts leave three options:

1. **Reduce WHIR bytes per node.** 473,336 B at 42 B/digest is ~11,270 digest-sized units —
   more than 32 queries x 42 B. Part of that is the WHIR non-digest overhead measured earlier
   at 110,378 B per commit; the remainder, ~8,642 units, still exceeds what 32 queries naively
   suggest. Where those bytes go is the thing to measure next.
2. **Move the tail out of the proof.** Aggregate off-chain / in a STARK whose proof is not
   carried in the 300 KB artifact.
3. **Accept > 300 KB for the aggregation path** and keep the cap only for the D0a packet.

Option 1 is the only one consistent with the stated objective and is now the highest-value
target on the size axis. It is a *measurement* question first: where do 473 KB of WHIR bytes
go for 32 queries?

## The anomaly this exposes (the real finding)

Comparing WHIR bytes per query, 10-bit vs 268-bit, on the same geometry:

| | 10 bits | 268 bits | ratio |
|---|---|---|---|
| WHIR rounds | 4 | 6 | 1.50x |
| queries per round | [41,35,27,23] | [77,60,49,42,36,32] | — |
| total queries | 126 | 296 | **2.35x** |
| WHIR bytes | 48,104 | 473,336 | **9.84x** |
| bytes per query | 382 | 1,599 | **4.19x** |

**WHIR bytes grow 9.84x while query count grows only 2.35x.** Two extra rounds explain part
of it (6/4 = 1.50x), but the remaining 6.6x is per-query inflation: each production query
costs 4.19x more bytes than a 10-bit query.

That inflation is the actionable target. A WHIR query should cost roughly one Merkle path per
round; if 268-bit queries cost 4.19x more bytes each on identical row geometry
(`merkle_nodes=464` in both, `cols=173` in both), the extra bytes are not going into *more*
openings — they are going into *deeper or wider* paths, or into duplicated commitments.

`merkle_nodes` and `cols` and `opened` are identical between the two runs, so the geometry did
not change. The 9.84x is therefore a **transcript/config effect, not a circuit effect** — and
that makes it a candidate for reduction without touching soundness.

## Depth 2: blocked by a layout limit, not measured

Two attempts, both fail before producing a proof:

* `AGG_LOG_ROWS2=20` -> `prog_log = 19` -> `builder.rs:303: program exceeds 2^18 rows`
* `NV_PROG_LOG=22, AGG_LOG_ROWS2=21` -> `circuit.rs:458:
  StackedPcs(LayoutHeightExceeded { log_height: 22, log_stacked_height: 20 })`

So a depth-2 node at production targets needs `log_stacked_height >= 22`, i.e. the stacked
layout budget must be raised too. That is a config change in the PCS, not a test-parameter
change. **Depth 2 at production targets is therefore unmeasured, and honestly reported as
such** — the level-1 measurement is sufficient to establish the 300 KB impossibility, but the
per-depth byte curve at production targets remains open.

## Reproduce

```
NV_PROG_LOG=22 AGG_DEPTH=2 AGG_LOG_ROWS1=18 AGG_LOG_ROWS2=21 \
PARENT_N_STACK=18 PARENT_LOG_BLOWUP=7 PARENT_BITS=268 PARENT_LIST_M=64 \
PARENT2_N_STACK=18 PARENT2_LOG_BLOWUP=7 PARENT2_BITS=268 PARENT2_LIST_M=64 \
PARENT_DKT_CERTS=.../calc/dkt_certs_o2.json PARENT2_DKT_CERTS=.../calc/dkt_certs_o2.json \
target-agg/release/deps/openvm_recursion_circuit-e8a84b4284f8a0d7 \
  agg_chain_depth_n --ignored --nocapture
```
4532512ddf234ed0c990d74af9bb40252a8b97685981c80324950f3068fe093d  research/near-compression/results/pq-agg-prod-target/agg-prod-d2.log
1a7991a6fa5085ce568173b6046d300bfb12822d78dd6467fc3efed221170877  research/near-compression/results/pq-agg-prod-target/agg-prod-d2-r2.log
