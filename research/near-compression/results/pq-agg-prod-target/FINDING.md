# Production-target aggregation: depth 1 measured, headline claim WITHDRAWN

**Status: the 547,657 B level-1 measurement is real, but it was NOT taken at the production
WHIR schedule, so it does not support "one node exceeds 300 KB at production targets". The
headline conclusion of the earlier version of this file is withdrawn. What survives is a
weaker, still-useful statement, recorded below.**

## Why the withdrawal

The run set `PARENT_BITS=268`, `LOG_BLOWUP=7`, `LIST_M=64`, `N_STACK=18` -- but **not the WHIR
levers**. `env_levers` (`sha384/e2e_tests.rs:29-48`) defaults every lever to **off**, so the
node was built with `k_first = 0` and `k = 3`, not the production `k_first = 1` / `k = 4`.
That changes the WHIR round count, and therefore the query count and every byte:

| config | `k` | `k_first` | `log_final` | rounds | queries |
|---|---:|---:|---:|---:|---|
| agg run as executed | 3 | 0 | default | **6** | **296** |
| delivered base final layer (`SETUP.json`) | 4 | 1 | 7 | **4** | **131** |

The delivered packet's own `SETUP.json` confirms the production shape: `k=4`, `k_first=1`,
`log_final_poly_len=7`, 4 rounds `[41,38,29,23]`.

**Arithmetic check that the byte gap is fully explained by the query gap:**

* base final layer: `whir = 42 * 2869 + 110,378 = 230,876` (digests 954+794+615+506)
* agg node: `473,336 B`; queries `296/131 = 2.26x`, bytes `473,336/230,876 = 2.05x`

2.26x queries -> 2.05x bytes is **sub-linear**, i.e. entirely consistent with "more rounds and
more queries" and with **no** per-node penalty. There is no production-specific blowup.

So the honest statement is: *a level-1 node at 296 WHIR queries is 547,657 B, and at the
production 131-query schedule it should be near the base final layer's 230,876 B of WHIR.* The
exact number at the production schedule is **not yet measured** -- the re-run is blocked on a
rebuilt test binary (see below) and is the next action.

## What this file still establishes

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

## The comparison that remains valid

| quantity | value | status |
|---|---|---|
| agg L1 at 296 WHIR queries | 547,657 B (whir 473,336) | **measured**, non-production schedule |
| base final layer, production shape | 299,935 B (whir 230,876, 131 queries) | **measured**, `SETUP.json` |
| agg L1 at the production 149-query schedule | *in flight* | `agg-prod-shape-proper.log` |

The production-shaped run reports `queries=[47,43,33,26]` = **149 queries**, i.e. within 14 % of
the base final layer's 131. Its byte count is the number that decides whether one agg node fits
under 300 KB, and it is not yet in hand.

### Confound that must be isolated before quoting the 4.41x

The 10-bit comparison row is `log_blowup=3`; production is `log_blowup=7`. Four extra tree
levels per Merkle path is a real byte cost and is *not* a query-count effect. So "4.41x" mixes
two changes: more queries AND deeper paths. The 236-bit row also used `log_blowup=7`, which is
why it is the fairer comparison point for the WHIR growth:

| pair | what changes | WHIR bytes |
|---|---|---|
| 10 bits lb=3 -> 236 bits lb=7 | queries 126->189 AND depth 3->7 | 48,104 -> 306,024 (6.36x) |
| 236 bits lb=7 -> 268 bits lb=7 | queries only 189->296 | 306,024 -> 473,336 (1.55x) |

The second row is clean: **queries 1.57x, bytes 1.55x — essentially linear in query count at
fixed depth.** So per-query cost is *not* inflated at production targets; the step comes from
`log_blowup` 3 -> 7. An isolating run at `BITS=10, LOG_BLOWUP=7` is in flight
(`agg-isolate-b10-lb7.log`) to split the two effects exactly.

If depth is the driver, the lever is `log_blowup`, which is set by soundness requirements and
may not be free to lower — but it makes the trade-off explicit rather than hidden inside a
single "4.41x".
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

## Correcting my own first analysis: there is NO per-query inflation

My first comparison used the 10-bit node at `log_blowup=3` against production at
`log_blowup=7` and reported "9.84x bytes for 2.35x queries". **That comparison was invalid** --
it mixed two independent changes. The isolating run at `BITS=10, LOG_BLOWUP=7`
(`agg-isolate-b10-lb7.log`) settles it.

Four measured points, all on identical row geometry (`cols=173`, `merkle_nodes=464`):

| BITS | log_blowup | rounds | total queries | WHIR bytes | bytes/query | bytes/round |
|---|---|---|---|---|---|---|
| 10 | 3 | 6 | 24 | 48,104 | 2,004 | 8,017 |
| 10 | 7 | 6 | 14 | 24,296 | 1,735 | 4,049 |
| 236 | 7 | 5 | 189 | 306,024 | 1,619 | 61,205 |
| 268 | 7 | 6 | 296 | 473,336 | 1,599 | 78,889 |

Bytes per query is 2,004 -> 1,735 -> 1,619 -> 1,599 across the four points: flat or declining.
**Cost looks essentially linear in query count**, so the growth from 10 to 268 bits is almost
entirely "more queries", not "more expensive queries".

**Caveat on this table, stated plainly:** the four runs do not vary BITS alone. They also
differ in `k` (3 or 4) and in whether `first_order` rounds are active. Specifically:
`BITS=10 lb=3` and `BITS=268` ran `k=3`; `BITS=10 lb=7` ran `k=3`; `BITS=236` ran `k=4`.
So "flat at fixed depth" is a real observation but **not yet a single-variable result**, and the
236-vs-268 pair I first called "clean" differs in `k` too. A controlled sweep that holds `k`
and `first_order` fixed while varying only BITS is required before quoting a bytes-per-query
law. What *is* solid: all four points sit in the 1,599-2,004 B/query band, i.e. within 25 % of
each other over a 27x range of BITS.

So the size axis is not hiding a per-query inefficiency. The WHIR bytes are ~1,600 B per query
at production depth, which for 296 queries gives 473,336 B. Reducing the tail means reducing
**queries** (higher BITS target is what forces more) or reducing **bytes per query** (path
length ~ log_blowup, and digest size 42 B).

On `log_blowup` 3 -> 7 at `BITS=10`: query count fell 24 -> 14 and bytes 48,104 -> 24,296. That
is the expected direction for a larger alphabet (more blowup => fewer queries for the same
soundness), not an anomaly. I first flagged it as odd by assuming more depth needs more queries;
the WHIR schedule here works the other way, and the four-point table above is the evidence.

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
30211fca806ca3f7ced1562822fcfcf5c64df367736159a54d320ad4f1b1f48b  research/near-compression/results/pq-agg-prod-target/agg-isolate-b10-lb7.log
