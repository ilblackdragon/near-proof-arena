# Production-target aggregation: MEASURED at 303,053 B and 276,269 B; depth 2 IMPOSSIBLE

> ## CORRECTION 2026-10-24: "depth 2 IMPOSSIBLE" is WRONG — depth 2 is measured LEGAL
>
> The title and the depth-2 block immediately below are **falsified**. A 2-child production node at
> depth 2 **proves and verifies**: `AGG_DEPTH2_OK leaves=4 final statement = segments [0, 4)`,
> 315,913 B, `prove_s=700.5`, `peak_rss_gb=18.76`. See
> `docs/logs/pq-agg-depth2-legal-2026-10-24.md` and log `agg-d2-geom-ns19lb6.log`.
>
> **What went wrong here:** the "field limit" conclusion tested only two `(n_stack, log_blowup)`
> pairings — `ns18 lb7` (sum 27, ceiling `2^20`, overflow at 21) and `ns20 lb7` (sum 29, illegal at
> `monty_31.rs:654`). It never tested the pairing that keeps the sum at 27 while *lowering* the
> blowup: **`n_stack=19, log_blowup=6`**, whose stacked ceiling is `2^21` — exactly the bit depth 2
> needs — while leaving the WHIR evaluation domain `15·2^27` byte-identical. No circuit change was
> required. The "Raising `n_stack` is illegal" sentence below is true only at `log_blowup=7`.
>
> **Also corrected:** the "36.1 % compression cut" target elsewhere in this directory. Measured L2
> compressions at production hash levers (`d=42, coset_leaf=1`) are **8,747**, not the predicted
> 12,813; the overrun against the 8,192 legal maximum is **555 (6.8 %)**, not 4,621. The prediction
> over-counted `leaf_blocks` (3,048 predicted vs **1,427** measured) and `merkle_nodes` (9,764 vs
> **7,320**) because it assumed `coset_leaf=0`. Depth 2 does not need a circuit change at all; the
> compression cut would only be needed to make depth 2 fit the *cheaper* 126-query schedule.
>
> **Still true below:** the `log_blowup=3` depth law (132,301 B flat) does not transfer to
> production; the 300 KB question at production geometry is still decided by the final layer's
> shape; and no final layer over a depth-2 tree has been measured.
>
> **Production-lever L1 reconciliation (asked for in the handover):** the "~256 KB production-lever
> L1" figure is `L1_0_CACHED proof_bytes=256165` / `L1_1_CACHED proof_bytes=255913` at
> `agg-d2-geom-ns19lb6.log:22,43` — i.e. the two **App-child depth-1 nodes** at production hash
> levers (`d=42, coset_leaf=1`), served from the proof cache (`cached=true prove_s=0.0`). These are
> 11–12 KB *smaller* than the 267,513 B depth-1 figure, which was measured at default hash levers
> (`d=48, coset_leaf=0`). So 267,513 B is a lever-contaminated upper bound for the App-child node,
> and 256,165 B is its production-lever value. The 276,269 / 276,789 B pair remains the *Node-child*
> production figure and is unaffected.

> **DEPTH-2 RESULT 2026-10-23: measured, and NEGATIVE — a field limit, not a resource limit.**
> The two App-child L1 nodes prove at production targets (**276,789 B** and **275,933 B**, both
> ~24 KB under the cap, 1,175 s and 791 s at 8.8–8.9 GB). The L2 **Node-child** node panics:
> `StackedPcs(LayoutHeightExceeded { log_height: 22, log_stacked_height: 20 })`
> (`circuit.rs:458`). The offending column is the **SHA compression AIR** (L2's NvAir is only
> 2^18; its `rows_so_far` was 171,873). `log_stacked_height = l_skip + n_stack ≤ 27 − log_blowup`,
> which at production `log_blowup = 7` is **20**, while two NV children need **22**. Raising
> `n_stack` is illegal (19 → 28, panics at `monty_31.rs:654`), so **a production aggregation node
> with two NV children cannot be proved in this configuration at all.** The base final layer
> verifies only 1 NV child and its SHA AIR sits at exactly 2^20 — the ceiling, with no headroom.
> Consequence: the "bytes flat in depth" result (132,301 B at depths 2–4) is a `log_blowup = 3`
> result and does **not** transfer to production. Log `agg-d2-streaming-qpow32.log`.

# Production-target aggregation: MEASURED at 303,053 B

> **UPDATE 2026-10-23 (query-PoW schedule): the same 2-child node at the base final layer's
> own schedule measures 276,269 B.** With `PARENT_QUERY_POW=32` the WHIR query list becomes
> `[41, 38, 29, 23]` — *identical to `SETUP.json`'s final layer* — and the proof drops to
> **276,269 B**, 23,731 B under the 300 KB cap. Sections:
> `gkr=29960 relations=23332 stacking=2704 whir=220068`; `prove_s=2160.8`, `peak_rss_gb=9.46`,
> `program_rows=16662`, `nvair_h=262144`, `soundness total=268.2`, `AGG_DEPTH1_OK`.
> Log `agg-prod-qpow32.log`. **The 26,784 B saving vs 303,053 B is exactly the 18 fewer queries
> × 1,488 B/query** — i.e. moving 32 bits of soundness from query sampling into query-phase
> PoW is a pure size win at constant total soundness (268.7 → 268.2).
>
> **Read this with its confound attached:** this node is `nvair_h=2^18` with **App** children,
> while the delivered final layer is `2^20`. Its WHIR is 10,808 B *smaller* than the base
> final layer's 230,876 B, and that gap is the height effect (131 queries × 2 extra Merkle
> path digests × 42 B ≈ 11,004 B), not a child-count effect. So 276,269 B does **not** show
> that aggregation is cheaper than the final layer at equal geometry; it shows that a 2^18
> App-child node at the final layer's query schedule is cheaper. The 2^20 Node-child node — the
> actual tree-root shape — is measured by the depth-2 run below.

# Production-target aggregation: MEASURED at 303,053 B

**Status: measured.** A 2-child aggregation node at the production WHIR schedule
(`BITS=268`, `LOG_BLOWUP=7`, `LIST_M=64`, `K=4`, `K1=1`, `LOG_FINAL=7`, all levers on,
`X15=15`, `COMMITS=1`) is **303,053 B** -- only **3,053 B (1.0 %) over** the 300 KB cap, not
the 547,657 B (83 %) that a mis-configured run suggested.

```
L1_0_PARAMS l_skip=2 n_stack=18 k=4 log_blowup=7 queries=[47, 43, 33, 26]
L1_0_O2 target=268 m=64 rounds(n,k,q,first_order)=[(2013265920,1048576,47,true),
              (2013265920,524288,43,true),(2013265920,32768,33,true),(2013265920,2048,26,true)]
L1_0_SUMMARY children=2 cols=173 opened=291 program_rows=16662 nvair_h=262144
              prove_s=1794.6 peak_rss_gb=9.54
L1_0_PROOF_BYTES total=303053 gkr=29960 relations=23332 stacking=2704 whir=246852
AGG_DEPTH1_OK leaves=2 final statement = segments [0, 2)
```

Log `agg-stream2.log`, sha256 `7c42f132…15cdc3`. Run under
`NEARPROOF_STREAM_COMMIT=1` because the default (materialised-LDE) configuration needs
25.94 GB and the session caps at 16 GiB; streaming peaks at **9.54 GB** and costs prove time
(1,794.6 s vs ~66 s materialised).

## What this settles

* **The 300 KB cap is nearly reachable at production targets.** 3,053 B is *not* a structural
  wall -- it is 72 digests' worth (3,053 / 42 = 72.7) on top of a 299,935 B deliverable.
* **The earlier "1.83x over, cap and 268-bit soundness are mutually exclusive" claim was
  wrong**, and wrong for a mundane reason: that run omitted the WHIR levers, so `env_levers`
  defaulted `k_first=0, k=3`, giving 6 rounds / 296 queries instead of 4 rounds / 149.
* **Bytes track query count linearly**, exactly as the four-point table predicted: 149 queries
  -> 246,852 B of WHIR, against 131 queries -> 230,876 B for the base final layer.

## Where the remaining 3,053 B could come from (each needs a run)

| lever | expected saving | basis |
|---|---|---|
| drop `program_part` (1 commit) | **~37,884 B** | measured 2c->1c delta on the chain (35,068 B overhead + 902 digests) |
| 41-byte digests | **~3,000 B** | `D≈2,900` at 1 B/digest, already-proven width |
| `K1=1` already applied | — | this run uses the final-layer `k_first` |

The first row alone would put a 1-commit production agg node near **265,169 B**, comfortably
under. That is a projection from a measured delta, not a measurement.



**Status (final for this session):**
1. The 547,657 B level-1 measurement is real but was **not** taken at the production WHIR
   schedule (296 queries, not 131-149). **The conclusion "one node exceeds 300 KB at production
   targets" is WITHDRAWN.**
2. The run that *would* settle it (production levers, 149 queries) **cannot execute in this
   session**: the harness caps every agent command at 16 GiB and the node needs ~26 GB. See
   "Environment blocker" below.
3. What stands: the byte cost is **linear in WHIR query count** at fixed depth, so a node at the
   production 149-query schedule should land near the base final layer's measured 230,876 B of
   WHIR. That is a projection, clearly labelled, not a measurement.

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
| agg L1 at the production 149-query schedule | **not obtained** | `agg-prod-shape-proper.log` (killed) |

The production-shaped run reports `queries=[47,43,33,26]` = **149 queries**, i.e. within 14 % of
the base final layer's 131. Its byte count is the number that decides whether one agg node fits
under 300 KB, and **it was not obtained**: the process was killed after both leaves proved
(`NV_PHASE end 18558`, `running for over 60 seconds`) with no `SUMMARY` line. Two attempts died
the same way. No OOM is recorded (125 GB total, 117 GB available at the time), so the cause is
the 300 s launcher limit plus session restarts, not memory.

So the decisive number remains unmeasured. What is established is only the *schedule*: with the
production levers set, a 2-child node asks for 149 queries rather than 296, and 149 is close to
the base final layer's 131 -- which is the configuration whose WHIR payload is 230,876 B, i.e.
comfortably inside 300 KB.

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

## Environment blocker, and the workaround that unblocks it

**The cap.** The harness wraps every agent command in a `run-*.scope` with
`MemoryMax = 17,179,869,184` (16 GiB):

```
$ cat /sys/fs/cgroup$(cat /proc/self/cgroup | sed 's/^0:://')/memory.max
17179869184
$ systemctl --user show 'run-*.scope' -p MemoryMax
MemoryMax=17179869184     # every scope
```

An inner `export HEAVY_MEM=32G` cannot lift an outer cgroup limit -- tried, and the scope still
showed `max: 16.0G`.

**Why that blocked the measurement.** A production 2-child node materialising its LDE measured
`peak_rss_gb=25.94`, so it is OOM-killed at 16 GiB every time, silently (the wrapper sets
`oom_score_adj=1000` deliberately).

**The workaround, measured live this session.** `NEARPROOF_STREAM_COMMIT=1`
(`stark-backend-unified/.../prover/stream_pcs.rs:17-60`) commits codewords without ever holding
them, and the stream lane records it as byte-identical:

| config | live peak RSS | outcome |
|---|---|---|
| default (materialised) | **25.94 GB** | OOM-killed at 16 GiB |
| `NEARPROOF_STREAM_COMMIT=1` | **5.7 -> 7.9 GB**, climbing slowly | **runs inside 16 GiB** |

So the blocker was a *default configuration*, not a hard limit. The production-schedule run
(`agg-stream2.log`) is executing under streaming and its byte count is the number this file has
been waiting for.

**Also worth recording:** `target-agg` was reclaimed by the disk-cleanup job a third time
mid-session. Several apparent launches produced no output for that reason alone --
`nohup: failed to run command ...: No such file or directory`. The rebuild takes 34 s; check the
binary exists before launching rather than trusting a previous build.

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
