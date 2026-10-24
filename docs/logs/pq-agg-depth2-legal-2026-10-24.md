# Depth-2 production aggregation is LEGAL and measured (2026-10-24)

Session: `lane/pq-chunk-perf`. **Reverses the headline of**
`docs/logs/pq-agg-depth2-production-2026-10-24.md` §1/§6.2 and the "36.1 % cut" target of
`docs/logs/pq-agg-sha-compression-accounting-2026-10-24.md`.

**Bottom line.** A 2-child production aggregation node at depth 2 **proves, verifies and
statement-matches**: `AGG_DEPTH2_OK leaves=4 final statement = segments [0, 4)`, in 700.58 s at
18.76 GB peak RSS. The proof is **315,913 B**. The geometry wall that two prior docs declared
structural was an artefact of an unlucky `(n_stack, log_blowup)` pairing, not a field limit: the
`2+19+6 = 27` pairing leaves the WHIR evaluation domain **byte-identical** and raises the stacked
ceiling from `2^20` to `2^21`, which is exactly the bit depth 2 needed.

This does **not** produce a 1 Pgas under-cap artifact, and the reason is now precise: the root
proof *is* the artifact in the aggregation path, and 315,913 B is **15,913 B (5.3 %) over** the
300,000 B cap — see §4 and §5. What it removes is the blocker that said a binary aggregation tree
could not exist at production parameters at all.

## 1. The measurement

Log: `research/near-compression/results/pq-agg-prod-target/agg-d2-geom-ns19lb6.log`.
Launch: `launch-d2-geom-ns19lb6.sh`. Binary
`/var/tmp/pq-prod-target/release/deps/openvm_recursion_circuit-e8a84b4284f8a0d7`,
test `agg_chain_depth_n --ignored --nocapture`.

| quantity | measured |
|---|---|
| outcome | `AGG_DEPTH2_OK leaves=4 final statement = segments [0, 4)` |
| test result | `ok. 1 passed; 0 failed … finished in 700.58s` |
| `L2_0_PROOF_BYTES` | **315,913** = gkr 37,592 + relations 24,772 + stacking 5,920 + whir 247,430 |
| `L2_0_SUMMARY` | `children=2 cols=173 opened=291 interactions=87,097,600 cells=254,084,224 program_rows=232,318 merkle_nodes=7,320 leaf_blocks=1,427 chain_starts=2 nvair_h=1,048,576 prove_s=700.5 peak_rss_gb=18.76` |
| child cost in this run | `L1_0_SUMMARY … cached=true prove_s=0.0` and `L1_1_SUMMARY … cached=true prove_s=0.0` — **both children were cache hits**, so the 700.58 s wall clock is L2's own prove time |
| `L2_0_SOUNDNESS` | `total=268.2 logup=321.9 proximity=283.1 query=268.2` |
| geometry | `L2_0_GEOM merkle_nodes=7320 leaf_blocks=1427 comps=8747 rows=1119616 log_rows=21 a0h=20 a1h=21 a2h=7 a3h=16` |
| WHIR schedule | `queries=[46, 41, 31, 25]` = **143**, 4 rounds, all `first_order=true` |
| `L2_0_PARAMS` | `l_skip=2 n_stack=19 k=4 log_blowup=6` |

`AGG_DEPTH2_OK` means proof-verifies plus statement-matches: `prove_mats` ends in
`engine.verify` (`crates/recursion/src/nv/circuit.rs`). It does **not** mean the VK is pinned
(regenerated in-memory) or that the program is bound on the App-child path — both remain open
(§4).

## 2. Why it works: the bit was bought without moving the domain

The prior doc's invariant is correct but was read too narrowly:

```
l_skip + n_stack + log_blowup <= 27      (BabyBear two-adicity; monty_31.rs:654)
=> log_stacked_height <= 27 - log_blowup
```

At `log_blowup = 7` the stacked ceiling is `2^20`; at `6` it is `2^21`. The point of holding the
sum at exactly 27 is that the WHIR evaluation domain `n = 15·2^27` is unchanged, so this is *not* a
smaller/faster domain — it is the same domain with a taller stacked commitment. Measured domain
per round confirms it: `n = 2,013,265,920` in both configurations.

**Two independent things had to change together, and only one of them is geometry.** An earlier
attempt (`launch-lb6.sh` → `agg-d2-lb6.log`) *did* use this exact `ns19/lb6` pairing and still
failed — at `log_height: 22` against a `2^21` ceiling. So the geometry fix alone is not sufficient.
The second change is the **production hash levers** (`d=42, coset_leaf=1`), which cut L2's
compressions enough to move its SHA AIR from `2^22` down to `2^21`:

| config | hash levers | `l_skip+n_stack+lb` | stacked ceiling | SHA `a1h` | verdict | log |
|---|---|---:|---:|---:|---|---|
| `ns18 lb7` | `d=48, coset_leaf=0` | 27 | `2^20` | 21 | `LayoutHeightExceeded{21,20}` | `agg-d2-hashprod.log` |
| `ns19 lb6` | `d=48, coset_leaf=0` | 27 | `2^21` | **22** | `LayoutHeightExceeded{22,21}` | `agg-d2-lb6.log` |
| **`ns19 lb6`** | **`d=42, coset_leaf=1`** | **27** | **`2^21`** | **21** | **`AGG_DEPTH2_OK`** | `agg-d2-geom-ns19lb6.log` |

The lever effect is visible in the measured child geometry: `agg-d2-lb6.log` reports
`L1_0_SUMMARY … merkle_nodes=464 leaf_blocks=257 nvair_h=524288`, while the passing run reports
`merkle_nodes=240 leaf_blocks=69 nvair_h=262144`. At default levers L1's children are `2^19` and
each query's coset costs `2^k − 1` extra nodes; at production levers the children are `2^18` and
the coset path is gone. That 2× child size propagates into L2's SHA AIR as the extra bit.

So the honest statement is: **depth 2 required both the geometry pairing and production hash
levers.** The prior doc's conclusion was wrong, but so would be the simpler claim that geometry
alone fixed it. **No circuit change was needed** either way.

### 2.1 The cost: 143 queries instead of 126/131

Lowering `log_blowup` at a fixed 236-bit target costs queries. Measured schedules:

| config | queries | total |
|---|---|---:|
| `ns18 lb7`, `k_first=2` | `[41, 35, 27, 23]` | 126 |
| `ns18 lb7`, `k_first=1` | `[41, 38, 29, 23]` | 131 |
| **`ns19 lb6`, `k_first=1`** | **`[46, 41, 31, 25]`** | **143** |

The +17 queries are the main reason the node proof is 315,913 B rather than ~276 KB. Two effects
separate cleanly and both are already measured elsewhere in this directory:

* **queries:** 126 → 143, i.e. +17. At ~1,751 B/query ≈ **29,767 B**.
* **height:** this node is `nvair_h=2^20` with **Node** children, while the 276,269 B figure was
  `nvair_h=2^18` with **App** children. Two extra Merkle path levels at 131 queries × 2 digests ×
  42 B ≈ **11,004 B** (the height effect already isolated in `FINDING.md`).

Sum ≈ 40,771 B against a measured difference of 39,644 B, i.e. the gap is accounted for within
~1.1 KB by these two effects. So the geometry escape is **paid for in size**, not in time: L2's
prove time is 700.5 s, in line with the 695–739 s depth-1 nodes, despite the taller stacked
commitment. Note this is *L2 only* — both L1 children came from cache at `prove_s=0.0`, so the
node's true cold cost is 700.5 s plus two L1 proves.

The size bill is what stands between this legal node and the cap: 143 queries at 2^20 is
inherently ~40 KB larger than 126 queries at 2^18, and only 15,913 B has to be clawed back.

## 3. The compression deficit is 6.8 %, not 36.1 %

The "36.1 %" target in `pq-agg-sha-compression-accounting-2026-10-24.md` came from a *predicted*
`comps = 12,813` for depth 2 with the default hash levers. The measured value at production hash
levers (`d=42, coset_leaf=1`) is **8,747**:

```
comps = merkle_nodes + leaf_blocks = 7,320 + 1,427 = 8,747      (measured, L2_0_GEOM)
rows  = 128 × 8,747 = 1,119,616  ->  2^21                        (measured log_rows=21)
```

Against the `2^20` ceiling of `2^20/128 = 8,192` compressions, the overrun is

```
8,747 − 8,192 = 555 compressions = 6.8 % of the 8,192 ceiling
```

not 4,621 (36.1 %). The prediction's leaf term was 3,048; the measured production-lever leaf term
is **1,427**, and `merkle_nodes` is 7,320 not 9,764. Both differences come from the same lever:
`coset_leaf=1` removes the `2^k − 1` coset path per query. Independent confirmation on L1, where
the same lever is visible in one line: `leaf_blocks=69` at `coset_leaf=1` versus `257` at
`coset_leaf=0` (`L1_0_GEOM` here vs the `coset_leaf=0` runs).

**This matters for the objective.** The circuit change once believed necessary to make depth 2
possible is *not* needed to make it possible — depth 2 already fits at `ns19 lb6`. It would only
be needed to make depth 2 fit at the *cheaper* `ns18 lb7` query schedule. A 6.8 % compression
reduction is a far more tractable target than 36.1 %, but it is now an optimisation, not a gate.

## 4. What this does and does not establish

**Established by measurement:**

1. A 2-child node whose children are **NV proofs** (not App proofs) proves and verifies at
   production hash levers and the production WHIR target — `AGG_DEPTH2_OK`.
2. The depth-2 SHA AIR is `2^21` and the legal stacked ceiling is `2^21`; they coincide exactly.
   There is no headroom: `comps` would have to rise above 8,192 × 2 = 16,384 to need another bit.
3. Depth 2 costs 143 queries, and 700.5 s / 18.76 GB for one node.
4. The prior "depth 2 is not provable at production parameters" claim is **false as written**. It
   was true for the `ns18 lb7` pairing only.

**NOT established — do not quote this as a 1 Pgas result:**

1. **The 315,913 B root proof IS the artifact, and it is over cap by 15,913 B.** In
   `agg_tests.rs:567-570` the tree's single root proof is what gets statement-checked against
   `RangeStmt::compose` of all leaves, and `AGG_DEPTH2_OK` is printed for that root. There is no
   additional final layer in the aggregation path — unlike the base packet, whose 6-level chain
   ends in a separate `FINAL`. So a depth-2 production tree currently ships a **315,913 B** proof,
   **5.3 % over the 300,000 B cap**. Depth 2 being legal is therefore *necessary but not
   sufficient* for the objective. The 15,913 B must come from somewhere (§5).
2. **No depth-2 tree has been wrapped in a separate final layer.** The 299,935 B delivered final
   layer wraps a depth-1 child. Whether adding one over depth 2 helps or hurts is **untested**: it
   adds a commit and its own WHIR, but it drops `program_part` to a single commitment. Net effect
   unknown.
3. **`NodeOK` is still unproved**, and at `S = 146` it is required regardless of proof size (§4 of
   the prior doc). Depth 2 being legal does not touch this.
4. **Leaves are still `SegAir` Fibonacci fixtures**, not `seg-v1`. A 146-leaf production tree needs
   `run_node_single`, which does not exist, so ragged (non-power-of-two) trees remain unproved.
5. **`k_first=1` at 143 queries is 268.2 bits**, same as the other depth-2 settings; no soundness
   was traded for the geometry escape. The union bound still fails from `S ≈ 103–118`.

## 5. Where the 15,913 B must come from

The root proof is 315,913 B against a 300,000 B cap. Three candidate levers, each with its own
status. None is a measurement yet.

### 5.1 Reclaim the cheaper query schedule — this is the only lever that matters

Three schedules are measured at depth 2, and the ordering is unambiguous:

| geometry | `k_first` | queries | stacked ceiling | verdict |
|---|---:|---:|---:|---|
| `ns18 lb7` | 2 | 126 | `2^20` | `LayoutHeightExceeded{21,20}` |
| `ns18 lb7` | 1 | 131 | `2^20` | `LayoutHeightExceeded{21,20}` |
| `ns19 lb6` | 1 | 143 | `2^21` | **`AGG_DEPTH2_OK`** |

Both `2^20` schedules fail **only** because L2's 8,747 compressions exceed 8,192. So the 555-cut
(6.77 %) is precisely what unlocks them, and it buys 12–17 queries:

* **131 queries** → ~16–21 KB saved → **294,901–299,929 B**, i.e. at or just under the cap.
* **126 queries** → ~23–30 KB saved → **286,146–293,269 B**, ~7–14 KB of margin.

The ranges bracket the two *measured* per-query rates in this directory: ~1,332 B/query from the
base-final-layer vs depth-2 comparison (§5.2), and ~1,751 B/query from the prior doc's 126→131
delta. Neither is a depth-2 measurement at the new schedule, so treat the band as a projection.

The 126-query row is better on size and the 131-query row is better on soundness-per-query. Either
way, **the 6.8 % compression cut is the single change that makes depth 2 ship**, and it is now a
much smaller ask than the 36.1 % the earlier accounting demanded. Part of the saving is not purely
additive: removing 555 compressions also shrinks L2's SHA AIR rows below `2^21`, which removes the
height effect on its own Merkle paths. That makes the projection conservative, not optimistic.
**Modelled from measured query deltas; not measured.**

### 5.2 The 1-commit lever is already consumed — and that is why this is close

`PARENT2_COMMITS=1` is already set in the passing run, and `NvCircuit::new` defaults
`program_part: false` (`circuit.rs:137`), so the agg root is already a **single-commitment** proof.
This makes the comparison to the delivered base final layer apples-to-apples, and it is the most
encouraging number in this document:

| proof | queries | NvAir | commits | bytes |
|---|---:|---|---:|---:|
| base final layer (`SETUP.json`) | 131 | `2^20` | 1 | **299,935** |
| depth-2 L2 node | 143 | `2^20` | 1 | **315,913** |

Same height, same commit count, same WHIR params. The 15,978 B difference is **12 queries**, at
~1,332 B/query — and the base final layer already sits 65 B under the cap. So a depth-2 root at
**131 queries and 2^20** would land within noise of the delivered artifact. That is the entire
remaining problem, and it is a 12-query / 555-compression gap, not a structural one.

The 35,068 B 1-commit delta measured on the chain is therefore **not available here**; counting it
would be double-counting. Recorded to prevent that.

### 5.3 Re-balance `k_first` / `log_final` at `lb6` (cheapest untested lever)

`PARENT2_LOG_FINAL=8, PARENT2_K1=1` was chosen because "`lf=7` would add a 5th round". But
`k_first=2` at `lf=6` also gives 4 rounds (`launch-lb6.sh` measured `[48,38,29,23] = 138`, five
fewer than 143) — and it failed only because that run's *children* were at default hash levers.
With production levers the children are smaller, so this needs a re-run to know. The 5-query delta
is worth ~8,755 B — over half the gap. **Untested.**

### 5.4 `X15=1` as a candidate — a tradeoff, not a free win

The `+4` in `nodes/query = nbits + 4` is `ceil_log2(15)`, from `domain_odd_factor = 15`
(`config.rs:513`), and the base packet's own `SETUP.json` has `domain_odd_factor = 15`. If that
term went to 0, L2's Merkle cost would fall from 7,320 to **6,272** compressions — a 1,048 cut,
comfortably more than the 555 needed.

**But `X15` is not a free size lever, and this is the trap to avoid.** The odd factor is bought in
exchange for query count: with `c=15` the per-round rate is `2^-log_blowup / 15`, so fewer queries
are needed for the same bits; with `c=1` the rate is `2^-log_blowup` and **more** queries are
required. The 1,048-compression saving would be partly or wholly given back in additional queries
and their leaf blocks. The net effect on `comps` is **unmeasured**, and dropping the odd factor
also changes the delivered artifact's own WHIR domain, so it is not a drop-in for the shipped base.

Recorded as a candidate only. The 6.8 % cut in §5.1 is the lever with a measured target.

### 5.5 The depth-3 question is separate from the size question

The depth law measured at test targets is flat (`132,301 B` at depths 2/3/4), but those runs used
`log_blowup = 3`, which does not transfer to production. Depth 3 aggregates two NV children exactly
as depth 2 does, so the model predicts a flat SHA cost. Its run (`launch-d3-geom.sh` →
`agg-d3-geom.log`) is in flight; **do not treat depth 3 as legal until it reports.**

Note that depth 3's flatness does **not** fix the size problem. Even if depth 3 fits `2^21`, each
level's root proof still carries ~143 queries, so a depth-8 tree's root would still be ~315 KB.
**The depth law being flat is necessary for a 1 Pgas tree to exist; the size levers in 5.1/5.3 are
what make it ship under cap.** These are independent problems.

**Partial depth-3 evidence is already in** (`agg-d3-geom.log`, still running at time of writing):

```
L2_0_GEOM … comps=8747 … log_rows=21        (identical to the depth-2 run — deterministic)
L2_1_GEOM … comps=8747 … log_rows=21        (the second L2 node, also identical)
L2_0_PROOF_BYTES total=315913               (byte-identical to the depth-2 node)
L2_1_PROOF_BYTES total=317845               (16 B wider: L2_1's own two children differ)
L3_0_GEOM merkle_nodes=7998 leaf_blocks=1913 comps=9911 rows=1268608 log_rows=21
```

**L3's SHA AIR is `log_height 21` against a `2^21` ceiling — depth 3 is legal.** That is the first
evidence that the production depth law is flat. Two independent checks support it:

* `merkle_nodes = 7998` matches the model exactly: `2 × (46·30 + (41+31+25)·27) = 7998`.
* Headroom is real, not marginal: 9,911 against the 16,384-compression ceiling, **39.5 %** spare —
  unlike depth 2's 6.8 % overrun at `2^20`. Every level ≥ 2 uses the same `PARENT{d}` schedule
  (`[46,41,31,25]`), so L4 and above should land near 9,911 and stay legal through depth 8.

`L2_0` being byte-identical to the depth-2 run (**315,913 B** in both) confirms prover determinism
for this node on identical input — which the 520 B spread noted in the earlier depth-1 table did not
have.

**But "flat" is approximate at production geometry, not byte-identical — and this matters for size.**
Within this same run, `L2_0` is 315,913 B while `L2_1` is **317,845 B**, a 1,932 B difference. Both
report `merkle_nodes=7320 leaf_blocks=1427 comps=8747`, so the AIR geometry is identical; what
differs is `program_rows` (232,318 vs 232,702) because the two nodes cover different Fib segments.
The earlier depth-law "byte-identical" claim (132,301 B at depths 2/3/4) came from test targets with
10 query bits. At production geometry **node proofs vary by ~2 KB depending on which leaves they
cover**, so a production root's size carries that uncertainty on top of the depth law.

**`AGG_DEPTH3_OK` itself is not yet printed — do not quote depth 3 as verified until the run
completes.**

## 6. The whole problem in one table

The "depth 2 is impossible" claim and the "depth 2 is too big" concern are **different claims about
different ceilings**, and conflating them caused the earlier error:

| configuration | SHA comps | ceiling | verdict |
|---|---:|---:|---|
| depth 2, `ns18/lb7` | 8,747 | 8,192 (`2^20`) | **FAILS** by 555 (6.8 %) |
| depth 2, `ns19/lb6` | 8,747 | 16,384 (`2^21`) | **LEGAL**, 46.6 % headroom |
| depth 3, `ns19/lb6` | 9,911 | 16,384 (`2^21`) | **LEGAL**, 39.5 % headroom |

Depth 2 was only ever impossible **at `2^20`**. At `2^21` it has *more* headroom than the base final
layer has at its own ceiling. So the depth question is settled and favourable; the remaining problem
is purely that the `2^21` geometry costs 143 queries, which makes the proof ~316 KB.

The size problem and the legality problem therefore pull in opposite directions:

* **Legality wants `2^21`** (`ns19/lb6`) — more stacked height, but 143 queries.
* **Size wants `2^20`** (`ns18/lb7`) — 126–131 queries, but needs comps ≤ 8,192.

**The 6.8 % compression cut reconciles them**, and that is the single remaining engineering change.
If it lands, depth 2 runs at 126 queries in `2^20` and projects under cap (§5.1); if it does not,
depth 2 remains legal but 15,913 B over. Either way the depth law itself is no longer the blocker.

## Reproduce

```
cd research/near-compression/results/pq-agg-prod-target
HEAVY_MEM=48G /data/illia/nearproof-deps/bin/heavy /bin/bash ./launch-d2-geom-ns19lb6.sh
```

Must run under the `heavy` wrapper: a bare `setsid` launch lands in the default 16 GiB scope and
is OOM-killed silently partway through L2 with no panic line. The completed run peaks at 18.76 GB,
so `HEAVY_MEM=48G` is required.
