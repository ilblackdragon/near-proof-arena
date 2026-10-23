# NEAR Proof Arena — handover (updated 2026-10-21)

This is for the next lead agent. Read it first. The raw working log for 2026-10-07 to 2026-10-09 (≈6,500 lines) now lives in `docs/logs/v3-progress-log-2026-10.md`. Use it only for evidence lookup.

**Rule for this file:** keep it short and current. Append progress to `docs/logs/`, not here.

## 0. Goal and standing user directives

**Goal.** A self-hostable arena where candidates submit NEAR state-transition provers. Each submission comes with a machine-checked Lean certificate. The judge independently builds the submission, checks it formally (fixed trusted root), tests it, and benchmarks it.

**Current target.** A **succinct proof of a NEAR chunk state transition, with a formal proof of correctness.** It must be a drop-in replacement for the stateless validator's `validate_chunk_state_witness`.

**Updated 2026-10-21 (later):** the Wasm join's bus side is **complete**. `wasm_base_exec_host` is
proved and both of its bus premises are now theorems about `Holds` (`host_hst` on 2026-10-20,
`host_hch` + the pair `host_buses` on 2026-10-21). What remains is the per-row instantiation layer
and `Compose`, not a bus fact. Evidence: `results/pq-hch/RESULTS.md`.

User directives (binding):
* **Don't shortcut.**
  * Use explicit, decidable domain conditions rather than hidden assumptions.
  * Prove things where possible; don't settle for testing alone.
  * Never loosen measurement rules to make something pass.
* **Proof size and verify time are first-class.** Proofs must be succinct.
* **One challenge.** `near-chunk-v3` covers the whole chunk transition with coverage tiers D0a < D0 < D1 < D2 < D3α. Do not create one challenge per domain.
* **The strategic value of ZK** is one proof across *all* shards, which standard validator hardware cannot re-execute. Single-proof capacity (`G_α`) is the key metric.
* **Recursion: R5 for today's challenges; reopened for the long-term track** (user 2026-10-14, `docs/zk-formal/V3-D3A-STUDY.md` §D U-1…U-9: recursion allowed; PQ track SHA-384, proven bounds only, real-time PQ end to end, 0.5–1 MB target). Today's signed challenges: no proof composition and no bounded R1. Single-proof capacity is raised through the prover, table and verifier levers listed in `docs/requirements/D3_WASM_REQUIREMENTS.md` §2.4.
* **Decisions already taken by the user:**
  * Price model: N_v = 50 validators **per shard**.
  * B0 = 2.0 MB for D0a.
  * A8 is in RelD0a.
  * A9 and A10 are in RelD0a (2026-10-09): ChaCha words drawn by all scheduler runs ≤ W0 = 770,000, and every used source Merkle path ≤ Dp0 = 32 items.
  * D3 error kinds count as one failure; floats come in a later stage; block facts are derived from headers.
  * 2026-10-11: **A11 `w.post_rebuild`** in RelD0a (no SHA-collision shadow changes the A7 post rebuild);
    **A7's measure** is the unfolded pre trie plus the whole rebuilt post trie (was position-matched
    `diffT`); A7 and A10 are **enforced in the AIR** (A10 by a depth counter in `srcpV3`, A7 by running
    sums checked against B0 in `sizeV3`); the **rcpt repairs** (13-bit deposit age, gated gas surplus) are
    adopted. `nearAirV3` may be revised to make soundness and completeness hold.
* **Security and operations:**
  * Repo: GitHub `ilblackdragon/near-proof-arena`, private.
  * Remote access is through `tailscale serve` only, never funnel. Everything binds to loopback.
  * Keys and secrets live outside the repo. Never print keys, env files or env vars.
  * Never modify signed challenges (`challenges/chl_*.json`), the frozen `oracle/v3`, or any pinned file. `make pin-check` must pass.

## PQ track: state after the 2026-10-20 merge

**Everything below is now on `main`.** All 25 PQ lanes are merged (298 commits from the previous
main tip). `make pin-check` passes, `zk-formal` builds (3,034 jobs), `cargo fmt --check` and
`clippy -D warnings` pass, and the workspace tests pass (`runners/sandbox` needs
`ARENA_DEV_UNSAFE=1`, an environment requirement, not a merge regression).

### What is measured, not modelled

| result | evidence |
|---|---|
| **Recursion tail: FINAL 293,077 B**, V_d accepts, forgery control live | `research/near-compression/results/pq-stream-commit/g2-gate/` (`MANIFEST.json` pins 6 proof hashes + 10 log markers; `reproduce.sh` verifies) |
| Fast CPU prover: 147x, byte-identical; L1 over a real base 152 s / 10 GB (was 190-230 GB estimated) | `results/pq-cpu-prover/README.md` |
| D0a state tables on SWIRL: all 25, no stand-in, tamper 19/19 | `results/pq-state-port/` |
| D1 on PQ: all 30 tables, no stand-in, tamper 23/23 | `results/pq-state-port/` |
| `holdsP_of_swirl` (SWIRL => HoldsP) proved, composed into `extractV3` / `ExtractD1Stmt` | `zk-formal/ZkFormal/PQ/StatePort/{Bridge,D0a,D1}.lean` |
| Wasm join: bus partition proved; interface + coverage statement fixed | `zk-formal/ZkFormal/PQ/StatePort/{Join,JoinFold}.lean`, `JOIN-INTERFACE.md` |
| HOST chip first slice: import calls representable, 77/77 KATs | `results/pq-host-chip/`, `wasm-base-lean/WasmBase/HostChip.lean` |
| Ed25519 costed: 1,514,194 cells / 27,163 interactions per signature | `results/pq-ed25519-air/CENSUS.md` |
| D1 envelope: every hard limit passes; one protocol edit needed | `tools/d1-pq-envelope/` |

### Two corrections that must not be lost

1. **293,077 B is the sound measured FINAL** (binding on at every level). The earlier 287,477 B ran
   with `bind = false` and is not the sound configuration. Margin to 300 KB is **2.3 %**.
2. **The NvAir 2^18 headroom is thin and real.** A paired run failed at `NvAir: 262572 rows exceed
   2^18` (+428 over). Model-vs-measured is ~2.5 %, not the 0.2 % once claimed. Program growth costs
   L 24 -> 25.

### Read next

* `docs/logs/pq-hch-2026-10-21.md` — the CH-bus permutation lane (raw log; summary in
  `results/pq-hch/RESULTS.md`).
* `docs/logs/pq-gap-analysis-2026-10-19.md` — the gap list, kept current by the lanes.
* `docs/logs/pq-final-layer-model-2026-10-17.md` — size/latency model and every measured point.
* `tools/d1-pq-envelope/README.md` — per-table envelope verdict.
* `results/pq-state-port/JOIN-INTERFACE.md` — the Wasm/state contract both sides must obey.

## Gap to e2e 1 Pgas under 300 KB (2026-10-20)

Read `docs/logs/pq-gap-analysis-2026-10-19.md`. Summary:

* **Two goals are conflated.** The signed challenge caps at `G_α` = 2^22·822,756 = 3.451e12 gas
  (2^41.65). 1 Pgas is **289.8x** that and exists only as `Scope.checkD3Peta` (a research
  definition). At 1 Pgas one proof is impossible at any width (W would be 35k-71k; the pin is 24),
  so it needs segmentation. **Segment count RECONCILED and CLOSED 2026-10-23: S = 146 at
  2^23 ops/segment is the correct structural count; the plan's 1,880–3,760 is the same count
  mis-divided and is withdrawn.** The arithmetic, all from the same 1.22e9-adversarial-op
  workload:
  * `results/pq-base-aggregation/model.out` divides by **main** cells:
    `seg_cells = 2^23 · 38 = 2^28.25`, so `S = 1.22e9 / 2^23 = 145.4` → **146**.
  * the plan divides a **width-equivalent** cell total by a **main**-cell segment size:
    `0.6e12 / 2^28.25 = 1,880`, `1.2e12 / 2^28.25 = 3,759`.
  * the bridge is exactly the W-eq→main-cell exchange rate, `494/38 = 13.0` and
    `995/38 = 26.2`: `146 · 13.0 = 1,898`, `146 · 26.2 = 3,823`, which reproduces the plan's
    range. W-eq is a **cost** unit (committed width × height, for prove time), not a row
    count, so it cannot be divided by a main-cell segment.
  * the plan's own neighbouring column validates the main-cell denominator: its single-proof
    width `0.6e12 / 2^24 = 35,763` matches the recorded `W ≈ 35,000–71,000`.
  **Consequence: S ≈ 146 (or ≈291 at the older 2^22 ops/segment), not 1,880–3,760.** This
  changes the labour estimate by ~13–26× but not the soundness verdict — either count exceeds
  the per-proof union bound's failure point of **S ≈ 103–118** (117.8 z-split, 102.5 uniform
  z=32), so the single-database `NodeOK` theorem is needed either way. Full derivation in
  `docs/logs/pq-agg-tail-2026-10-22.md` §7 item 5.
* **The 293,077 B is the recursion tail only.** It does not cover a NEAR chunk.
* **Remaining blockers for a `G_α` chunk:** (a) the HOST chip's gas-invariant generalisation
  (`g := remaining` breaks `R·S + g = g0`; ~112 sites), (b) `HOSTB` byte movement + register
  space, (c) contract-data storage tables (D1 is transfer-only; `ContractData` is D3 work),
  (d) the `runCall` fold / coverage theorem.
  **(e) and (f) are DONE** and were verified in the delivered packet, not just in code:
  the TAPE root reaches V_d and is bound (driver asserts it through every level at
  `main.rs:258-266`, and the chain records `NEGATIVE_CONTROLS_OK changed_tape_root`), and
  `max_interaction_count` is already 2^30 in both `base_params.logup` and
  `final_vk.inner.params.logup` in `runs/opt-baseline-8/SETUP.json`.
* **Ed25519 is decided:** a separate signature proof layer (16-26 days), not in-AIR per chunk.

Realistic: **~2-3 months to a `G_α` chunk under 300 KB**, minus whatever (e)/(f) were carrying.
1 Pgas is a separate project on top.

### Production-target status, margin requirement, `NodeOK` gap (2026-10-23, decision-ready)

Three sentences the reader can act on, each with its evidence and its limit:

1. **Production target: MEASURED and under the cap at the node shape measured.**
   A 2-child agg node at the base final layer's own schedule (`[41,38,29,23]`,
   `QUERY_POW=32`, `COMMITS=1`, 268.2 bits) is **276,269 B**, 23,731 B under 300 KB, proving
   in 2,160.8 s at 9.46 GB peak under streaming. **Limit:** it is an App-child node at
   `nvair_h=2^18`; the 1 Pgas tree's root aggregates Node children at `2^20`, whose program is
   larger. Depth 2 is the run that closes that gap, not this measurement.
2. **Margin requirement: ≥1 KB, and it is NOT met by the delivered packet.** Base sits at
   33 B of margin against an observed 798 B transcript spread. At 42 B digests, with
   `C = 179,437`:
   * **Route A — shrink `C`.** For 1,024 B (1 KiB) of margin: `C` −**991 B** at `D = 2,869`,
     or −**1,789 B** at the worst observed `D = 2,888`. To merely *fit* at `D = 2,888` needs
     −765 B. `C = 179,437` is already a 1-commit final layer and the chain's extra 35,068 B
     comes from a second commit the final layer does not have, so no identified source of
     ~1 KB exists. (A separate reading quotes −1,765 B as "1 KB"; that is 1,000 B decimal,
     which lands exactly at 1,000 B of margin.)
   * **Route B — accept more digests.** `D ≤ 3,095` needs `C` −**9,459 B** (exactly 0 B margin);
     `D ≤ 3,619` needs −**31,467 B**. Both are larger asks than Route A.
   * **Route C — the only identified lever that clears 1 KB is digest width.** At `D = 2,869`,
     41 B digests give **297,066 B (+2,934 B margin)**, 3.5× the observed spread and 89× the
     current margin. That needs `sha_levers()` relaxed (it hard-asserts 48 or 42,
     `sha384/config.rs:131`) plus one final-layer run at `d = 41` to confirm `C` is
     width-invariant. **Neither is done**, so this is arithmetic on the measured law, not a
     result. It is also the cheapest of the three: one ~500 s run.
3. **Depth 2 is arithmetically IMPOSSIBLE at production blowup — a new hard blocker.**
   The 2-NV-child aggregation node needs a 2^22-row SHA compression AIR (measured panic
   `LayoutHeightExceeded { log_height: 22, log_stacked_height: 20 }`, `circuit.rs:458`), but the
   stacked height is `l_skip + n_stack ≤ 27 − log_blowup`, which at production `log_blowup = 7`
   caps at **20**. The field's 2-adicity (27) leaves nothing to raise `n_stack`: 19 gives 28 and
   panics at `monty_31.rs:654`. **So a production aggregation node with two NV children cannot be
   proved in this configuration at all** — not a memory or time limit, a domain limit. Depth 1
   works because its children are App proofs (SHA 2^17); the second NV child takes SHA to 2^22
   (32× growth, recovered exactly from L1's `cells = 2^18·76 + 2^17·83 + 128·9 + 2^16·5`).
   Consequently **the "bytes flat in depth" result (132,301 B at depths 2–4) is a
   `log_blowup = 3` result** (those runs used `n_stack=20, log_blowup=3`, giving stacked height
   22) and **does not transfer to production**. Exits: lower `log_blowup` to ≤5 at the aggregation
   levels (costs query count for the same soundness and breaks the byte comparison to the base
   final layer), or reduce SHA compressions per child. Neither done.
4. **`NodeOK` gap: the soundness of a 1 Pgas tree is an OPEN obligation.** The per-proof union
   bound fails from **S ≈ 103–118** and every 1 Pgas shape exceeds that (S ≈ 146 at 2^23
   ops/segment). The repair is to apply the extraction theorem **once** to the vk family
   (`NodeOK`, DESIGN §9.1), not `n` times — but that theorem is **unproved**: the Lean
   induction is done, the QROM application is paper-level (S-19/S-28).
   `RESULT.json`'s `security_established: false` is a hardcoded literal, not a derived verdict.
   **Until `NodeOK` lands, no byte count makes a 1 Pgas proof sound**, so size work is
   necessary but not sufficient.

## Aggregation tail: what is now measured (2026-10-23)

Full detail, with the scope attached to every number, is in
`docs/logs/pq-agg-tail-2026-10-22.md` and `research/near-compression/results/pq-agg-depth-law/`.

* **The delivered packet is 299,967 B and its tail is a 5-level linear chain, not a tree.**
  `main.rs` folds `L1..L5` one child at a time; the final layer is 299,935 B because it drops
  `program_part` and carries 1 WHIR commit instead of 2.
* **Node bytes are flat in depth** (measured, test targets, Fibonacci leaves): depths 2, 3, 4
  are byte-identical at **132,301 B**; an exact **S=13** flat node is **133,357 B** / 104,614
  program rows / 75.5 s / 12.16 GB. Depth is free in bytes and linear in time.
* **A production-target aggregation node HAS now been proved, but only at 2 WHIR commits and
  only as an upper bound.** At the full production shape (268-bit / z=32 / 42 B / `m=64`,
  all levers on, real DKT certificates) a 2-child node proves at **368,177 B**
  (`L1_0`) and 366,929 B (`L1_1`), 401.2 s and 28.1 GB peak RSS. Caveat: that run's odd-factor
  lever was wrong (`X15=1` instead of 15), so it used 68 queries instead of 44 and the byte
  total is an **upper bound**. Its AIR geometry matches the base final layer exactly
  (`cols = 173`, `nvair_h = 2^20`), so it is the same circuit, differing only in child count
  (2 vs 1) and WHIR commits (2 vs 1).
  **MEASURED 2026-10-23: the 1-commit 2-child production node is 276,269 B**, 23,731 B under
  the 300 KB cap. Schedule `queries=[41, 38, 29, 23]`, `pow(query)=32`, `target=236` (= 268.2
  bits total) — **exactly the delivered base final layer's own schedule** (`SETUP.json`
  `final_vk.inner.params.whir`). Sections `gkr=29960 relations=23332 stacking=2704
  whir=220068`; `prove_s=2160.8`, `peak_rss_gb=9.46`, `program_rows=16662`, `nvair_h=262144`,
  `soundness total=268.2`, `AGG_DEPTH1_OK`. Log
  `results/pq-agg-prod-target/agg-prod-qpow32.log`.
  The 300 KB question is therefore **answered at this node shape: it fits.** Three caveats
  keep it short of a finished result:
  * It is an **App-child** node (`nvair_h=2^18`); a 1 Pgas tree's root aggregates **Node**
    children at `2^20`, which is a bigger program. Depth 2 is the measurement that closes this.
  * It ran under `NEARPROOF_STREAM_COMMIT=1` (9.46 GB peak). The size is streaming-invariant;
    the 2,160.8 s prove time is not — the same node materialised proved in ~66 s at 25.9 GB.
  * The 26,784 B saving vs the earlier 303,053 B run is exactly 18 fewer queries at
    ~1,488 B/query: moving 32 bits from query sampling into query-phase PoW is a **pure size
    win at equal total soundness** (268.7 → 268.2).
  Two earlier projections that disagreed by 7,184 B (302,119 over vs 294,935 under) are now
  **both withdrawn as superseded** — the measurement replaces them. The cold `target-agg`
  rebuild is cheap: **41.3 s** with sccache warm. `/data` has ~77 GB free after cleanup.
  **Correction to the earlier "killed by server restarts, not OOM" claim: they WERE OOM kills.**
  `zkbuild.slice` has `memory.max = 48 GiB`, `memory.peak` reached 40–42.9 GB and
  `memory.events.oom_kill` rose 4 → 5 across two launches; a `mem-watchdog`
  (`/data/illia/nearproof-deps/bin/mem-watchdog`) additionally `kill -9`s the largest process
  in the slice when host `MemAvailable` stays under 10 GiB. Page cache occupies ~16.5 GB of
  the slice, so a ~26 GB materialised run has under 29 GB of headroom and dies mid-WHIR.
  Streaming is the reliable path at 9.46 GB.
* **Leaves are `SegAir` Fibonacci fixtures, not seg-v1 — and the reason is a concrete
  interface mismatch, not just a TODO.** The two shapes are structurally different:
  * `SegAir` is a **2-column** Fibonacci AIR (`l, r`; `SegFixture::rows`, `nv/agg.rs:355-362`)
    whose public values are one flat slice `[ctx…, j, pre, post]`. `ChildKind::App` reads
    `pv[0]` and asserts `len == n_ctx + 1 + 2·n_state` (`agg.rs:169-172`), matching
    `RangeStmt::of_segment` (`agg.rs:53-63`).
  * A real chunk base proof has a **per-AIR** statement: `StatementClaim.public_values` is
    `Vec<Vec<F>>` with one entry per AIR (`nv/circuit.rs:299-304`, filled at
    `state-port/src/chunk_bridge.rs:164-167`). `BASE.vk.json` carries 26 AIRs with public
    values only on **16/21/22/23** (198/202/30/178) and none on AIR 0 —
    `BASE.proof` reports `pv_entries=[0×16, 198, 0,0,0,0, 202, 30, 178, …]`.
  So a real base proof cannot be dropped in as an `App` child without an **adapter that
  flattens four AIRs' public values into one range statement** (ctx, segment index, incoming
  and outgoing state), plus a decision about which commitment plays the role of the segment's
  `cached_roots` entry. That adapter — not the aggregation node — is the missing piece, and
  no such adapter exists in the tree today.

  **And the data that adapter needs is not public (checked 2026-10-23).** Decoding
  `dump/pubs.bin` against `near-air-v3.json`'s `pubSegs` descriptors: the tape is
  self-describing (each descriptor names a `countAt`/`startAt` index, and the decode is
  cross-validated — bus 28 gives `count = 65` and `heights.json` gives `bnd.used_rows = 65`).
  The segment boundary state rides **bus 15** (message length 5), and bus 15 **does not appear
  in `pubSegs` at all** — both its endpoints are *tables* (`rcpt` and `bnd`, each sending and
  receiving), i.e. a row-to-row chain, not a verifier-supplied per-segment value. So exposing a
  segment's `(in, out)` boundary requires either a **new public segment** (which changes the
  vk, every stored proof and the trusted setup — invalidating the 299,967 B packet) or a
  **boundary-commitment statement** (the `G_α` coverage obligation).
  Also: `near-air-v3.json` has no segment concept at all (`format/numBuses/numPub/tables/
  pubSegs/maxPub` only), and one base proof covers the **whole** chunk — 25 tables, 3,391 used
  rows. So there is one proof per chunk, not one per segment; a 1 Pgas chunk needs ~146 segment
  proofs *first*, and only then is there anything to aggregate. Details:
  `research/near-compression/results/pq-agg-depth-law/README.md`.

  The wider `G_α` blockers in §"Gap to e2e 1 Pgas" are what still block the base proof from
  covering a NEAR chunk in the first place.
* **"Under 300 KB" is a transcript-sampled property, not a structural bound.** Measured law:
  `proof_bytes = 42·D + C` (7/7 proofs), so the cap needs `D ≤ 2,869`. The base packet sits
  **exactly at `D = 2,869` — 33 B of margin, 0.79 of one digest** — and a second valid proof
  (`replay-l4`, wrapping `L4` instead of `L5`) is `D = 2,888`, i.e. **765 B over**. Same
  configuration, same geometry: only the wrapped child differs. Margin must be widened by
  ≥1 KB before the bound is treated as a bound.
* **The margin is a digest-width question, and 41 B already clears it on paper.** Because the
  law is linear in the digest byte, at `D = 2,869` / `C = 179,437`: 42 B → 299,935 (+33 B);
  **41 B → 297,066 (+2,934 B)**; 32 B → 271,245; 27 B → 256,900; 26 B → 254,031. The 41 B
  width is **proven now** (CMS19 constants + Thm 4 with K = 0) and needs no new cryptography,
  so a 1-byte reduction buys 3.5× the observed 798 B spread and 89× the current margin. The
  same lever rescues the 2-child agg node at `D = 2,921`: 42 B is 2,119 B over, 41 B is
  971 B under, 32 B is 27,091 B under.
  **Two mechanical blockers before this is a fix:** `sha_levers()`
  (`sha384/config.rs:131`) hard-asserts `digest_bytes == 48 || 42`, so
  `NEARPROOF_DIGEST_BYTES=41` panics today (one-line relaxation, not done); and `C` is
  calibrated only at 42 B, so it needs **one final-layer run at `d = 41`** (~500 s) to confirm
  the non-digest term is width-invariant. Until that run exists this is arithmetic on the
  measured law, not a result.
* **Soundness: the per-proof union bound fails from S ≈ 103–118**, not at S = 295 as previously
  recorded. A 1 Pgas root therefore needs the single-database `NodeOK` theorem, which is
  **unproved** (paper-level, S-19/S-28). `security_established` in the driver is a hardcoded
  `false` literal, not a derived verdict.
* **Prover rebuild is real:** `cargo build --release --offline -j 8` in `chunk-driver` finishes in
  7–14 s incrementally and the rebuilt binary verifies the packet in 2.74 s
  (`INDEPENDENT_VERIFY_OK bundle_bytes=299967 under_300000=true`). It is **not** bit-identical to
  the base run's binary.
* **Verify time is ~1.5 s and is not the bottleneck.** Measured directly on the rebuilt binary:
  **1.46–1.58 s at 32 threads**, 1.78 s at 8, **7.65–7.72 s pinned to one core**; peak RSS
  365 MB → 496 MB as threads rise. Scaling is 4.3× from 1→8 threads but only 1.2× from 8→32, so
  the verifier is latency-bound past ~8 cores. Profile in
  `research/near-compression/results/pq-agg-depth-law/VERIFY-PROFILE.md`. Against a ~522 s final
  prove, verify is ~340× cheaper, so any change trading prove time for verify time is the wrong
  direction.
* **The 5-level chain buys 582 s of prove time for a termination check — and a 4-level variant
  is already measured.** The loop exits on `by_bind` (`main.rs:357`), which fires only when
  `select_anchor` returns an anchor with `M != level-1`. Measured anchors are L2→1, L3→2, L4→3,
  L5→3, so the program had already converged at L4 and **L5 exists only to observe that**. L5 is
  the most expensive level (582.17 s of 2,538.55 s, 23 %).
  `runs/replay-l4` is the 4-level proof, fully measured: `FINAL_PHASE proved_and_verified =
  425.96 s`, `NEGATIVE_CONTROLS_OK changed_tape_root changed_program`, and an independent
  re-verify this session returned `INDEPENDENT_VERIFY_OK bundle_bytes=300765
  under_300000=false`. It is a valid proof that misses the cap by **765 B** at 42 B digests.
  Dropping L5 is **not** a soundness shortcut: the two runs' `SETUP.json` differ only in `level`
  (6 vs 5), `final_vk` and `program` are byte-identical, the anchor `(M, C_M)` is identical, and
  the *verifier* pins the converged program (`verifier.rs:903-921`) independently of how many
  levels were proved.
  **The promising combination is 4 levels + 41 B digests:** −582 s prove time *and* **+2,123 B**
  of margin at once (projected; needs the 41 B run). At 42 B the two objectives conflict — the
  faster chain is over the cap — and the digest width is what removes the conflict.

## Lanes 1-4 landed (2026-10-20, merged + pushed)

All four ran in parallel and are on main (`aba464c0a`):

| lane | what landed | evidence |
|---|---|---|
| `pq-host-gas` | `RelW` gas invariant generalised to `R·(S − S_seg) + g = segb`; recovery lemmas keep the 114 sites one-line; `step_host_ok_seg`/`step_host_abort_seg` proved; `wasm_base_sound`/`wasm_base_exec` re-proved through it | `results/pq-host-gas/`, `Main/Host.lean` |
| `pq-host-bytes` | `HOSTB` bus 210 `[ts, dir, pos, byte]`, table at index 25, 8 degree-2 constraints, byte-table range check; 3 tamper cases rejected; `wasmBaseAir` byte-identical | `results/pq-host-bytes/` |
| `pq-cd-storage` | the `storage_write` **state half**: `cdWalkV3` read + `upsV3` write, `CdBus`/`StateRead`/`StateWrite` + `PQ.CdStorage.Link`; measured 541,608 cells / 43,029 slots (42.9 % / 56.3 % of the D0a baseline) | `results/pq-cd-storage/` |
| `pq-nv-tape` | cached TAPE root folded into the statement and reaching V_d (node-fold, because 18 more limbs would push the message past one SHA block); per-AIR height cap in vk/NV/V_d; `max_interaction_count` production default 2^30 (gate scripts pin 2^28 so the recorded G2 proofs stay valid) | `results/pq-nv-tape/README.md` |

Verification: `zk-formal` builds (3,044 jobs); `pin-check`; `cargo fmt --check`; `clippy -D warnings`;
KAT **77/77**; the G2 gate's 6 proof hashes still verify.

**Two process traps found (worth remembering):**
1. A stale `wasmbase-tool` binary made 4 KATs fail after the merge (`HOSTB` missing from `airH`).
   The Lean source was correct; the binary was old. Always rebuild the tool after a Lean change that
   adds a table.
2. `lane/pq-cd-storage` appeared to be a no-op merge because its commit was already an ancestor of
   the merge base through shared history — verify content (`git merge-base --is-ancestor <sha> HEAD`
   and check the files), not just whether HEAD moved.

**Finished after lanes 1-4** (2026-10-20, on main):

* **`pq-host-gas`: the HOST CH-channel soundness bug is fixed.** `Host.constraints` had no
  `act`–`pf`/`nres` link, so an *inactive* HOST row still emitted count-1 CH receives and broke the
  base `ChipFacts.inactive` premise. Added `(1−act)·pf j = 0` and `(1−act)·nres = 0`. (The first
  attempt wrote the constraint backwards and KAT caught it: active rows would have required
  `pf = 1`. Verified: lake build 123 jobs, KAT 77/77.)
* **`pq-host-bytes`: HOSTB groups now carry their call and prove `pos < len`.** New columns
  `len`/`hid`/`gap`; `len` and `hid` constant within a group; `pos + gap + 1 = len` with `gap`
  `RANGE16`-checked, which proves `pos < len` for `len < 2^16` (a stated domain condition). The wire
  message is `[ts, hid, dir, pos, byte]`, so a group cannot be spliced onto a different host call.
  Tamper **65/65 rejected** on `hostarg`, including the new `len+1`/`hid+1`/`gap+1`.
* **`pq-cd-storage`: `UpsertPreservesWfWithBounds` is now a THEOREM, not a stated `Prop`.** The
  full `PTrie.upsert_wf` induction was proved (mutual `Kids.upsert_wf` too), plus
  `upsert_memD_le`. **The originally proposed `splitExt_wf` statement was FALSE** — `splitExt`
  rebuilds a usage from the stored `m`, so `m < 2^64` is insufficient; it needs the headroom
  `m < memHead` that the induction actually supplies. Proved with that hypothesis and shipped a
  machine-checked counterexample (`not_splitExt_wf_64`). Axioms on all of it:
  `[propext, Classical.choice, Quot.sound]`.
* **`pq-nv-tape`: `maxLog` is wired** from each ported table into `max_log_trace_height`, so the cap
  reaches the vk, the native proof shape, the NV generator and V_d.

**Still genuinely open after lanes 1-4:**

* `wasm_base_sound_host` is not a finished theorem. The gas/boundary layer, the HOST `RowSpec` and
  the host-AIR bus decomposition are all done; what remains is the `Exec` **segmented induction**
  for `wasmBaseHostAir` (`HostChipFacts` + threading `S_seg`/`segb`). `Main/Host.lean` and
  `results/pq-host-gas/RESULTS.md` §3.3 state it exactly.
* `HOSTB` still does not model the `(ptr, len)` range into linear memory, nor the register space
  (space 6). `len < 2^16` is a domain condition.
* CD storage: `RealStoreMatchesTables` remains stated (it needs the D3 render + overlay replay,
  engineering E1/E3, not a new AIR fact). `memOk`/`memLe` preservation across an upsert is not
  proved; `memLe` is only a hypothesis.
* NV: the `maxLog` wiring is built but **not validated end to end** — `run_demo.sh` panics earlier
  in the classical trace dump (`statedump: srcp: classical constraint failure`), which reproduces
  with the change stashed. Also the `pq-state-port` deps tree predates the
  `max_log_trace_height` trait method, so it needs a `setup.sh` refresh.

## Host-function coverage: the four lanes are merged (2026-10-21)

All four host-coverage lanes are on main (`f77f748d7`), pushed, `pin-check` + `lake build` (3,050
jobs) + `cargo fmt` green, KAT **88/88** (main was 79 before the merges).

| lane | what landed |
|---|---|
| `pq-host-promise` | HOST chip widened `np ≤ 2` -> `np ≤ 9` (HOSTQ 8 -> 22 fields, inside the NV 128-field envelope), 23 promise entries, `wasm_base_exec_host`, `HostChipBits` re-derived on the new layout; 2 latent Rust bugs fixed (arg order vs spec `popArgs`, producer time) |
| `pq-host-ctx` | 19 context/state-read hosts; **no AIR needed** — arity/type agreement with `hostSigs` is a kernel check (`hostFns_arity_agrees`, `hostFns_types`) |
| `pq-host-logreg` | log/panic + register/return, the space-6 `RegisterSpace`, the `REG` chip, and `HOSTB`'s `reg` column (a register fill byte is a response byte) |
| `pq-host-storage2` | `storage_read`/`has_key`/`remove`/`usage` **proved**; `storage_iter_*` **proved out of domain** |

**The structural finding.** The HOST chip is *generic*: it never names a function. Coverage is
therefore a `hostFns` entry plus a state-side response plus a KAT — not a chip per function. That is
why 44 of the 64 D3α functions cost almost nothing. The exceptions:

* **hash (`sha256`, `keccak256/512`, `ripemd160`)** — need arithmetic AIRs that do not exist on the PQ
  stack at all. The classical stack has a SHA-256 table; nothing on PQ does.
* **promise / receipt (23 functions)** — need a receipt-construction AIR that does not exist
  (`D2/Actions.d2Hooks.functionCall` errors out). Priced in `results/pq-host-promise/DESIGN.md` at
  ~7-12 lane-weeks, the borsh `ActionR` encoder being the dominant cost.

**Merge lessons (this took far longer than it should have):**
1. Three lanes chose three different host-id schemes. Only ids `0..7` are pinned (they are what a
   cached `HOSTT` contains); nothing indexes a host id numerically, so one canonical table resolves
   them. `tools/host-fns/canonical.txt` is it (64 D3α entries).
2. `origin/main` was **broken** for a period: `pq-host-promise` branched before `HostChipBits`
   existed, so merging it broke a file no lane had compiled against, and the follow-up commit's
   "build 128 jobs" claim was false. Verify a build yourself; do not trust a commit message.
3. Editing another agent's proof file under merge pressure produced real corruption (twice I
   truncated a 331-line file to 76 lines). Delegate that with the exact goal printed via
   `trace_state` rather than guessing the proof state.
4. Rebuild `wasmbase-tool` and the Rust crate after any Lean table change; a stale binary produced
   four false KAT failures.

**Still open in this lane:**
* `HOSTB` does not model the `(ptr,len)` range into linear memory, nor the register group walk
  (`Register.RegLenAgree`), nor the `HOSTB`<->`HOSTQ` container relay (`CdKeynibFromHostB`).
* `gas` remains out of domain (its parameter is `i32`, the row's argument slots are `i64`).
* The hash and receipt families above.

## The segmented induction and `wasm_base_exec_host` (2026-10-21)

**What this closed.** `wasm_base_sound_host`'s last missing proof was the `Exec` segmented
induction: `exec_of_rows` threads *one* gas segment, but a host call resynchronises the budget
(`g := remaining`), so every instruction after it lives in a different segment. That is now done.

| theorem | file | meaning |
|---|---|---|
| `exec_of_rows_seg` | `WasmBase/Main/SegHarness.lean` | `exec_of_rows` re-run with the segment threaded per row (`seg : Nat → Nat × Nat`, indexed by STATE time so it survives the `act`/`rs` permutation) |
| `wasm_base_exec_host` | same | `exec_of_rows_seg` instantiated for `wasmBaseHostAir`; conclusion reports the **last** segment |
| `host_rel_restart` | `WasmBase/Main/HostRel.lean` | lifts `step_host_ok_seg` to a full 20-field `RelW` at `(S+fee, g_after)` |
| `host_hst` | `WasmBase/Main/HostBus.lean` | the STATE-bus `Perm` premise, discharged from `Holds` |
| `occ_bits_host` | `WasmBase/Main/HostChipBits.lean` | every STATE/CH occurrence has count ≤ 1 |
| `RowSpecSeg` / `RowFactsSegMap` | `WasmBase/Main/SegHarness.lean` | the row spec whose successor segment is a parameter |

### Three findings that must not be lost

1. **The per-row gas condition is not derivable.** `exec_of_rows` gets each row's
   `R·(S+fee−S_seg) ≤ segb` from *monotonicity of one budget*. After a host restart that is false:
   the next row needs `R·fee ≤ g_after`, a real machine fact. Hence `hstepgas` is a hypothesis.
2. **`HOSTO.mult` is unconstrained and harmless.** `HostO.table.constraints = []` and both its
   interactions count `mult`, so nothing forces `mult ≤ 1`. It does **not** block anything: the
   induction needs "counts are bits" only on buses STATE(0)/CH(2), and `HOSTO`/`HOSTT`/`HOSTB` touch
   neither (`hosto_avoids_state_ch`, `hosttab_avoids_state_ch`, `hostb_avoids_state_ch`). `mult > 1`
   is the oracle's call count and is correct. **Do not "fix" it by constraining the AIR.**
3. **`hostActRows` was silently selecting nothing.** It filtered with `rowAct (chipT 22)`, but
   `chipT 22 = default`, not `Host.table`. Every HOST row was dropped from `actListHost`, which would
   have made `wasm_base_exec_host` *vacuously true* over host traces. Fixed to filter with
   `rowAct Host.table`. If you write another active-row helper for a non-`chipT` table, check this.

### Still open for the join (was "four items", one and a half done)

| item | state |
|---|---|
| `hst` (STATE-bus `Perm`) | **proved** (`host_hst`) |
| `hch` (CH-bus `Perm`) | **proved** (`Main/HostBus.host_hch`, plus `host_buses` = `hst ∧ hch`). Two gaps the "~30 lines" estimate missed: `HostTraceOK` had no derivation from `Holds` (`host_row_inactive_counts` gives the raw `pf j`/`nres` counts, `host_trace_ok` packages them), and `msgs_ch` interleaves the HOST block *differently* on the two sides (memory block after the instruction rows on the true side, drain block between them on the false side), so a bare `flatMap` congruence does not suffice — `perm_ch_host` needs one `perm_mid` association swap per side. `List.flatMap_map`'s shape was the wrong tool. |
| `HOSTB` `(ptr,len)` -> memory | **open** (lane 6 below) |
| `RealStoreMatchesTables` / `UpsV3AppliesLog` | **open, and not a proof task.** `upsert` is hard-coded at `[0,15]` as a *constraint polynomial* (`Tables/Ups.lean` `symE`, `Extract/Ups/QNodes` `UpsSpec.key`), so a ContractData path is a different polynomial, not a different instance. This needs a **table parameterisation (a render change)**, or the statement drops it. `UpsertPreservesWf` was already shown **false as stated** and corrected to `UpsertPreservesWfWithBounds` (headroom `m < memHead`), which is proved. |

### Process lessons (paid for in this session)

* **Never trust a build claim you did not make from a clean checkout.** `git archive <commit> | tar x`
  into `/tmp`, build there, then quote the number. A stale `.olean` under an actively-merged tree
  produced a false "128 jobs, KAT 77/77" for a commit that did not build at all.
* **Work in a worktree, not the main checkout.** The main checkout was switched to another agent's
  branch mid-session and a merge landed in it (`MERGE_HEAD` + `UU` conflicts) while I was editing.
* **Verify content, not HEAD movement** (already lesson 4 below; it bit again).

## Hash and receipt families: both lanes landed (2026-10-21)

Two parallel lanes on top of `origin/main` @ `f51c8563c`, merged and pushed as `57bbd3478`.
Verified independently on a clean worktree: `lake build` 219 (wasm-base) + 3,057 (zk-formal) jobs,
KAT **97/97** (was 88), `make pin-check`, no `sorry`/`native_decide`/`implemented_by`.

### `pq-hash-air` — a SHA-256 AIR on the PQ stack

**What it is.** `WasmBase/ShaAir.lean` (454 lines): a 44-column, 17-rows-per-block SHA-256 AIR,
degree 4, 5 interactions/row, 9,333 cells per block. Plus `ShaSound.lean` (the soundness leg) and
`ShaVectors.lean`. Exported as `wasmbase-tool airX`; `wasmBaseAir` stays byte-identical.

**Measured.** Real proof of a 100-byte-input SHA program: 1,637,754 B, 43.7 s prove, 0.054 s verify,
268.4-bit soundness. Differential test against `sha2` on **16/16 vectors** (empty, 1, 3, 55, 56, 63,
64, 65, 100, 119, 120, 127, 128, 129, 200, 1000 bytes) — AIR cells equal the reference on message
bytes and digest. Tamper 11/11 rejected. KAT contributed 9 new hash programs (88 -> 97).

**Per-function verdict.**

| function | cells/call | feasible on PQ? |
|---|---:|---|
| `sha256` | 9,333 · blocks | **built** |
| `ripemd160` | ≈9-11k · blocks | yes, ~2-3 weeks |
| `keccak256` / `keccak512` | ≈118,582 cells/permutation (bit-sliced) | **feasible at degree 3**; the chi step is built and proved (see below). **The earlier "needs a 64-bit-multiply gadget" claim was wrong** |

Envelope: 27 AIRs total (≤32), degree 4 (≤8), widest message 12 fields incl. bus (≤128). The
classical `ZkFormal.Sha.Table` was the reference; porting it beat a from-scratch narrow AIR.

**Finding worth noting:** before the declaration bus (212) was added, a `Dmult = 0` trace was
*accepted* — the digest declaration was not bound. That is recorded in the lane README; the fix is
in the merged tree.

### `pq-receipt-air` — the promise/receipt bookkeeping AIR, and a corrected price

**What it is.** `zk-formal/ZkFormal/PQ/Receipt/{Table,Ids,Rows,Statement,Wire,Cost,Bookkeeping}.lean`:
`PBC`, one row per `promise_*` call in `ts` order — **49 columns, 51 constraints (degree ≤ 4), 29
interactions, maxLog 16**, `Air.wf` clean at maxDeg 8. The 13 class fields live in a cached `PBK`
table consumed on bus 211 (the `HOSTT`/`CODE`/`TAPE` pattern), so static columns are pinned by a bus
receive rather than witnessed. Wire reuses `HOSTQ`/`HOSTR`/`HOSTB` (+2 interactions, no second wire).

**Proved** (axioms ⊆ std3): the class transcription is checked against a **second independently
written** list via `decide` (`promiseClasses_*`); the row/chain lemmas (`rcpt_row`, `prm_row`,
`rcpt_chain`, `tgt_lt` i.e. `tgt < rcpt`, `dep_le` i.e. `dep ≤ 128`); and the counter obligation
`Statement.prevR_counter_is_count` — **the receipt counter is `#{k<n | addR k = 1}`**, a count of
`PBK` bits, not a guessed integer.

**Stated-not-proved** (named `Prop`s): `HostCallTrace`, `TgtIsReceipt`, `ActionBytesAreHostBytes`,
`ActionEncodingIsBorsh`.

**The price correction — this changes the plan.** DESIGN.md called the borsh `ActionR` encoder the
dominant cost (4-6 weeks). Measured at the D3α limits (4,194,722-byte maximum receipt): the encoder
is 268 M cells and the SHA over those bytes is 606 M — **the hash is 69 %, the encoder 31 %**. The
encoder is separable from the SHA/`RIDS` work, so the sequence becomes SHA/`RIDS` first and the
encoder optional. Total ≈6-10 lane-weeks (was 7-12).

**Two flags for the join:**
1. `two_max_receipts_over_cap`: two 4 MiB-argument receipts exceed a 2^21 SHA table — the per-byte
   path does not compose past a couple of maximum receipts. This is a real capacity constraint.
2. ~~`PQ/Join/Statement.lean`'s `HOSTQ`/`HOSTB` are still the stale 8- and 4-field shapes.~~
   **FIXED 2026-10-21 (lane `pq-actionr`)**: migrated to the HOST chip's wire (`HOSTQ` 22 fields,
   `HOSTR` 8 with `ar` in field 6, `HOSTB` 5 with `hid`). `Receipt/Ids.lean`'s
   `hostQ_no_bridge`/`hostB_no_bridge` are unchanged in content and now compare the *old* shapes
   (`Join.hostQOld`/`hostBOld`) against the current wire, so the gap stays proved.

### Keccak and ActionR (2026-10-21, merged `fa00bcd5e`)

**Keccak: the recorded blocker was wrong, and chi is proved.** Keccak-f has **no multiplication** —
theta is a 5-way XOR plus `rotl(C,1)`, rho is `rotl`, pi is a lane permutation, chi is `a ^ (~b & c)`,
iota is a XOR with a round constant. The base layer already has both needed primitives at i64: the
**BIT** chip (i64 and/or/xor) and the **SHIFT** chip (`P = A·2^e mod 2^(2w)`, `rotl`/`rotr`), both
KAT-tested. Both are byte-sliced, so the "three sub-multiplies ⇒ degree ≥ 9" premise had no subject.

`WasmBase/ChiAir.lean`: a 48-column `CHI` table with **zero row constraints** and 24 BYTE lookups,
using the identity `(~b) & c = c ^ (c & b)` — no NOT column, no range gadget, no 64-bit arithmetic.
`chi_sound` proves `val8 r = val8 a ^^^ ((2^64−1−val8 b) &&& val8 c)`; `and_not` proves the lane
identity; `ChiVectors.lean` has **16 differential vectors** (all-zero, all-ones, alternating phases,
single bits, byte stamps, random, spec round constants) closed by kernel `decide`, plus `chi_diff`.
Axioms: `{propext, Classical.choice, Quot.sound}`.

Cost (`results/pq-keccak-air/model.py`): round row 4,826 cols / 9,689 constraints / degree 3 /
0 interactions; **118,582 cells per permutation**; 872 / 1,647 cells per input byte for
keccak256 / keccak512 — i.e. 6.0× / 11.3× SHA-256. More expensive, but **buildable at degree 3** and
well inside the NV envelope. Remaining: the 24-round permutation AIR itself (composition in
`results/pq-keccak-air/README.md` §3), and wiring `CHI.table` into an `Air` value.

**ActionR: the join wire is fixed, and the encoder is built for four action kinds.**
`PQ/Join/Statement.lean` was migrated to the real chip wire — `HOSTQ` **22** fields (was 8),
`HOSTB` **5** (was 4), `HOSTR` field 6 now the signature's `ar`; `wasmBusMax` corrected 6 → 9. The
old shapes survive as `hostQOld`/`hostBOld` so the gap stays a theorem (`hostQ_old_not_current`,
`hostB_old_not_current`), and `Receipt/Ids.lean`'s `hostQ_no_bridge`/`hostB_no_bridge` still hold
unchanged. `hostQ22`/`hostB5` are proved *equal* to the join's definitions by `rfl`, so the two
spellings cannot fork again.

`PQ/Receipt/Encoder.lean`: reference encodings checked against the spec's own decoder `D2.pBaseAct`
(`decodesAs`) by kernel `decide` on real vectors, with a discriminating negative case. Rows
(`encAction`) proved equal to those bytes for **transfer, delete-account, create-account and
function-call**; `PBE` is 15 cols / 23 constraints (deg ≤ 3) / 4 interactions / maxLog 22. Framing
proved: `encAction_length`, `prefixBytes_value`, the per-shape lengths (`receipt_tr_len` 82/114 for
ed25519/secp, `receipt_da_len`), and row-side `pbe_len_framing_general`,
**`pbe_group_len_is_row_count`** (declared `len` = row count), `pbe_msg_len`/`pbe_buses` (bytes on
the existing `HOSTB` 210, no second wire).

Remaining: the `FC`/`promise_create` row instances (`FC` is 3/4 done — two string prefixes need a
per-field index in the `PBE` group key; `promise_create`'s nested `Vec<Action>` needs `tail` as a sum
of action lengths), then `RIDS`/`SRC`/`RCL` + `newReceipts`, `HostCallTrace`, and
`ActionBytesAreHostBytes`. Price unchanged: the encoder is 31 %, the SHA 69 %.

### Still open

* `ripemd160` AIR (≈2-3 weeks, same shape as SHA-256).
* `RIDS`/`SRC`/`RCL` + `newReceipts` fold, and the `HostCallTrace`
  induction (Wasm side).
* The `ActionR` encoder AIR (lane `pq-actionr` started it: `PQ/Receipt/Encoder.lean`).

## Parallel lanes to run next

Lanes 1-4 are done (see above). The remaining critical path is the **tightening** of what landed,
then the join. Lanes 5-7 and 9-10 are independent; 8 depends on 5 and 7.

| # | lane | scope | blocks | est. |
|---|---|---|---|---|
| 5 | ~~`lane/pq-host-rowfacts`~~ **DONE 2026-10-21** | `exec_of_rows_seg`, `wasm_base_exec_host`, `host_rel_restart`, `host_hst`, `occ_bits_host` all proved (see the section above). `hch` followed in ~~`lane/pq-hch`~~ **DONE 2026-10-21** (`host_hch`, `host_buses`). The bus side is closed. | — | done |
| 6 | `lane/pq-host-memio` | `HOSTB` -> memory: the `(ptr,len)` range, `pos < len`, and the register space (space 6), plus the link from a `HOSTB` group to its `HOSTQ` call. The bus and table exist; this gives them meaning. | any real byte-moving host call | 5-7 d |
| 7 | `lane/pq-cd-props` (**not a pure proof lane** — see the note) | `WalkKeyIsContractData` has been **proved for the HOSTB route** (`PQ/Join/CdWalkView.lean`, residual `CdKeynibFromHostB`); `UpsertPreservesWf` was **false as stated** and its corrected form `UpsertPreservesWfWithBounds` is **proved**. Remaining: `RealStoreMatchesTables` (render + overlay replay, engineering E1/E3) and `UpsV3AppliesLog`, which needs a **table parameterisation** because `upsert` is hard-coded at `[0,15]` as a constraint polynomial. | the state half being a theorem, not a check | 6-10 d, and the `upsert` rework is the long pole |
| 8 | `lane/pq-runCall-fold` | The coverage theorem: `join_additive` + `d3Hooks`/`runCall` correspondence, so a joined proof implies the D3 chunk relation. Shape stated in `JoinFold.JoinStmt`. | the end-to-end claim | 10-15 d |
| 9 | `lane/pq-sig-layer` | The separate Ed25519 proof layer: ZK-friendly curve arithmetic + a SHA-512 witness over the preimage, proving `Ed25519.verify` at 128 bits. Census done (`results/pq-ed25519-air/CENSUS.md`). | signed transactions | 16-26 d |
| 10 | `lane/pq-1pgas-scale` | Research only: measure one 2^28.25-cell segment at real settings, then extrapolate the aggregation tree. No 1 Pgas claim. | goal B | research |

**Suggested first batch:** 6 and 7 in parallel. 8 (the runCall fold) can start now:
`wasm_base_exec_host` exists and its `hst`/`hch` are discharged from `Holds`, so the instantiation
layer is the only thing between it and a `Holds`-only statement. 9 is independent and long; 10 is
independent and cheap.

**7 is not a proof lane.** Read the `UpsV3AppliesLog` note above before dispatching it: `upsert` at a
ContractData key needs a table parameterisation, which is a render/AIR change with a size/model cost.

### Merge discipline that worked (learned twice now)

1. Merge the **frontier** lane (the one containing the others' commits), not every lane.
2. Shared log files conflict **additively**: keep both sections.
3. A file main already has a newer version of: keep main's.
4. Verify **content**, not HEAD movement: a lane can be a no-op merge because its commit is already
   an ancestor through shared history. Check `git merge-base --is-ancestor <lane> HEAD` **and** the
   files.
5. **Rebuild before believing a test failure.** A stale `wasmbase-tool` made 4 KATs fail; the Lean
   source was fine. After any Lean change that adds a table, rebuild the tool and the Rust crate.
6. Always run `pin-check`, the `zk-formal` build, `cargo fmt --check`, `clippy -D warnings`, the KAT
   suite and the G2 manifest check before promoting to main.

## 0a. State at stop (2026-10-15) — HISTORICAL, superseded by the sections above

* **Signed + live (local operator key; registered on the live arena):**
  `chl_56077279…` `near-chunk-validation-d0-stark` (D0a) and `chl_497bbbf1…` `near-chunk-v3`
  (tiers D0a 0 / D0 1 / D1a 2 / D1 3 / D2 4 / D3a 5). Live release `13d2e653` (Firecracker FORMAL_CHECK
  batched 64 runs/VM; `docs/logs/judge-fc-batch-2026-10.md`).
* **D0a live run** `run_335e1cda…` (`np-udr-stark-v2`): **REJECTED 2026-10-15 08:19** on
  CONFORMANCE_DIFFERENTIAL only (all formal gates, ADVERSARIAL, PROVER_RELIABILITY 86/86 and
  RESOURCE_LIMITS PASS; max proof 5.69 MB, verify 4.0 s, 13.4 GiB). Counterexample: rejection case
  `00-h10024-s3-w.applied_receipts_hash` — the request is byte-identical to the honest `00-h10024-s3`
  (only the witness's applied-receipts hash is mutated), so the claim is TRUE and the certificate is not
  contradicted; but the judge requires `prove` to refuse a supplied witness the reference rejects, and
  `prove_v3` doesn't check that field. **Fix (candidate side):** `prove_v3` must validate the supplied
  witness completely (all checks of `checkD0a`, incl. applied_receipts_hash) and exit 2 otherwise; run the
  full arena-public-d0a rejection set locally (all 128) before resubmitting. Evidence:
  `/data/illia/nearproof-deps/validation/d0a-live-run-20261015/`. Resubmit with the improved prover.
* **Prover:** D0a 263–312 s / ≤ 12.6 GiB on 8 vCPU (`docs/logs/v3-prover-perf-2026-10.md`).
* **D1a** (native Ed25519, interim): phase 1 done (first D1a proof Lean-accepted). R-5 option (B) (user):
  `nearAirV3D1` = 33 tables (walk every tx key: `walkU`, `nmemV3`, `uvalV3`, `nodeD1`, `uniqD1`; `ridV3`
  `l` range check); conformance 257 fixtures, AIR A7 = `unfoldBytesD1` incl. the R-5 counterexample.
  Phase 2: views, receipt/Merkle copies (generator `zk-formal/scripts/rcpt_d1_copy.py`), links 65/113
  copies + walk copies; F1 proved (`factorSoundD1_B0 : FactorSoundD1 B0`, `D1/F1/`, 2026-10-21);
  NOT yet: `A7D1Step`, `LinkD1CoreStmt`, R1/R2/A1. Next steps:
  `docs/logs/v3-d1-a7b-2026-10.md`, `docs/logs/v3-d1-phase2-2026-10.md`, plan `docs/zk-formal/V3-D1-PHASE2.md`.
  Untested: no fixture exercises a stub / `nmemV3` query yet; real D1a proof on the 33-table AIR not re-run.
* **D3a / 1 Pgas / PQ:** study `docs/zk-formal/V3-D3A-STUDY.md`; performance design + CPU spikes
  `docs/zk-formal/V3-PERF-DESIGN.md` (worst-case 1 Pgas ≈ 1.75–1.9 s after execution on 32 H200 if GPU
  ≥ ~30 % of peak; decisions P-PERF-1…7, no code cap). PQ research: `research/hash-recursion/`,
  `docs/research/recursive-compression.md` (also untracked copies in the main checkout by another agent —
  a `git pull` there will refuse until they're removed).
* **Open user decisions:** live guest-image upgrade for build/conformance/benchmark (SANDBOX_VIOLATION
  detection missing there); H200 access; P-PERF-8 (early code-prep sub-proofs), final-layer rate,
  research milestones M2/M3 next; when to resubmit D0a with the improved prover.

## 1. Host rules (the host OOM-crashed twice; follow these strictly)

* **Run heavy builds through the wrapper:** `HEAVY_MEM=16G taskset -c 8-15,24-31 /data/illia/nearproof-deps/bin/heavy <cmd>`.
  * The wrapper is a systemd scope in `zkbuild.slice` with a 48G cap, and `mem-watchdog` runs alongside.
  * Use `HEAVY_MEM=32G` only for the D2 kernel-eval proofs.
  * At most about 3 lanes, and at most 2 heavy builds per lane at a time.
* **CPUs 0-7 and 16-23 are reserved for the live benchmark worker w1.**
  * Stop w1 only in short, logged windows with an empty queue (`docs/LIVE.md` §5f).
  * If a run is interrupted, restart w1.
* **Disk:** `/` is at **98%** (20 GB free) and `/data` at **90%** (2026-10-11).
  * Delete merged worktrees and their `target/` dirs.
  * Session scratchpads under `/tmp/claude-1002/...` are large (`lean`, `npai-e2e`, `elan` ≈ 25 GB) and can go once you have confirmed nothing needs them.
* **Merging:**
  * Use explicit `git add <paths>` only; other agents work in worktrees. Check `git status` before committing.
  * Merge lanes to main **before** installing live.
  * Run `cargo fmt --check`, clippy with `-D warnings`, the affected tests and `make pin-check` before pushing.
  * Commit trailer: `Co-Authored-By: Claude Opus 5.5 (1M context) <noreply@anthropic.com>`.
* **Worktrees:** lanes live in `/data/illia/nearproof-wt/<lane>`, one per concurrent agent. Never share a worktree between agents.
* **Helper:** `/data/illia/nearproof-deps/bin/resolve-members.py` resolves `Cargo.toml` member conflicts.


## 2. Repository state

* **2026-10-20: the whole PQ track merged into main** (298 commits, 25 lanes). D0a/D1 state tables on
  the PQ base layer, the measured G2 recursion tail (293,077 B), the HOST chip first slice, the
  Ed25519 census, the D1 envelope tool and the join statement are all on main. Merge checks:
  `make pin-check` OK; `zk-formal` builds (3,034 jobs); `cargo fmt --check` and
  `clippy --workspace --all-targets -D warnings` OK; workspace tests pass with
  `ARENA_DEV_UNSAFE=1` (`runners/sandbox` requires it; without it 22 bwrap tests fail on an env
  assertion, independent of this merge).
* **What the merge resolved:** three lanes disagreed on the HOST bus ids (7/8/9 vs 200/201/202 vs
  208/209/210). `200/201/202` was **unsound**: the state port shifts classical buses by 128 and the
  D1 export uses buses up to 75, so the occupied range is 128-203 and 200-202 landed on classical
  buses 72-74. Final allocation is **HOSTQ 208 / HOSTR 209 / HOSTB 210**, `HOSTT` 9 (Wasm-internal).
  See `results/pq-d3-join/BUS-NUMBERING.md`.

* **2026-10-14:** `lane/v3-size-opt` merged to main (`584d55ff`): compact hint codec spec-first
  (`NearSpecV3.HintCompact` + `ZkFormal.V3.HintCompact`, axioms ⊆ std3, builds on the merged base),
  STATUS-V3-SIZE corrected (lever 1 landed: measured 5.26–5.67 MB proofs, aligned bound 6,435,489,
  admission at exact 8 MiB fit; lever 2 = GoodV3 amendment, runbook in `docs/logs/v3-sizeopt-2026-10.md`;
  auxGroup g = 2 optimal).  No behavior change — the Commit-B hint-format swap is NOT in main; its
  7-step runbook (incl. Link re-route map and the ~4 h rebuild warning) is in the lane log.  AuxGroup
  sweep closed by kernel numbers (g = 2 optimal).  peta-gas/300 KiB question: scoped to a future
  WHIR-class research lane; current caps unchanged.
* **2026-10-11 (evening):** `integration/v3-20261011b` merged into main: `lane/v3-a11` (A11, A7 measure,
  `factorComplete`), `lane/v3-link` (ExtractV3Stmt at B0, v1-style `LinkV3Stmt`, `extractV3_of_link`,
  `LinkClaim`), `lane/v3-render-rcpt` (acct/size/srcp/qv renders, cap changes, A10 counter, rcpt repairs),
  `lane/v3-render-sched` (sha/ChaCha/mrk/sort/mem/cmp/ups renders, ChaCha 22, empty-capable mrk/sort),
  `lane/v3-render-asm` (`RenderBundleV3`, `CompleteV3Stmt`, `nearV3_admission_of`). See §5 and §6.
* **2026-10-11:** `integration/v3-20261011` merged into main:
  * `lane/v3-prover` at `5347fed3`: Rust prover part 1, `examples/np-udr-stark-v2/` (forked from the live `np-udr-stark-fast2`). It adds `auxGroup` g ∈ {1,2,3}, the `np-air-v2` format with public segments and `maxPub`, `pubFit` checked before any record is enumerated, and public messages in the bus equation. `conformance/run-v2.sh`: the deployed Lean v2 verifier (`np-lean-verify-v2`) accepts the Rust proofs at g = 1/2/3 and rejects them under the other g, plus 9 proof and 5 claim mutations per case (166/166). Rust's per-table layout of `nearAirV3` equals Lean's (`np-lean-export-v3 --layout g`) for all 25 tables. The inherited v1 suite passes 205/205. See its `README.md`.
  * `agent/v3-assembly` at `5ef6767d`: the `RenderV3` obligation types, `HoldsP` assembly from per-table traffic, the `traceSum` composition, and head/walk `maxLog` raised to 13/22. The lane is still active; merge its next commits the same way.
* **2026-10-10:** `integration/v3-20261010` merged into main:
  * `agent/v3-assembly` at `85a02cb1` (committed tip only), which includes `RcptV3ViewStmt` (rcpt-view package done), all per-table views from `HoldsP`, and the `LinkV3` interface. The lane is **still active**: an agent has uncommitted work in `/data/illia/nearproof-wt/integration`, so don't touch that worktree. Merge its next commits the same way.
  * `NearV3/Candidates/ProcActualGrantOperands` was fixed (binder type annotations) and committed; it was the one module that failed to build on 2026-10-09.
  * New guarded audit `zk-formal/test/AuditNearV3Admission.lean`.
* **main** (2026-10-09) contains everything below. It was merged from `integration/v3-20261009` on 2026-10-09, which combined:
  * `lane/v3-air`, `lane/v3-hpl`, `lane/v3-assembly`, `lane/v3-qvals`, `lane/v3-public`;
  * `lane/v3-d3`;
  * `codex/near-state-proof-20261008`, which was recovered from the local bundle `checkpoints/near-state-proof-20261008.bundle` because the codex sandbox could not push;
  * the uncommitted work that sat in the main checkout: about 160 newer files, the web Research page and the PR template.
* **Merge checks:**
  * Conflicts were limited to import lists, axiom-audit files and status docs. They were resolved by taking the union, with duplicates removed.
  * Every `import ZkFormal.*` resolves.
  * No new `sorry`, `axiom`, `native_decide` or `implemented_by`.
  * `make pin-check` OK. Rust: fmt, clippy `-D warnings` and 355 workspace tests pass.
  * Lean build of all ZkFormal modules: see §6.
* **Not merged, on purpose:** two old WIP commits that don't build, kept on origin:
  * `lane/v3-trie-h` `1d8b2f12`;
  * `lane/v3-rcpt-h` `4ae51a13`.
* **Live arena:** reinstalled on 2026-10-10 from main `64713b80`, to serve the web Research page (`deploy/live/arena-live build`, web build, `install`, `migrate`, `restart`; health OK, workers w1–w3 active). No challenge was signed or registered; the v3 challenge is still a draft.

## 3. What is DONE

* **v1 arena: milestones A–D, live.** NPAI (CHECKED) and native-lean routes. The succinct STARK np-udr-stark is formally admitted; it is a validity proof, not zero-knowledge.
* **Cost scoring:**
  * governed price model `pm-near-mainnet-2026q4@v2` (N_v = 50 per shard);
  * paired baseline control and pinned calibration (bench-spec-v1.6);
  * v1-7 cost board live.
* **v3 D0 (`chl_4b431651…`):** the proven normal-form reference and its fast child (rank 1) are ADMITTED.
* **v3 spec ladder:** D1, D2 and D3α, each difftested three ways (nearcore / Lean / Python) with 0 disagreements. RelD0a has B0 = 2.0 MB and A1/A2/canon0f/A7/A8.
* **Read-logging checker** (`checkD2L_eq`, `checkD3L_eq`, plus the stack-safe WASM loop):
  * proved equal to the trusted checker;
  * D3: the 115,284 saved results reproduce;
  * fresh D2 regressions recorded over both the D2 corpus and the D1 corpus;
  * WASM and trie harness parity recorded.
* **D3α read-set reference** (`examples/reexec-v3-d3`):
  * complete read-set normalisation is proved, with a single run;
  * strict public and held-out worker gates pass;
  * all 3,062 mutations rejected, including unread-value and unread-code injection.

## 4. Stream A: unified challenge `near-chunk-v3`

**Design.** One challenge whose statement is `RelD0 ∨ RelD1 ∨ RelD2 ∨ RelD3`. Candidates declare a tier, D0a < D0 < D1 < D2 < D3α, and may abstain outside it. Ranking is by tier, then cost. See `CONTRACTS.md` §11 and `BENCHMARK_SPEC.md` §17.
* **Draft:** `challenges/drafts/near-chunk-v3.draft.json`, unsigned.
* **Class weights:** ASSUMED until a mainnet replay measures them.
* **Known limitation:** four transcriptions are trusted. The follow-up is to make `Rel_Dk := RelD3 ∧ InDk`.

**Blockers, in order:**
1. ~~lean4lean fails on the D3α reference~~: fixed proof-only on `lane/d3-lean4lean` (2026-10-13). The configured
   formal check passes every gate; leanchecker, nanoda and lean4lean accept all 72 modules at default limits;
   native binaries are byte-identical. Root cause and evidence: `docs/logs/d3-lean4lean-2026-10.md`.
2. **The D0a tier needs real workload-class coverage in the draft.** An empty class list would silently allow abstention on every input.
3. ~~Domain bounds A9/A10~~: merged to main (`b06167fa`), with difftests showing 0 disagreements.
4. **Freeze, then measure, then release:**
   * freeze once;
   * run the joint w1 paired-baseline window with the cost tooling;
   * sign, register and deploy;
   * submit the reference (expect ADMITTED); hostile `near-v3-d3-lenient-codes` was retired 2026-10-14 (`adversarial/retired/`);
   * record the results.

## 5. Stream B: succinct D0a STARK (np-udr-stark-v2), the critical path

**Location:** `zk-formal/ZkFormal/NearV3/` (Assembly, Candidates, Rcpt, Qv, Render, Sched, Extract, Link, Public) and `ZkFormal/V3`, `ZkFormal/Size`.
* About 5,000 modules. Integration target: `ZkFormal.V3.Integration`.
* About 2,400 axiom-audit files in `zk-formal/test/`. Run each with `lake env lean test/<file>`.

**State (2026-10-12, main `abf81215`): the D0a certificate is unconditional.**
`Assembly/AdmissionV3.lean:nearV3_admission_final` proves the `AdmissionStatement` of
`near-chunk-validation-d0-stark` from only `hpub` (public digest binding) and `himpl` (the artifact's
implementation connection). Soundness `extractV3 : ExtractV3Stmt` (`Assembly/ExtractV3Proof.lean`)
and completeness `completeV3 : CompleteV3Stmt` (`Render/CompleteV3Chacha.lean`) are both proved.
Guarded audit `test/AuditAdmissionV3.lean` (only propext/Classical.choice/Quot.sound). Details:
`docs/logs/integration-v3-20261012d.md` and the lane logs `v3-link-2026-10.md`,
`v3-render-sched-2026-10.md` (packages 11–13), `v3-render-vbytes-2026-10.md`,
`v3-render-chacha-2026-10.md`.

* `nearAirV3`: table 20 = `SrcpDD` (DedupTable + A10 depth bits); table 9 carries the A9 word
  counter; A7 tables nodeA7/valA7/upsA7/sizeA7 (RPL 70, RPLV 71); rcpt q<128 check.
  Size bound **6,435,489 B** at g=2 (`v3MaxInner`), `v3MaxHintBytes` 1,953,115 (4+hint+inner =
  8 MiB exactly); honest hints ≤ 1,295,025 B.
* **Public format change (2026-10-12):** prepared source rows are 34 bytes `[dup, rep] ++ root`;
  dup byte 0 first occurrence, 1 consistent repeat, 2 inconsistent repeat (AIR rejects 2).
  `PreparedByteLength = 340 + 34·|lists| + …`. `prepD0` unchanged.
* Spec (unsigned draft): A7 = unfolded pre trie + native post trie ≤ B0; A11 retired; A12
  `|boundaries|+1 = |shardIds|`.

**Rust prover (2026-10-13, main `c6330302`): first real proofs, accepted by Lean.**
`examples/np-udr-stark-v2`: `npudr v3prove <case> <out>` builds all 25 `nearAirV3` tables natively
from claim + witness (`v3prepare` hint/prep/public tape, `v3trie` 2–7/21/A7, `v3rcptfam` 16–20/23/24,
`v3sched` 8–15/22, SHA collector 0/1), checks constraints + all 51 buses + public messages, and
proves at g=2. `np-lean-verify-v3` (deployed `npVerifierP challengeSpecD0a nearAirV3 split prepV3b`)
accepts proofs of 00-h10004-s3, 00-h10035-s3, 01-h10009-s1 (5.26–5.67 MB, ~12 min on 8 cores,
≤13.3 GB RSS) and rejects 14/14 mutations each. `--check-only`: all buses balance on all 81 fixtures
(64 public-d0a + 17 `conformance/fixtures-extra`, repeated source keys / empty values).
`formal/NpUdrStarkV2.certificate` = `nearV3_admission_final` (unconditional; maxRecDepth 20000).
Every Rust generator/preprocessor is differential-tested against Lean (`conformance/run-v2.sh`,
sections in `run-v2.d/`; `PROVE_V3=1` adds the real proof). Logs: `docs/logs/v3-prover-*.md`.

**Open:**
* ~~Elaboration budget / packaging~~ (2026-10-14, main `50f26055`): **the real `formal-check` with the
  D0a config (`runners/formal-checker/challenges/near-chunk-validation-d0-stark.json`) passes every
  gate with no findings** on the packaged candidate: elaboration 7,007 s serial; leanchecker 2,267 s,
  nanoda 1,148 s, lean4lean 3,223 s (all within 1 h/module, 4 h total, 2 h/run); certificate type
  matches `ArenaExpectedInst.expectedType`; native verifier model 90 modules (was 657; no `Std`),
  built in ≈ 90 s; `out/verify` byte-identical to the judge's build. `out/prepare` = `prepare_v3`,
  `out/prove` = `prove_v3` (v3 contract, reproducible). Logs: `docs/logs/v3-{package,recheck,
  model-split,d0a-challenge}-2026-10.md`. **SIGNED 2026-10-14: `chl_5607727929ca2c634a92c3f0bd4bdeb6`**
  (`near-chunk-validation-d0-stark`, trusted tree `b890e835` frozen into the live store, held-out
  commitment `sha256:56e6f599…`, seed off-repo in `nearproof-deps/keys`, set in
  `nearproof-deps/heldout/near-chunk-validation-d0-stark`); candidate re-pinned. NOT yet registered
  or deployed (user: stop after signing). Hostile `near-v3-d3-lenient-codes` retired. near-chunk-v3
  re-frozen with the D1a tier and **SIGNED 2026-10-14: `chl_497bbbf1a6a5abc5b3448e0bc1a56997`** (tree
  `66bba27e` at `85adc6c0` in the live store; not registered/deployed). D0a was registered and deployed
  2026-10-14 (release `9da1032a`); its first live FORMAL_CHECK hits the Firecracker per-module copy
  overhead (lane judge-fc-batch is fixing the runner; see `docs/logs/v3-deploy-d0a-2026-10.md`).
  D1a spec is on `lane/v3-d1a-spec` — do NOT merge it before the D0a draft is signed (any new
  **Elaboration budget (2026-10-14, `d2f27096`):** proof-only `codec_fast` tactic, NearAirCheck g=2
  split, GWalk/GRows joint simp: serial elaboration 9,100 s → 5,953 s (−35%), lean4lean peak 13.6 →
  6.9 GB, nanoda 604 s; no module > 200 s. Re-run the judge formal-check before submitting (the
  certificate sources changed; the 90-module verifier model did not). Log: `docs/logs/v3-elab-budget-2026-10.md`.
  D3a / 1 Pgas study and user decisions: `docs/zk-formal/V3-D3A-STUDY.md` (sections D, 10).
  `spec/lean` file breaks regeneration at freeze commit `3c2a4563`).
* ~~Oracle~~ (lane oracle-d0a, 2026-10-13): `oracle/v3-d0a` implements A7 native post trie, A12,
  empty-key-extension fix, offline `unfold-case`; public-d0a regenerated (all `.bin` byte-identical,
  only meta.json); difftests 0 disagreements on public-d0a, fixtures-extra, full/heavy scratch corpora,
  d1run, d2corpus (`docs/logs/oracle-d0a-2026-10.md`). **Empty main pre-state is outside RelD0**
  (user decision 2026-10-13): Lean/Python/oracle reject it; mutant `public-d0a/mutants/
  00-h10004-s3-w.empty_pre_state` (re-add after any regeneration; command in its meta); spec v0a §1.
* ~~Fixture coverage~~ (lane v3-prover-cover): `fixtures-extra/d0` has 39 accepted cases incl. 9 ChaCha
  (1–597 words, block boundaries) and 13 upsert-path cases (all 11 terminal cases / 12 part kinds);
  real proof of x-bw-implicit accepted by Lean (`docs/logs/v3-prover-cover-2026-10.md`).
* **Rechecked (lane v3-prover-digest):** the schedqv bus-1 DIGEST imbalance was `npudr v3bus` evaluating
  with zero publics (mrk root row reads the outcome root from `p146..177`); `v3prove` was right. `v3bus`
  fixed; `run-v2.d/digest.sh` checks BYTES/DIGEST on all 81 (`docs/logs/v3-prover-digest-2026-10.md`).
* **Argued, not proved (prover-side only):** receipts read the pre-scheduler trie (scheduler writes only
  key `[0,15]`); native execution skips grant distribution and the refund-forwarding limit check.
* Cleanup: `ChachaWords.lean` duplicates `A9Words.coreMid`/`runMid_st`; 2 `clippy -D warnings` errors
  (`protocol.rs`, `chacha.rs`); Lean `rankWalks` and Rust `ups::uu` are quadratic.
* Conformance: full `run-v2.sh` on `c6330302` 2,126 PASS; its 92 FAILs were stale/missing Lean exes
  (fixed in `run-v2.sh`, `7bc2086e`); reruns schedqv 143 PASS, prove 18 PASS (real proof accepted).

**Judge budgets (user decision 2026-10-13: 4 h elaboration).** The formal checker enforces
`Limits::default` (`runners/formal-checker/src/pipeline.rs`, since `a0990606`): 1 h per module, 4 h
total elaboration, 2 h per recheck run, 4 h per rechecker; the older 1,800 s figure is superseded
(DESIGN.md F6). Measured (judge-style clean serial `lean -o`, warm trusted oleans): the unconditional
`nearV3_admission_final` closure was 4,514 modules before pruning, projected ≈ 5,000–6,000 s (first 1,523 modules
took 1,800 s); slowest: `Candidates.HorizontalAuxCheck` 140 s, `Candidates.VerticalPriorFusion` 124 s,
`Render.Ups.GWalk` 86 s, `Render.Node.Links` 80 s, `Assembly.NearAirCheck` 68 s; 49 modules ≥ 10 s ≈
1,650 s. The conditional 748-module certificate (589 s) does NOT prove admission — never use it.
* **Pruning (done, `ea459caa`):** closure 4,514 → **3,964 modules**; full single-core serial
  `lean -o` (conservative; Lean's parallel elaboration is faster) 10,242 s → **8,734 s**. Import
  redirection + `*Core` splits of 16 modules; no code deleted; constant-type fingerprints
  unchanged (`zk-formal/scripts/TypeHashes.lean`); tools `ClosureDeps.lean`, `judge-time.py`;
  log `docs/logs/v3-prune-2026-10.md`. Packaged closure re-vendored (3,960 modules; `sync-lean.sh`
  layout bug fixed). Remaining hot spots: `CodecEndInt` 1,695 s, `CodecRecInt` 1,255 s,
  `CodecHeader` 335 s (≈ 38% of the closure; `simp` inside `codec_int`), `GWalk` 192 s,
  `Node.Links` 182 s. Proposed next levers (not applied): faster `codec_int`, per-case codec
  modules, a g = 2-only `NearAirCheck` lemma.
* ~~Rechecks~~: all pass and fit (see above; `docs/logs/v3-recheck-2026-10.md`).
* **Prover resource limits (resolved, `7cd8a982`):** draft `max_prove_ms` 600,000 and 16 GiB / 8 vCPU.
  `v3prove` now takes 263–312 s wall with cgroup `memory.peak` ≤ 12.6 GiB on 8 vCPU (4 Zen 5 cores ×
  2 threads, `HEAVY_MEM=16G`); proofs byte-identical to before; Lean accepts; 14/14 negatives.
  Earlier 710–749 s figures were scalar builds (host `~/.cargo/config.toml` rustflags override the
  crate's AVX2 flags; `build.sh` with a fresh HOME does get AVX2) and the old RSS figures were
  last-phase only. Cloud 8-vCPU risk: heaviest fixture ≈ 400–500 s. Log `docs/logs/v3-prover-perf-2026-10.md`.

**Quality notes for whoever continues:**
* Converge on `ExtractV3Stmt` / `CompleteV3Stmt`; every new module should sit on one of them.
* `nearAirV3` is no longer frozen, but each lane edits only its own tables' entries in
  `Assembly/NearAir.lean`; the lead recomputes the combined size bound at merge (`#eval
  sizeMaxAligned nearAirV3.toAir (pg 2)`), since lanes' bounds don't merge textually.
* Keep the guarded axiom audits.

## 6. Verification status of this merge

* **2026-10-12 (`integration/v3-20261012d`, main `abf81215`):** `lake build
  ZkFormal.V3.Integration` passes (4,692 jobs); 2,787 dependents of the 140 changed modules
  rebuild (153 top-level modules, 5,357 jobs, 0 errors); 15 guarded audits incl.
  `AuditAdmissionV3` pass; `make pin-check` OK; no sorry/axiom/native_decide/implemented_by.
  Difftest not re-run.
* **2026-10-11 (`integration/v3-20261011b`):** from clean caches (see §7), `lake build
  ZkFormal.V3.Integration nearspec-v3-check-d0a` passes (2,753 jobs); all 3,333 modules
  depending on the merged changes rebuild (`lake build` of their 185 top-level modules: 5,128
  jobs, 0 errors); the 14 new or changed audits and `AuditNearV3Admission` pass; `make pin-check` OK;
  D0a difftest on the public fixtures (300 cases): 0 disagreements.
* Earlier builds reported by lanes before the cache repair may have run against stale
  artifacts; the numbers above supersede them.
* **Not re-run:** the ~2,400 older audit files, the D3 reference check-local, the full difftest
  corpora (only public-d0a and the A11 measurement on d1run/d2corpus).

## 7. Process rules learned (2026-10-07 to 2026-10-11)

* **Never hard-link (`cp -al`) a `.lake` between worktrees.** Lake rewrites `.trace` files in
  place, so a build in one worktree marks modules up to date in all others while their `.olean`
  stays stale (false build results). On 2026-10-11 every mismatched trace was deleted and all
  small cache files de-linked. Copy with `cp -a` (or rebuild) instead.

* **Push every checkpoint to origin.** If the sandbox has no network, say so in the final report. Do not leave work only in bundles or as untracked files in the main checkout.
* **One worktree per agent.** Never work in `/data/illia/nearproof` itself; integrate on an `integration/*` branch.
* **Progress notes go to `docs/logs/`, not this file.** Don't make commits that only touch the log on main.
* **Never overwrite another lane's module.** Rename instead; this already caused one collision, which was caught and restored.

## 8. Smaller follow-ups

* ~~**Succinct badge**~~ DONE (lane/stream-a, 2026-10-16, `610427283`): contracts v1.8 additive —
  `CoverageSpec.succinct` + §17 slope test recomputed by the control plane into the signed report
  and the board (`SUCCINCT` badge, "succinct only" filter). No signed draft sets thresholds yet
  (successor decision). Docs: `docs/logs/stream-a-2026-10.md`.
* ~~**Mainnet replay**~~ DONE (same lane): `tools/mainnet-replay` measured 13,770 mainnet chunks
  (1,378 consecutive blocks, PV 86): D3a family ≈ 60 % of chunks (`d3-maxgas` 30.9 % — FC gas
  ≥ G_α/2), quiet ≈ 25 %, transfers ≈ 5.5 %, D2 ≈ 0.2 %. Measured G_α rows: FC-chunk median
  0.71 × G_α, p90 3.9 ×, max 156.9 × — today's G_α = 3.45 Tgas is far below busy-shard traffic.
  Artifacts `docs/e2e-results/mainnet-replay-2026-10/`; adoption is a versioned-successor/user
  decision (CONTRACTS §11).
* **Independence of the clean-room Python VM:** it was tuned against nearcore black-box runs.
  Documented 2026-10-16 (lane/heldout-aggregate): what that means, what the difftests do and do
  not constrain, and four follow-up options — `docs/research/python-vm-independence.md`.
  Independence itself is **not** achieved.
* **Future challenges:**
  * 1 Pgas as a single STARK, which needs Goldilocks, a distributed prover and precompiles;
  * a cross-shard whole-block proof (`BENCHMARK_SPEC.md` §14.11).
* **Disk:** `/` about **98%** (20 GB free), `/data` about 90% (2026-10-11). Remove merged worktrees and their build dirs once they are clean and pushed. There are about 110 worktrees under `/data/illia/nearproof-wt`; most belong to merged lanes. The untracked drafts left in the `v3-air` and `v3-assembly` worktrees are superseded by main.

## 9. Key documents

| Topic | Documents |
|---|---|
| Architecture and contracts | `ARCHITECTURE.md`, `CONTRACTS.md`, `CHANGELOG-contracts.md` |
| Security model | `TCB.md`, `THREAT_MODEL.md`, `SECURITY_POLICY.md` |
| Benchmarking and operation | `BENCHMARK_SPEC.md`, `LIVE.md` |
| v3 domain specs | `spec/near-chunk-validation-{d0,v0a,d1,d2,d3}.md` |
| Requirements | `docs/requirements/` |
| ZK formalisation | `docs/zk-formal/` (DESIGN, V3-D0-DESIGN, STATUS-*) |
| Lane status files | `STATUS-V3-AIR.md`, `STATUS-V3-D3.md` |
| Raw log | `docs/logs/v3-progress-log-2026-10.md` |
| Literature catalogue | `docs/research/literature/INDEX.md` (topic index, CATALOG, refs.bib); unexploited items ranked in `OPPORTUNITIES.md` |
