# Lane `lane/v3-sched`: the bandwidth scheduler's state-dependent core in the AIR (np-udr-stark-v2)

Design: `V3-D0-DESIGN.md` §10–§11 (round-2 decision (c): under the 8 MiB formal cap the
scheduler's state-dependent core is in-AIR; its claim-only inputs are computed natively and
published). Target: `NearSpecV3.Scheduler.runCore` (`spec/lean/v3/NearSpecV3/PrepD0.lean`;
`run_eq_core : run = pubOf.bind runCore`). Lean: `zk-formal/ZkFormal/NearV3/Sched/`.
v1 and every existing v2/v3 definition are untouched; `spec/lean/v3` is not edited.

Rules: no `sorry` / `axiom` / `native_decide`; axioms ⊆ {propext, Classical.choice, Quot.sound}.

## 0. Plan and milestones

| # | milestone | content | state |
|---|---|---|---|
| M0 | design | tables, buses, message formats, public data, amendments needed, `W_eq` estimate (§2–§4) | **done** |
| M1 | spec-side refinement | `runCore` decomposed into the AIR's phases, each **proved** equal to the spec (§5); executable event model `coreEv` = `runCore` on 600/600 vectors | **done** |
| M2 | tables | six `Table` values (§3), kernel-checked budget (`W_eq` = 814 at g = 1), honest generators for all six (`Gen/*`), constraint evaluator + bus-balance tests on the 600 vectors, mutants (§8) | **done** |
| M3 | soundness | per table: `…Local → ∃ v, Wf v ∧ Traffic …` (L5 style), bus contracts (comparator, memory, scan, codec), link lemma: `schedCore_sound` | **started** (§7): comparator contract, memory row view + segments, abstract memory consistency |
| M4 | completeness | honest traces satisfy every constraint, traffic = expected lists; `schedCore_complete`; height bounds | open |
| M5 | integration | message formats agreed with `v3-trie` (`VBYTES`, `upsV3`) and the assembly (public segments, `Prep.fwd`), cuts | open |

## 1. Inputs and what is native

Per applied block τ (main, then implicit oldest first), `SchedPub_τ` is claim-only (native):
shard ids, `Params`, the link-allowed matrix, the requests (raw 5-byte bitmaps per the spec
lane's in-progress switch; converted in-AIR), the seed `prev_block_hash`, `sha256(all_shards)`.
In-AIR: decode of the previous `0x0f` value (canonical, Canon0f), allowances, budgets, request
processing with the run-wide ChaCha20 RNG, distribute-remaining, the new `0x0f` value bytes and
its sanity hash, and the grants checked against `Prep.fwd`.

## 2. Spec facts the design relies on (all to be **proved** in M1)

1. **Base grants never fail on budgets.** With `Params.calculate pv86 n`: `(n−1)·base ≤ MSB − MSG`,
   so `n·base ≤ 405,696 < MSB`; and `base ≤ fair = MSB / n ≤ a1` for every link. Hence after
   `increase_allowances` + `grant_base_bandwidth`: `a2[l] = allowed ? a1[l] − base : a1[l]`,
   `granted = allowed·base`, budgets `MSB − base·#allowed(row / column)` — budgets are claim-only.
2. **Increases are set-bit differences.** `requestValues` is strictly increasing and `> base`, so
   `increases` = `[v[c₁] − base, v[c₂] − v[c₁], …]` over the set bits `c₁ < c₂ < …`.
3. **Process loop = rounds with strictly decreasing keys.** Invariant `allowance[q.link] ≤ key`
   for every queued request; a re-push goes to a key `< k` unless `k = 0`. So popped keys strictly
   decrease, then (possibly) repeated `0` rounds; a round's bucket = all pushes targeted at it
   (`(key, z)`, `z` = 0-round ordinal) in push-time order.
4. **Distribute never breaks** (`links_num` counts exactly the allowed links still to visit), so
   every allowed link `(s, r)` in sorted order gets `min(⌊SL/SN⌋, ⌊RL/RN⌋)`.
5. **Canonical prev** (Canon0f) with distinct shard ids: `allow0[l] = a_l` (record `l`).

## 3. Tables (v0; `W_eq` = width + 8·interactions + 8·(degree − 1), g = 1)

| table | rows | role |
|---|---|---|
| `schV3` codec + link | one per byte of the `0x0f` encoding (pre and post in lockstep), + 32 hash rows per τ | pre bytes → `VBYTES`, post bytes → `upsV3`; id bytes via public + delay line; sanity hash via SHA; per link: `a1 = min(a0+fair, MA)`, `a2`, memory init/final, grants vs `fwd` |
| `sscV3` scan | 20 per request (2 bitmap bits per row) | set bits → increases `INC(τ, v=rid·64+j, inc, last, s, r)`; initial push |
| `sprV3` process | one per processed request-step | bucket entries (push log, ts order), shuffle in/out/header, `INC`, 3 memory ops, re-push |
| `smmV3` memory | one per access | address-sorted segments: init, ops in time order, final |
| `scpV3` comparator | one per comparison | `(x, y, [x ≥ y])`, 24-bit |
| `sdsV3` distribute | per τ: 2n sorted shard rows + n² grid cells | sorted orders (key `avg·64 + idx` strictly increasing), grid with receiver delay line |
| `chachaV3`/`genV3`/`shufV3` | lane v3-chacha | one instance set for the scheduler |

**Kernel-checked** (`Sched/BudgetCheck.lean`: `report_g1`, `weqSched_g1`), g = 1:

| table | file | width | interactions | degree | `W_eq` | maxLog |
|---|---|---:|---:|---:|---:|---:|
| `schV3` codec + link | `Tables/Codec.lean` | 106 | 13 | 4 | 234 | 22 |
| `sscV3` scan | `Tables/Scan.lean` | 50 | 6 | 4 | 122 | 22 |
| `sprV3` process | `Tables/Proc.lean` | 64 | 11 | 4 | 176 | 22 |
| `smmV3` memory | `Tables/Mem.lean` | 18 | 4 | 4 | 74 | 22 |
| `scpV3` comparator | `Tables/Cmp.lean` | 33 | 1 | 4 | 65 | 22 |
| `sdsV3` distribute | `Tables/Dist.lean` | 55 | 8 | 4 | 143 | 22 |
| **total** | | 326 | 43 | | **814** | |

(At g = 3 the grouped aux constraints have degree 8; g = 1 is the better setting for these
tables.) With lane v3-chacha's 654 the scheduler costs ≈ 1,468 `W_eq` ≈ 1.27 MB of proof (at
≈ 864 B per `W_eq`). The comparator is 29-bit: the distribute sort key `avg·64 + shard` reaches
≈ 2^28 (found by `SchedFullTest`; 25 bits were too few).

**Proposed cuts** (not implemented):
* codec: a per-byte digest output from SHA (`DBYTE (Id, i, b)`) instead of the 34-element
  `DIGEST` removes the 32-column shift register (−32); a combined pre/post value message agreed
  with `v3-trie` (`VBYTES` + `SPOST` → one interaction) (−8);
* process: the three memory GRANT sends on three sub-rows per step (−16); a ChaCha key registry
  (lane v3-chacha's proposal) removes the 16 key limbs (−16);
* the process/scan/memory/distribute row-kind structures could share one table (−24 per merged
  quotient), at the cost of a harder view proof.

## 4. Requests to other lanes

* **Spec (proposed amendments, claim-decidable):**
  * *layout ids distinct* (`c.layout`): every real layout; without it `allow0` needs a duplicate
    map (one more bus).
  * *A8 `c.bw_requests`*: every sender's request list has at most `n` entries (nearcore: one per
    receiver). Without a claim-side bound, `Σ_τ R_τ` is bounded only by the 1 MiB claim and
    header sharing across blocks (up to 32 × 150 k requests) — beyond any table height.
* **Trie (`v3-trie`):** the pre value reaches `valV3` as `VBYTES (vid, pos, b)` sent by `schV3`;
  `schV3` needs `(τ, present, vid)` for the `0x0f` read of instance τ (bus `S0F`); the post value
  leaves as `SPOST (τ, pos, b)` with header `(τ, len)` for `upsV3`.
* **Assembly:** public segments (§5), `Prep.fwd` as `(τ = 0, link, total)`.

## 5. M1 — spec-side refinement (all **proved**, axioms ⊆ {propext, Classical.choice, Quot.sound})

| theorem | file | content |
|---|---|---|
| `runCore_eq` | `Sched/Model.lean` | `runCore pub prev = coreOf …` (converted requests explicit) |
| **`core_compose`** | `Sched/Spec/Compose.lean` | `coreOf` = decode of the canonical prev (`PrevCanon`) → closed-form link pass → replayed rounds (`process_rounds` hypotheses) → sorted grid; output state = canonical links with the final allowances and `sha256(h₀ ‖ ash)`, grants = `applyGrants` of the grid (needs `n ≤ 64`, distinct ids < 2^64) |
| `decode_encode`, `allow0_canon(_get)`, `indexOf_nodup` | `Spec/Canon.lean` | canonical prev decodes; `allow0[l]` = record `l` |
| `linkPass_eq`, `pv86_facts` | `Spec/LinkPass.lean` | increase + base grants = closed form (budget checks never fail, `a1 ≥ fair ≥ base`) |
| `increases_eq_incsFrom`, `convertRequests_eq_convRaw`, `incsOf_pos`, `incsOf_length_le` | `Spec/Conv.lean` | increases = value differences over the set bits; conversion from resolved raw requests |
| `bucketsOf_eq_groups`, `groups_pop` | `Spec/Buckets.lean` | the spec's bucket map of a push log; popping the largest key |
| `processBucket_runL`, `shuffle_map`, `length_shuffle` | `Spec/Rounds.lean` | one round's processing as the AIR replays it |
| **`process_rounds`** | `Spec/Loop.lean` | `processRequests = some stF` from the AIR's rounds: replay (`simR`), push-log permutation (the `SPUSH` balance), round order, valid / nonempty rounds, entry time stamps strictly increasing and below the round start (start time any `t₀ ≥ |reqs|`) |
| **`distribute_eq_grid`**, `gridGrants_get`, `sortByKey_eq_of_sorted`, `applyGrants_granted` | `Spec/Dist.lean` | `break` never fires; per-cell recurrences `SE`/`RE`; sorted orders are the unique `avg·64 + idx`-sorted permutations |

Facts found on the way: the popped keys strictly decrease except trailing key-0 rounds (a re-push
key is below the popped key unless both are 0); `distribute_remaining_bandwidth`'s `break` is dead
code; base grants never fail on budgets.

## 6. M3/M4 plan (soundness and completeness of the tables)

Target statements (instance τ of a v2 AIR containing the six tables, lane v3-chacha's three
tables, the public segments rendered by `Render.render` from the instances' `InstPub` and
`Prep.fwd`, with the bus-ownership side conditions of §6.1):

* **`schedCore_sound`**: `HoldsP AP pub tr` ⇒ for every instance τ, with `v_τ` the bytes the codec
  sends on `VBYTES` for τ (absent if `present = 0`): `v_τ` is a canonical state (Canon0f) and
  `runCore pub_τ v_τ = some out` with `out.state` = the bytes sent on `SPOST` for τ, and in τ = 0
  every forwarding demand is `≤` its link's grant.
* **`schedCore_complete`**: for pubs with `PubOk` (n ≤ 64, distinct ids, A8 request bound) and any
  canonical previous states, the honest traces (`Gen/*`) satisfy every constraint, have 0/1
  multiplicities, and their traffic on every scheduler bus is the expected list (public records,
  `VBYTES`/`SPOST`/SHA messages); heights `≤ 2^22` under A7 (`Σ_τ (|pre| + |post|) ≤ 3,000,000`)
  and A8.

Soundness chain (per τ), using M1's `core_compose`:
1. comparator: `cmp_sound` (**done**);
2. memory: row view (**done**, `View/Mem.lean`); segments (one per address, by `INIT`
   uniqueness on `SOP`); **memory consistency**: by induction over process time, each GRANT's
   `vin` is the replayed state (`simR`) at its address — ops on an address are exactly its
   segment's rows (bus balance), sorted by time (comparator), chained;
3. codec: header/records/trailer structure; pre bytes = `State.encode ⟨canonLinks ids a0, h0⟩`
   (`decode_encode`); link pass = `linkPass` (INIT values); post bytes = the same encoding with the
   final allowances and the SHA digest of `h0 ‖ ash`;
4. scan: the `INC` records of request `cid` are `incsOf` of its bitmap (`Spec/Conv`), the initial
   pushes are `initPushes`;
5. process: rounds `RoundD` from headers/entries; `process_rounds`' hypotheses: `hperm` from the
   `SPUSH` balance (filtered by τ), `hord`/`hval`/`hts` from headers and the comparator, `hsim`
   from the shuffle contract (`shuffle_sound`, RNG positions chained from `Rng.ofSeed seed =
   rngAt (leWords seed) 0`) and memory consistency;
6. distribute: sorted orders (`sortByKey_eq_of_sorted`), cells = `gridGrants_get`;
7. assemble with `core_compose`.

### 6.1 Bus ownership (side conditions)

`scpV3` the only receiver on `SCMP`; `smmV3` the only receiver on `SOP` and sender on `SFIN`;
`sscV3` the only sender on `SINC`; `SPUSH` sent only by `sscV3`/`sprV3`, received only by `sprV3`;
`SDL` only codec + public; `SDLX` only `sdsV3`; `SDG` sender `sdsV3`, receiver codec; public
segments only on `SPUBB`, `SPAR`, `SRAW`, `SLINK`, `SSHD`, `SDL`; lane v3-chacha's conditions on
its buses (`STATUS-V3-CHACHA` §6).

## 7. M3 progress (all **proved**, axioms ⊆ {propext, Classical.choice, Quot.sound})

| theorem | file | content |
|---|---|---|
| `Cmp.cmp_row` | `Tables/Cmp.lean` | a comparator row with `x, y < 2^25` has `b = [y ≤ x]` |
| `send_matched`, **`cmp_sound`** | `Link/Cmp.lean` | dual of lane v3-chacha's `recv_matched`; every active `SCMP` send `(x, y, b)` with `x, y < 2^25` has `b = [y ≤ x]` (given `CmpOwn`) |
| `Mem.row_flags`, `row_next`, `row_after_lst`, `row_pad`, `row_last`, `row_first`, `row_init`, `row_read`, `row_grant` | `View/Mem.lean` | memory rows: one-hot kinds, segment continuation with carried `addr, v→vin, t→tp, w→wp, al, isL`, boundaries, INIT/READ/GRANT semantics (values mod `P`) |
| `Mem.seg_back`, **`Mem.seg_start`** | `View/Mem.lean` | every active row lies in a segment that starts at an INIT row |
| **`mem_consistent`** | `Spec/MemCons.lean` | abstract offline memory checking: chained time-ordered segments + frame + correct steps ⇒ every op reads the simulated state |

## 8. M2 tests (executable, from `zk-formal/`)

* `test/SchedModelTest.lean` (≈ 4 s): the event model `coreEv` = `runCore` on **600/600**
  vectors (6,535 rounds, 1,017 key-0 rounds, 9,981 steps), every structural check holding.
* `test/SchedTablesTest.lean [limit]` (≈ 22 min for 600, interpreted): `Gen.run` (checked step by
  step against `processEv`/`coreEv`, shuffles replayed with `genAt`), honest traces of `scpV3`,
  `smmV3`, `sscV3`, `sprV3` **and** lane v3-chacha's `shufV3`/`genV3`/`chachaV3` (fast row
  builders, equal to the lane generators cell by cell on a sample): **600/600 vectors, 0
  violations, 0 non-0/1 multiplicity bits**, buses `SCMP SOP SFIN SINC SPUSH SSIN SSOUT SSMEM SGEN
  SSHUF SCHACHA SPUBB SPAR SRAW` balanced against the expected external traffic; the renderer
  (`keyRecs`, `parScan`, `rawRecs`) agrees on all 600; **37/37** single-cell mutants caught.
* `test/SchedFullTest.lean [limit]`: all six tables (codec and distribute included) per vector;
  constraints, multiplicity bits, balance of `SCMP SOP SFIN SINC SPUSH SPUBB SPAR SRAW SLINK SSHD
  SDL SDLX SDG S0F SPOST VBYTES BYTES DIGEST` with the renderer's public records and the
  expected external traffic, where the expected `SPOST` bytes are **`runCore`'s new state** and
  `VBYTES` the canonical previous state; forwarding demands = half of each grant of sender 0;
  codec / distribute mutants.

Honest-value conventions (for a Rust generator): scan `INC` multiplicity = bit set ∧ increase
processed; `sprV3`'s first padding row carries the key register and the instance values of the
last active row, `ikc = (kc − 15)⁻¹` on every row; a scan param row only for instances with a
converted request (the public `SPAR` tag-1 record follows the same rule).
