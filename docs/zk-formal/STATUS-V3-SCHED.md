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
| M2 | tables | six `Table` values (§3), kernel-checked budget (`W_eq` = 934 at g = 1), honest generators for all six (`Gen/*`), constraint evaluator + bus-balance tests on the 600 vectors, mutants (§8) | **done** |
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
| `schV3` codec + link | `Tables/Codec.lean` | 114 | 14 | 4 | 250 | 22 |
| `sscV3` scan | `Tables/Scan.lean` | 96 | 6 | 4 | 168 | 22 |
| `sprV3` process | `Tables/Proc.lean` | 64 | 11 | 4 | 176 | 22 |
| `smmV3` memory | `Tables/Mem.lean` | 18 | 4 | 4 | 74 | 22 |
| `scpV3` comparator | `Tables/Cmp.lean` | 33 | 1 | 4 | 65 | 22 |
| `sdsV3` distribute | `Tables/Dist.lean` | 113 | 8 | 4 | 201 | 22 |
| **total** | | 438 | 44 | | **934** | |

(At g = 3 the grouped aux constraints have degree 8; g = 1 is the better setting for these
tables.) With lane v3-chacha's 654 the scheduler costs ≈ 1,588 `W_eq` ≈ 1.37 MB of proof (at
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

* **Spec (proposed amendments, claim-decidable, true of every honest D0 claim):**
  * *layout shard ids distinct* (`c.layout`). M1's `core_compose` assumes `ids.Nodup` (`allow0` of
    a canonical state is then record-by-record); without it the codec needs a duplicate map
    (one more bus).
  * *A8 `c.bw_requests`*: every sender's request list has at most `n` entries (nearcore: one per
    receiver). Without a claim-side bound, `Σ_τ R_τ` is bounded only by the 1 MiB claim and header
    sharing across blocks (up to 32 × 150 k requests), beyond any table height; with A8 and A7
    (`Σ_τ N_τ ≤ 125 k`) the scan needs `≤ 20·Σ R_τ ≤ 2.5 M` rows.
  * The in-progress switch to raw bitmaps (`SchedPub.raw/values`, `convertRaw`) needs **no AIR
    change**: the AIR consumes resolved raw requests (`Render.rawRecs`, indices resolved natively);
    `Spec/Conv.convertRequests_eq_convRaw` is the bridge (`convertRaw` from `toBTreeMap requests`
    is the same list). Once it lands, `runCore_eq` changes from `pub.reqs` to `convertRaw …`
    (one line).
* **Trie (`v3-trie`)**, message formats:
  * `S0F (τ, present, vid)` — the `0x0f` read of instance τ (present flag and the value record
    id), received once per τ by the codec;
  * `VBYTES (vid, pos, b)` — the codec **sends** the previous value's bytes (lockstep with
    `valV3`'s receive);
  * `SPOST (τ, pos, b)` — the new value's bytes for `upsV3`, `pos < 37 + 24N`;
  * the bytes are canonical; `upsV3` may rely on the value length `37 + 24·n²`.
* **SHA**: the sanity hash uses message kind `K_SCH = 11` (`Id = 11 + 16τ`), 64-byte input.
  Proposal: a per-byte digest output (`DBYTE (Id, i, b)`) would save the codec's 32-column shift
  register.
* **Assembly:** public segments of `Render.render` (`SPUBB`, `SPAR`, `SRAW`, `SLINK`, `SSHD`, `SDL`
  send/receive), `Prep.fwd` as per-link demands of instance 0; bus ownership §6.1.

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
| `Proc.entry_row` | `View/Proc.lean` | process entry rows: `ok = cS·cR·cL`, `last = [rem = 0]`, `za = [alOut = 0]`, push gate |
| `Dist.div_of_row`, **`Dist.cell_div`**, **`Dist.shard_div`** | `View/Dist.lean` | distribute divisions are exact integer divisions (from the new range checks), `gb = min` via the comparator bit |
| `Scan.row_*`, `Scan.q_ranges`, `Scan.q_exact`, `struct_all`, `vals_all`, **`scan_request`** | `View/Scan.lean`, `View/ScanReq.lean`, `View/ScanSpec.lean` | a request block: 20 rows, bits = the bitmap's bits, `m` = number of set bits, every sent `INC` is `(τ, 64·cid + j, (incsOf p bm)[j], len − j − 1, s, r, link)` (at most once each), end-row PUSH / READ messages; the process side must show every needed `INC` is used |
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
* `test/SchedFullTest.lean [limit]` (≈ 16 min for 600): **600/600 vectors, 0 violations, all listed buses balanced, 28/28 codec/distribute mutants caught**; all six tables (codec and distribute included) per vector;
  constraints, multiplicity bits, balance of `SCMP SOP SFIN SINC SPUSH SPUBB SPAR SRAW SLINK SSHD
  SDL SDLX SDG S0F SPOST SPLEN VBYTES BYTES DIGEST` with the renderer's public records and the
  expected external traffic, where the expected `SPOST` bytes are **`runCore`'s new state** and
  `VBYTES` the canonical previous state; forwarding demands = half of each grant of sender 0;
  codec / distribute mutants.

Honest-value conventions (for a Rust generator): scan `INC` multiplicity = bit set ∧ increase
processed; `sprV3`'s first padding row carries the key register and the instance values of the
last active row, `ikc = (kc − 15)⁻¹` on every row; a scan param row only for instances with a
converted request (the public `SPAR` tag-1 record follows the same rule).

## 9. Binding interface with `v3-trie` / `upsV3` (program lead, V3-D0-DESIGN §12; STATUS-V3-TRIE §2.3.1)

* `S0F (τ, present, vid)`: `upsV3` → codec (received on the instance's first row); `vid = 0` if absent.
* `VBYTES (vid, pos, b)`: codec → `valV3`, the bytes of the read `0x0f` value (when present).
* `SPOST (τ, pos, b)`, `pos < L`: codec → `upsV3`, the bytes of the written state.
* `SPLEN (τ, L)`: codec → `upsV3`, once per τ (bus 61, sent on the first row, `L = 37 + 24·N`
  computed by the codec; `upsV3` must not assume it). **Implemented** (`Tables/Codec.lean`, +8 `W_eq`).
* `upsV3` hashes the post value under SHA kind `K_VUPS = 12`; the sanity hash keeps `K_SCH = 11`.
  Kind registry: 1–10 v1, 11 SCH, 12 VUPS, 13 SRC, 14 VAK, 15 and 0 reserved.

## 10. Range audit (program lead, after the `sdsV3` division gap)

Every division, comparison and subtraction of the six tables, and what makes it exact.
"Link layer" means a fact the soundness link (§6) must establish from other tables; those are
proof obligations, not table gaps.

| table | operation | check | status |
|---|---|---|---|
| `sdsV3` | `avg = left / links` (shard rows), `⌊SL/SN⌋`, `⌊RL/RN⌋` (cells) | **was: only `N − 1 − r` in 6 bits** (gap: `r`, `q` free) → now `q < 2^23` (23 bits), `r < 64` (6 bits), `N − 1 − r < 64` (6 bits) ⇒ `q·N + r < 2^30 < P`, exact | **fixed**, proved `Dist.div_of_row`, **`Dist.cell_div`**, **`Dist.shard_div`** |
| `sdsV3` | `min(q1, q2)` | comparator `(q1, q2)`, operands `< 2^23` by the new bits | sound (`cmp_sound` + `cell_div`) |
| `sdsV3` | sort key `q2·64 + shard` vs previous | comparator, key `< 2^29` (`q2 < 2^23`, shard byte from public `< 64`) | sound |
| `sdsV3` | `L2 − gb`, `SL − gb`, `N − al` | `gb ≤ q ≤ L/N ≤ L`; `N ≥ 1` on allowed cells (`r < N`) | no borrow (`cell_div`) |
| `sscV3` | `40·Q + rem = D·(pos+1)` (×2 per row) | **was: only `rem` in bits** (gap: wrong `rem` ⇒ non-integral `Q`) → now `Q < 2^23` (23 bits) ⇒ exact | **fixed**; proved exact in the scan view (`Scan.q_ranges`, `Scan.q_exact`, used by **`scan_request`**) |
| `sscV3` | `inc = val − cur`, `rem = m − j − 1` | values strictly increasing (`requestValues_strict`), `j < m` at set bits | no borrow (scan view) |
| `schV3` | `a1 = min(a0 + fair, MA)` | comparator at byte 2, `ap < 2^24` needs pre bytes `< 256` → **now 8 bits on `bpre`** (was relying on `valV3`) | **fixed** |
| `schV3` | `a2 = a1 − al·base` | `a1 ≥ min(fair, MA) ≥ base` from public params (PubOk) | no borrow |
| `schV3` | post allowance bytes | `bpost` 8 bits, high bytes 0, `Σ = afin` | sound |
| `schV3` | forwarding `ft ≤ gfin + gb` | comparator; `gfin + gb < 2^29` | link layer (grants ≤ sender budget) |
| `smmV3` | GRANT `v = vin − ok·(sf ? inc : vin)` | comparator `sf = [inc ≤ vin]`; `vin, inc < 2^29` | link layer: induction (`v ≤ vin`, INIT values ≤ 4.5 M, `inc` from the exact scan values) |
| `smmV3` | time order `tp + 1 ≤ t` | comparator; times `< 2^29` | link layer (process times `≤ 2^20 + height`, scan `cid + 1 < 2^16 + 1`) |
| `smmV3` | `w = wp + ok·inc` | — | link layer (`Σ` grants on a link ≤ sender budget) |
| `sprV3` | round keys `Kq ≥ K + 1`, entries `ts` order, `ts < T` | comparator; keys = allowances or sentinel `2^24`, times `< 2^22` | link layer (operand bounds) |
| `sprV3` | `ok = cS·cR·cL`, `[rem = 0]`, `[alOut = 0]`, `zn` | bits / exact isZero gadgets | sound (`Proc.entry_row`) |
| `scpV3` | `d = b(x − y) + (1 − b)(y − x − 1)`, 29 bits | contract needs `x, y < 2^29` | sound under the stated precondition (`cmp_sound`) |

Cost of the fixes: `sdsV3` +58, `sscV3` +46, `schV3` +8 ⇒ `W_eq` 822 → **934** (kernel-checked
`weqSched_g1`). Tests after the fixes: `SchedFullTest` **600/600 vectors, 0 violations, 28/28
mutants** (1,234 s).

## 11. Open items (in priority order)

1. M3 views: codec, process structure (key
   block, headers, rounds); link layer per §6 (memory consistency instance, operand bounds of
   §10, `process_rounds` hypotheses, `core_compose`); `schedCore_sound`.
2. M4: completeness of the six tables (honest generators exist and pass on 600 vectors).
3. Amendment requests (§4): distinct layout ids; A8 request bound.
4. Cuts (§3).
