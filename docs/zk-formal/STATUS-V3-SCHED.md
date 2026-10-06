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
| M2 | tables | six `Table` values (§3), kernel-checked budget (`W_eq` = 781 at g = 1 after cuts B, D and the source map), honest generators for all six (`Gen/*`), constraint evaluator + bus-balance tests on the 600 vectors, mutants (§8) | **done** |
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

**Kernel-checked** (`Sched/BudgetCheck.lean`: `report_g1`, `weqSched_g1`), g = 1, after cuts B and D (§12):

| table | file | width | interactions | degree | `W_eq` | maxLog |
|---|---|---:|---:|---:|---:|---:|
| `schV3` codec + link | `Tables/Codec.lean` | 91 | 16 | 4 | 243 | 22 |
| `ssdV3` scan + distribute | `Tables/ScanDist.lean` (`Scan.lean`, `Dist.lean`) | 119 | 10 | 4 | 223 | 22 |
| `sprV3` process | `Tables/Proc.lean` | 64 | 11 | 4 | 176 | 22 |
| `smmV3` memory | `Tables/Mem.lean` | 18 | 4 | 4 | 74 | 22 |
| `scpV3` comparator | `Tables/Cmp.lean` | 33 | 1 | 4 | 65 | 22 |
| **total** | | 325 | 42 | | **781** | |

History: 810 (first layout) → 814 (29-bit comparator) → 822 (`SPLEN`) → 934 (range fixes, §10) →
788 (cut B) → 761 (cut D) → **781** (duplicate-id source map, +20).

(At g = 3 the grouped aux constraints have degree 8; g = 1 is the better setting for these
tables.) With lane v3-chacha's 654 the scheduler costs ≈ 1,435 `W_eq` ≈ 1.24 MB of proof (at
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
| `Codec.kinds`, `bytes`, gadget iffs, carries, **`codec_block`**, **`codec_post`**, **`codec_pre`**, **`codec_post_encode`**, **`codec_pre_encode`**, `a0_split`, `alw_walk`, **`codec_link`**, **`codec_rec_msgs`**, **`codec_trailer`**, `codec_first` | `View/Codec*.lean` (7 files, 2,422 lines) | an instance block: 5 header rows, `24·N` record rows, 32 + 32 trailer rows. The post bytes are `State.encode ⟨postLinks, digest⟩`, where ids are the received `SDL` bytes and allowances are `afin`. The pre bytes (when present) are `State.encode ⟨preLinks, hash⟩`. The link pass at a record end is `a1 = bigR ? MA : min(apR + fair, MA)` and `a2 = a1 − al·base`, given the comparator bit. It also states every message value (INIT/FIN/SDG/SA0/SCMP/SHA/forwarding). No missing constraint was found. Statements assume `height ≤ 2^22`; unbounded cells are stated mod P. |
| `ProcRow.*` (kinds, gadgets, carries, transitions), **`proc_keys`**, **`round_shape`**, `round_after`, **`hdr_msgs`**, **`ent_msgs`**, **`proc_rounds`** | `View/Proc*.lean` (5 files, 1,129 lines) | an instance: a 16-row key block (limbs = public key records), then rounds `i < m` with headers at `hdrAt i`. `T_0 = T0`, `T_{i+1} = T_i + Lr_i`; `kst` chains from 0 through `kend`; `Kq/zq` are the previous round's; round validity. Gives every shuffle/push/INC/SOP/CMP message value on headers and entries. No missing constraint. Results are mod P where cells are unbounded (`z = zq + 1` among them). |
| `MemOwn`, `sopSent`, **`mem_seg_unique`**, **`mem_seg_sorted`**, `mem_seg_time`, **`mem_chained`**, **`mem_reads_sim`**, **`mem_ops_eq_sent`**, `mem_ops_perm`, `mem_init_eq_sent`, `Cmp.cmp_row_le`, `cmp_sound_le` | `Link/MemBus.lean`, `Link/MemSeg.lean` (740 lines) | memory inside a v2 AIR. Given `InitOnce` (each address INITed at most once over all senders) and every memory time `< 2^29`: one segment per address, times strictly increasing within it, `Chained memOps memInit`. So each op reads the simulated state given `Frame`/`StepOk` (`mem_reads_sim`). The ops the memory table receives are exactly the op-1/2 `SOP` messages sent by all tables. Open obligations for the composition: `InitOnce` from the codec/distribute views, and the time bound. |
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

## 11. Claim conditions for the two proposed amendments (nearcore 2.13.4, `44f7ae6c`)

**A8 status (lead decision): a relation-level conjunct** `a8` of `RelD0a` (commit `61191270`;
`ChunkValidationV0a.a8`, `checkD0a`, `relD0a_iff`/`relD0a_relD0`/`relD0a_mono` proved; `prepClaim`
checks it natively, and so does its `@[csimp]` fast copy). Independent implementations (Python checker, Rust
oracle on nearcore's chunk headers), mutant `c.dup_bw_request`, full D0a difftest (seed 4243, 9 × 120):
11,616 cases, **0 disagreements**, A8 on honest witnesses 0 / 4,597, A8 mutants 845/845
out_of_domain in Lean and Python (STATUS-V3-SPEC §1.1a; commits `8971775f`, `fd75c9f0`). The scheduler uses it **only** in completeness / height bounds (stated parametric in
`B0` and A8).
**Soundness does not need it**:
* `process_rounds`, `core_compose`, the views and `cmp_sound` have no request-count hypothesis;
* table heights are bounded by `HoldsP` itself (`maxLog`);
* the request count only matters for whether an honest trace fits (M4).

**A8: at most one request per target shard and sender.**
* *Construction:* `runtime/runtime/src/congestion_control.rs:512-521`, `generate_bandwidth_requests`.
  It runs `for shard_id in shard_layout.shard_ids() { if let Some(request) =
  self.generate_bandwidth_request(shard_id, …)? { requests.push(request) } }`. So there is at most one
  request per shard id of the layout, `to_shard = shard_id`
  (`core/primitives/src/bandwidth_scheduler.rs:84-126`, `make_from_receipt_sizes`).
* *Validation:* `chain/chain/src/validate.rs:280-298`, `validate_bandwidth_requests`. A chunk header's
  requests must equal the ones the previous chunk's application stored in its chunk extra
  (`InvalidBandwidthRequests` otherwise).
* *The block's map:* `chain/chain/src/chain_update.rs:508`, `block.block_bandwidth_requests()`, has one
  entry per chunk slot.
* *Proposed condition:* in each block, each slot's `BandwidthRequests` list has at most `n` entries.
  Equivalently, its `to_shard` values are distinct (claim-decidable). Every honest claim satisfies it,
  because the requests are the validated outputs of the loop above.

**Decision (program lead): no distinct-ids amendment; the AIR follows the spec on every layout.**
* **Spec side (done).** `Spec/CanonDup.allow0_src` (proved): for any layout, the spec's `allow0` of
  a canonical previous state is `a (srcOf ids l)`. Here `srcOf ids l` is the last record `k` with
  `tgt ids k = l`, and `tgt` uses the spec's first-index `indexOf`. `core_compose` no longer
  assumes `ids.Nodup` (commit `04a4ad9a`).
* **AIR side (done, commit below).** The codec reads `a0` through the claim-only source map.
  * The public per-link record gains `(src_lo, src_hi, hasSrc)`, plus a per-record `use` bit; these
    reach the codec with `SDG`.
  * Record `k` sends `A0 (τ, k, ap, big)` with multiplicity `use(k)`.
  * Record `l` receives `A0 (τ, src(l), …)` at its byte-2 row with multiplicity `hasSrc(l)`, where
    the comparator runs.
  * Cost: ≈ +16 `W_eq` (two interactions) plus a few columns.
* **Faithfulness finding (pinned spec vs nearcore), unreachable on real layouts.** On a layout with
  duplicate shard ids:
  * nearcore's `get_shard_index` reads `id_to_index_map`, built by inserting every `shard_ids` entry
    in order, so the last index wins (`core/primitives/src/shard_layout/v2.rs:199-215`,
    `v3.rs:205-216`);
  * the pinned spec's `indexOf` returns the first index.

  So the spec and nearcore disagree on the scheduler's link indices. No real layout has duplicate
  ids. The AIR proves the spec relation.

**Distinct layout shard ids: weaker evidence.**
* No explicit assertion:
  * `ShardLayoutV2::new` (`core/primitives/src/shard_layout/v2.rs:199-215`) inserts `shard_ids`
    into the `BTreeMap`s `id_to_index_map` / `index_to_id_map` without a distinctness assertion.
  * `ShardLayoutV3::new` (`shard_layout/v3.rs:205-216`) asserts only the boundary order and the split map.
* *The split-map case does force distinctness.* With a split map, `validate_and_derive_shard_parent_map`
  (`v2.rs:21-47`) asserts `shard_ids.sorted() == shards_parent_map.keys()`. The right side is a
  `BTreeMap`'s keys, so this forces distinct ids.
* *Duplicates break nearcore itself.* `get_shard_index` reads `id_to_index_map`, and a duplicate id
  makes it disagree with `shard_ids` (last insert wins). The spec's `indexOf` takes the first index.
  The spec's own `Scheduler.decodeShardLayoutV2` rejects such a layout (`idToIndex ≠ byId`).
  `prepD0`'s `decodeLayout` does not check the maps.
* *Proposed condition:* `c.layout`: the layout's `shard_ids` are pairwise distinct (claim-decidable).
  This is true of every layout nearcore actually builds: the mainnet `ShardLayout::v2` configurations,
  and splits, where the assertion above applies.
* *Alternative if the lead rejects it:* handle duplicates in-AIR with a source map
  `allow0[l] = record src(l)`. This is one more bus in the codec/link pass, ≈ +16 `W_eq`.

## 12. Width cuts: evaluation (program lead, after design §13)

`W_eq` = width + 8·interactions + 24 per table (degree 4). Current total: 934.

| cut | saving | re-proof cost | decision |
|---|---:|---|---|
| **A. one table for scan + process + memory + distribute row kinds.** Columns are multiplexed (width ≈ max over kinds + message windows ≈ 125 instead of 291). The public receives `SPAR/SRAW/SPUBB-key/SSHD/SLINK` move to one padded public bus with an aligned window (5 → 1). `SPUSH` sends 2 → 1, `SOP` sends 5 → 3, `SCMP` sends 4 → 2 (aligned windows). Interactions 29 → ≈ 20. Quotient 4 → 1. | **≈ 310** (934 → ≈ 625) | **medium.** All four proved views (memory, process entry, distribute, scan; ≈ 1.8 k lines) need edits: renamed columns resolve by name, but constraint-membership proofs change; ungated value/booleanity constraints get kind gates; the padding/first/last-row lemmas change because the table becomes sections (`row_pad`, `row_first`, `seg_start`, scan's `row_next_lt`/`row_pad`). Generators and both tests must be rebuilt for the merged layout. Rows ≈ 3.6 M ≤ 2^22 under A7 + A8 (tight). | needs the lead's go-ahead (re-proof is not small) |
| **B. scan + distribute only.** These are the two widest; public receives 4 → 1, `SOP` sends 2 → 1. | ≈ 140 | small–medium: the distribute view (membership only) and the scan view's boundary lemmas | candidate if A is declined |
| C. process + memory only | ≈ 48 | small | below the threshold |
| D. codec: overlay the 32-column digest register on record-only columns; receive `DIGEST` on the first hash row | 32 | none (no codec view yet) | below the threshold; cheap, can go with the codec view |
| E. per-byte SHA digest output (`DBYTE`) | 32 | SHA lane change | external |
| F. range-check bits via the comparator | — | — | not possible: a comparator-only bound (`x < 2^29`) is too weak for exact divisions, and the extra comparator rows would exceed 2^22 |

Range checks are kept in every variant.

## 13. Open items (in priority order)

1. **Done:** cut B (`ssdV3`, commit `26829f12`: −146; views re-proved; SchedFullTest 600/600, 51/51
   mutants; SchedTablesTest 600/600, 44/44) and cut D (commit `b056a51d`: −27; SchedFullTest 600/600,
   51/51). Cut A is on hold. Codec source map done (+20; `SA0` bus 62, `SDG` carries
   `(src, hasSrc, use)`, `Render.srcFields`). **Both tests rerun on the final tables (781):**
   SchedFullTest 600/600 vectors, 0 violations, all buses balanced, 51/51 mutants (2,033 s);
   SchedTablesTest 600/600, 0 violations, 0 unbalanced messages, 44/44 mutants (2,729 s). Duplicate-id layouts are tested:
   `SchedFullTest`'s dup mode sets shard id 1 := shard id 0 on every vector with `n ≥ 2`, which
   gives a non-identity source map. The codec's new state equals `runCore`'s (spec first-index
   semantics), with every constraint and bus checked. The event model and run data read `allow0`
   through `srcArr` (commit `e64a64b0`). Result: 600/600 vectors and **525/525 duplicate-id
   layouts** (all with a non-identity source map), 0 violations, 51/51 mutants (3,896 s).
2. M3 views: codec, process structure (key block, headers, rounds); link layer per §6 (memory
   consistency instance, operand bounds of §10, `process_rounds` hypotheses, `core_compose`);
   `schedCore_sound`.
3. M4: completeness of the six tables (honest generators exist and pass on 600 vectors).
4. A8 (§11) as a completeness-only hypothesis; the distinct-ids amendment is dropped (source map, §11). The codec source map is pending.
5. Cuts D/E.
