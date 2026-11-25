# E2E milestone M5d-T1: the FINAL and INIT templates for general chunks (lane G)

Plan: `docs/zk-formal/E2E-GENERAL-CHUNK-PLAN.md` §1.1 ("outputs and roots"), §3.2, §3.4, §5.0.1
(blocker 7, item 1(b)(ii)), §5.7 (status). Leaf-template spec for lane D:
[`LEAF-TEMPLATE-SPEC.md`](LEAF-TEMPLATE-SPEC.md). Date 2026-11-21. Labels: **[M]** measured here,
**[K]** kernel-checked Lean (std axioms), **[S]** stated / design only.

## G-5 (2026-11-25): view encodings, the two counters, INIT / FINAL as joined leaves in lane E's forms

Log `docs/logs/e2e-laneG-g5-2026-11-25.md`. Plan §3.5 (discharge table), §5.3. Leaf spec §3, §4.
Reproduce: `TARGET_DIR=… ./g5.sh OUT` (prove both, `m8-import`, both batteries). `S`, `claimDigest`
and the checker are unchanged (`nearspec-v3-check-successor` does not import `E2E/`).

**Circuit changes [M].**
* **FINAL, the M12 clear fields** (`Final.lean` `Fin.clearConstraints`): public values grow from 58
  to **82**: 58..66 = `o.gasUsed`, 66..82 = `o.balanceBurnt`, one byte per value, big-endian (the
  boundary record's `natC 8` / `natC 16` order), constrained to the `FinIn` gas / balance cells
  reversed — the cells `eqGu` / `eqBb` equate to the header's `prev_gas_used` /
  `prev_balance_burnt`, i.e. exactly what `headerOk` checks. Every other clear field at `done` is a
  view constant (`clearE`).
* **FINAL, lane E's view encodings** (coordinator decision I2b, lanes E ∧ G): `B_out`'s two
  commitments are now `ctxDE (.header H) = bdigest (3 ‖ Ser.enc H)` and `outDE (.done o).1 =
  bdigest (Ser.enc o)`. `ViewSer.lean` (spec/lean/v3, view data only) replaces `Ser ChunkInner` /
  `Ser Outputs` by fixed-width prefix-free forms (`natW n = 0 ‖ beN 16 n` for `n < 2^128`, else
  `1 ‖ vnat n`; `hashW b = 0 ‖ b` for `|b| = 32`, else `1 ‖ Ser.enc b`; lists / options `Ser.enc`;
  `natW_pf`, `hashW_pf`, `ciW_inj`, `outW_inj`; `ViewE` unchanged but for a doc note). FINAL sends
  `Fin.hdrBytes` (389 B from the statement window) and `Fin.outBytes` (304 B from the `FinIn` cells
  and the computed roots) through `S384`; on T1 they equal Lean's `BOut.encHdr H` / `encOut o` byte
  for byte (`tracegen.py` asserts it against `m5d-tool dump`). G-2's own encodings
  (`0x04 ‖ chunk_inner`, `0x05 ‖ encOutputsF1`) are removed.
* **INIT, big-endian `u32`** (I2b-1): `INI` sends `u32 ℓ_B`, `u32 |cb|` big-endian (`b4be`), so
  `ctxRoot = ViewE.ctxDE (.raw cb wb)`; T1 `ctxRoot` `0e790a2c…` → **`60498d85…`** (= lane I's
  `ctx_raw_be`).

**T1 [M]** (lane D base configuration, grinding 24, 8 threads, `heavy` 12 G, lane D's tree prover
gone):

| | FINAL (`F1`) | INIT (`INIT-14`) |
|---|---|---|
| proof | **486,168 B** (G-3: 485,862) | **356,405 B** (G-4: 355,691) |
| prove / verify | 22.9 s / 28 ms | 21.6 s / 11 ms |
| peak RSS | 6.84 GB | 6.25 GB |
| soundness | 268.2 bits | 268.2 bits |
| cells / SHA-512 compressions | 5,505,888 / 33 | 1,714,696 / 124 |
| public values | 82 | 44 |

Native verify + statement check OK, lane D `fs-count` OK, **`m8-import` OK** for both. Saved:
**`/data/illia/nearproof-deps/e2e-m5d/g5/tmpl/{init,final}/`** (`TMPL.proof`, `TMPL.vk.json`,
`INFO.json`; FINAL `fc311780…0364c1` / `63bc9683…d391f4`, INIT `3c26d067…b380df` /
`f7787bd7…0c6a4f`), in-repo `results/g5/`. **Lane D:** re-import both (FINAL now has 82 public
values on `FIN`, still the first 30 on `BODY`, `SEG`, `RS`, `PART`; INIT unchanged in layout).

**Against lane I's chain (`t1/chain.py`, I-2b) [M]:** the leaves' assembled boundaries are the
chain's records digest for digest: INIT's `B_0` (view constants + public `ctxRoot`) = **`h(c0)`
`ac01792e…5109`**; FINAL's `B_out` (view constants + public `ctxD (.header H)`, `outD (.done o).1`,
`gasUsed`, `balanceBurnt`) = **`h(c10)` `bd9c8344…a6df`**. `chain.py` now fills `c10`'s
`ctxRoot` / `outcomeAcc` (two placeholders removed; Lean-evaluated by `m5d-tool dump`, input fields
`ctx_header` / `out_done`) and its `leaf_table` checks both G-5 leaves (all checks ✓, INIT in / FINAL
out equal). `c1` (`ctxD (.intake I)`, `R_0`) and `c9` are lane B's halves of the joined leaves.

**Batteries with the prover [M]:** **FINAL 38 / 38** rejected (`logs/G5-T1-final-mutants.txt`: the
35 of G-3 + **`pub_gu`**, **`pub_bb`** (a counter byte changed: `clearConstraints`), **`gu_le`** (the
counter in `FinIn`'s little-endian order); `fin_gas` / `fin_bal` now also move the public counters
and are rejected by `eqGu` / `eqBb`), all by the AIR. **INIT 13 / 13** (`logs/G5-T1-init-mutants.txt`,
as G-4: 10 by the AIR, `pre_byte` / `blk_byte` / `wit_byte` by the statement check).

**Lean [K]** (std axioms, `Audit.lean`; `lake build` of `m5d/lean` and `spec/lean/v3` green):
* **`InitBus`** (G-4's open INIT items, on the deployed `initAirS` = `initAir` + lane B's `IF384`
  chip stub; `precheck_holds_init`): **`init_blk_act0`** (`BLK`'s row 0 is active: `INI` sends `IX`
  once from its single active row, only `BLK` receives it, with `kn`, which is `0` off row 0),
  **`init_ix_blk`** (`BLK.ix = INI.mi`), **`init_lay_head`** (`LAY`'s head row receives `INI`'s
  start, shard limbs and `mi`), **`init_slot`** (`INI`'s `SLOT` is the unique selected `BLK` row's),
  **`init_main_index`** (G-4's `blk_main_slot` / `lay_first_pair` with these premises discharged:
  the first new slot at `L.index shard` = `INI.mi` = the first layout pair's value, and `INI`'s slot
  is that row's).
* **`Leaf`** — the joined leaves in lane E's canonical forms. `TreeM8.split_sound`'s `EngHalf` must
  yield the meaning alone, which neither half of INIT / FINAL can (INIT's rows do not know that
  `CM.step (init cb wb)` succeeds; FINAL's rows do not reach `t`); **`join_sound_abs`** /
  **`join_sound_relC`** compose an input half (`Pre ctx x q` for the bus value `q`) and an output
  half. Lane D's wrapper (`InitWrap`, `FinWrap`: the records from the public values), the view laws
  (`InitView`, `FinView`, `EncRaw`, `EncDone` — all proved for `ViewE.viewE`: `initView_viewE`,
  `finView_viewE`, `encRaw_viewE`, `encDone_viewE`).
  * INIT: **`init_g_half`** (lane G's input half: `b = lbOf V (init cb wb)` and the context link,
    from the wrapper, the laws and the named `InitDig`), **`init_sound8`** (`SegSoundInit8` with lane
    B's INTAKE output half `InitBOut`), `init_soundRel8C` (`TmplSoundRel8C .init`).
  * FINAL: **`fin_clear`** (from `Holds finalAirS`: the public counters' big-endian values are
    `u64c o.gasUsed`, `u128c o.balanceBurnt` of the template's `o`), **`fin_g_half`** (lane G's
    output half: from the rows and any input meeting lane B's `FinPre`, `b' = lbOf V (done I.H o)`
    with `tailNew … = .ok o`, along `MFinal`, with `FinalOutPub`), **`final_soundRel8C`**
    (`TmplSoundRel8C .final` from lane B's input half and lane G's rows).
* **`T1G5`** (non-vacuity on T1, `decide +kernel`, SHA-384 in the kernel): `t1_init_c0` (INIT's
  wrapper holds with `b = (0, h(c0))`), `t1_final_c10` (FINAL's with `b' = (4, h(c10))`),
  `t1_same_ctx`, `t1_fin_dig` (the leaf's `ctxD (.header H)` / `outD (.done o).1` are
  `BOut.ctxHeaderD (hdrOf hb)` / `outDoneD (outputsOf …)` of T1's row: `FinDig`'s digest parts on
  T1), `t1_clear`, `k0_viewE` / `k10_viewE` (the wrapper constants are `viewE`'s, with lane B's
  `stD .none` at the chain's placeholder `0^42`).

**Named premises left (owner):**
* lane G: `InitDig` (INIT's two SHA-384 messages are `S` and `rawPre lB cb wb` for the `CLM`
  stream's bytes, `lB cb = ℓ_B`), `FinDig` (FINAL's statement / header / output messages), `Computed`
  (the `OUTL`/`SHD`/`RS`/`PART`/`MRK` roots) — the SHA-384 message contract (padding, digest bytes,
  functional senders; per-row parts proved in G-2: `s384_chain`, `s384_out_byte`) and the row ↔
  decoded-structure correspondence of the walks;
* lane B: `InitBOut` (INTAKE: `CM.step (init cb wb) = .ok c`, `b' = lbOf V c`, i.e. `c1`), `FinPre`
  (FINAL half: the opening of `B_in` = `c9` reaches `fin I out`, `FinReach`, the `FinIn` bus, class
  F1) and **the header link** `decodeChunkInner window = .ok I.H` (the window the `FIN` row reads is
  `I`'s header: a chain invariant from INIT, not visible to a relative FINAL leaf alone);
* lane D: the joint leaf AIRs (`JoinAir.joint`) and the wrapper; lane B: publish `stD .none`.

## G-4 (2026-11-25): the main-slot selection in-circuit — `psr_slot` rejected by the AIR

Log `docs/logs/e2e-laneG-g4-2026-11-25.md`. Plan §5.3. Leaf spec §6. Reproduce: `./g4.sh OUT`.
Nothing under `spec/` changed; `S`, `claimDigest`, the checker and INIT's 44 public values are
unchanged (T1's public values are bit-identical to G-3's). Soundness fix adopted.

**The change (`Init.lean`).** INIT class **E1**: the claim's epoch table has one record (`INI`
reads `#epochs = 1`; 19,007 / 19,007 `d3` claims). There the checker's `walkSegment` is the D2
rule (`WalkSel.walk_single` [K], below), and the AIR now computes it:
* `INI` reads the claim's shard id (`u64` at chunk inner + 145, inner at `60 + 40 + |chain_id|`),
  sends `(|pre| + ℓ_B + 56, shard limbs, mainIdx)` on `LAY` (bus 23) and `mainIdx` on `IX` (24).
* New table **`LAY`** (43 columns, pinned 2^8): walks the layout prefix `tag ‖ boundary_accounts ‖
  shard_ids ‖ id_to_index` and selects the **first** pair with key = shard id (`Layout.index`);
  its value byte is `mainIdx`.
* **`BLK`** (+19 columns): reads each block's height and each slot's `height_included`; `tgt` = slot
  index is `mainIdx`, `eq` = target and new (3 limbs equal, inverse witness otherwise),
  `sel = eq · (1 − g)` (`g`: selected earlier), `g + sel = 1` at the last active row: exactly one
  slot selected, the first new one at `mainIdx` in block order. Its `SLOT` message fixes `INI`'s
  `(b2i, mainIdx, sst, sln)` and hence the `prev_state_root` read.
* `CLM`'s `rd` may now read `pre` / `post` bytes (never witness bytes). Templates `INIT-14..18`
  re-pinned (`LAY` 2^8; T1 at `INIT-14`: 1,714,696 cells).

**T1 [M]** (`INIT-14`, lane D base configuration, grinding 24, 8 threads, `heavy` 10 G):

| | G-3 | G-4 |
|---|---|---|
| proof | 350,435 B | **355,691 B** |
| prove / verify | 19.0 s / 10 ms | **23.8 s / 18 ms** |
| peak RSS | 6.24 GB | **6.27 GB** |
| soundness | 268.2 bits | 268.2 bits |
| tables | 7 AIRs | 8 AIRs (`… INI, LAY, SHA512, SHA512T`) |

Native verify + statement check OK, lane D `fs-count` OK, **`m8-import` OK**. Saved (lane D's M8 leaf
format): **`/data/illia/nearproof-deps/e2e-m5d/g4/tmpl/init/`** (`TMPL.proof` `6a39bcac…a3e2b`,
`TMPL.vk.json` `235aa151…b7c45`, `INFO.json`); prover copy `…/g4/t1i/proof-init/`. In-repo
`results/g4/`. **Lane D:** the INIT `TemplateSpec`'s AIR list gains `LAY` (index 5; public values
still on `INI` only) and the vk changed — re-import from the G-4 path.

**Battery with the prover [M]** (`logs/G4-T1-init-mutants.txt`): **13 / 13 rejected**. `psr_slot`
is now rejected by the **AIR** (BLK `sel = eq·(1−g)` fails on the honest slot row, plus `LAY`/`IX`
imbalance). New: `psr_ix` (a fully consistent BLK/INI walk for another main index: rejected by
`LAY`'s `hit · (y₈ − ix)`), `sel_two` (a second slot selected), `sel_none` (no slot selected) —
both rejected by the `sel` constraint. As before, `pre_byte`, `blk_byte`, `wit_byte` (other chunks,
honestly re-hashed) prove and are rejected by the statement check; the other 6 by the AIR.

**Lean [K]** (std axioms, `Audit.lean`; `lake build` 423 jobs green):
* `WalkSel.walk_single`: `c.epochs = [ep]`, `decodeLayout ep.shardLayout = .ok L`,
  `walkSegment c blks ae s0 = .ok wk` ⇒ `wk.mainShard = s0`, `wk.mainLayout = ep.shardLayout`, block
  `wk.b2i` is new at `L.index s0` and every earlier block is not (proof through the checker's own
  `for` loop: `pre` before the first new block, `forIn_inv` after). `main_slot_single`: the same
  for the intake's `mainIdx` / `slotB2`. `p_ch_eq`: `P_CH = 60` from the claim tags.
* `InitSel.blk_main_slot` / `init_blk_main_slot` (from `Holds initAir`): exactly one `BLK` row has
  `sel = 1`, it satisfies `BlkNew` (slot row, index `ix`, limbs equal), no earlier row does, `ix`
  is row 0's. `lay_first_pair` / `init_lay_first_pair`: exactly one `LAY` hit, the first pair whose
  key limbs are `sh`, value byte = `ix`, bytes 1..7 zero, `sh`/`ix` = the head row's.
  Generic: `first_sel`, `last_active`.
* Premise / open [S]: `BLK` row 0 active (bus-level, its count row receives from `INI`); the bus
  glue `ix(BLK) = mi = ix(LAY)` (`IX`, `LAY` messages) and the row ↔ decoded-structure / limbs ↔
  `u64` correspondence of the walks (as for `BLK`'s framing since G-2).

**Out of scope / reported:** a claim whose epoch table has ≥ 2 records (a segment crossing an epoch,
possibly a resharding boundary) is out of class E1 and rejected by the INIT AIR (completeness only);
no such claim in the `d3` corpus. The general walk (layout per block, `parentV3`) is not built.

## G-3 (2026-11-25): T1's INIT and FINAL re-proved on the current AIRs, saved in lane D's leaf format

Log `docs/logs/e2e-laneG-g3-2026-11-25.md`. Plan §5.3. Reproduce: `./g3.sh OUT` (prove both,
`m8-import`, both batteries). Nothing under `spec/` and no AIR changed in G-3.

**What was proved [M]** — the G-2 AIRs as on main (`m5d-tool` export of this tree's Lean: INIT
with `BLK` / `SLOT` `sel` bit / `ℓ_B` check / `PSR` public values; FINAL with the `B_out` digests,
`FINB`/`PSR` bus ids fixed per leaf spec §5), lane D's base configuration (grinding 24), pinned
templates `F1` / `INIT-14`, 8 threads, `heavy` slice at `HEAVY_MEM=18G`, host load ≈ 15:

| T1 | FINAL (`F1`) | INIT (`INIT-14`) |
|---|---|---|
| tables / cells | 14 AIRs, 5,505,888 cells, 32 SHA-512 compressions (26 + the 2 `B_out` messages) | 7 AIRs, 1,698,776 cells, 124 compressions |
| proof | **485,862 B** (G-2 before `B_out`: 480,428) | **350,435 B** (G-2 before `BLK`: 346,723) |
| soundness | 268.2 bits (`query` bound) | 268.2 bits |
| prove / verify | **21.8 s** / 26 ms | **19.0 s** / 10 ms |
| peak RSS (prover) | **6.86 GB** | **6.24 GB** |
| public values | 58: `claimDigest` (0..14), `finInDigest` (14..28), `n` = 990, `L` = 198, `ctxD(.header H)` (30..44) = `a1d33e43…`, `outD(.done o).1` (44..58) = `ef7d1e4e…` | 44: `claimDigest` (0..14), `ctxRoot = ctxD(.raw cb wb)` (14..28) = `0e790a2c…`, main slot `prev_state_root` (28..44, `pack2`) |
| checks | native verifier + statement check OK; lane D `fs-count` OK; `m8-import` OK | same |

Cross-checks: both `claimDigest` = `bb5aad11…9f2f01` (lane E's `t1_claimDigest`); FINAL's
30..58 = the dump's Lean `ctxHeaderD` / `outDoneD`; INIT's 28..44 = **lane B's STATE_IF leaf's
`WSB` public limbs 0..15 exactly** (lane D's `results/zk/m8/t1real/tmpl/state_if/INFO.json`), i.e.
the standalone `PSR` link to lane B's intake holds on T1.

**Saved (lane D's M8 leaf format)** — `/data/illia/nearproof-deps/e2e-m5d/g3/tmpl/{init,final}/`
(`TMPL.proof`, `TMPL.vk.json`, `INFO.json`, written by lane D's own `m8-import`, which verifies
natively); the prover's copies `…/g3/t1{i,f}/proof-{init,final}/STATE.{proof,vk.json}` +
`statement.json`. In-repo: `results/g3/{init,final}/{INFO,statement}.json`, `results/g3/SHA256SUMS`.

| file | sha256 |
|---|---|
| `final/TMPL.proof` (485,862 B) | `08f282a5…1c8dcd33` |
| `final/TMPL.vk.json` | `eb0e7920…63a84a22` |
| `init/TMPL.proof` (350,435 B) | `e88e84a2…35a99ac410` |
| `init/TMPL.vk.json` | `982d4a91…379b0bf060` |

For lane D's `TemplateSpec` (from `INFO.json`): INIT carries its 44 public values on `INI` only;
FINAL carries 58 on `FIN` and the first 30 on `BODY`, `SEG`, `RS`, `PART` (the interpreter's
"first `num_pub`" convention: one equality group, prefix form as lane B's WSB/WSX). No cached
commitments. `ctx` = `CtxMode::Src(pv 0..14)` on both.

**Mutant batteries with the prover [M]** (`logs/G3-T1-{final,init}-mutants.txt`; each mutant: the
AIR precheck, and if it passes, the full prover + native verifier + statement check):
* **FINAL 35 / 35 rejected**, all by the AIR precheck (the 32 of M5d-T1 + `bout_od`, `pub_hdr`,
  `pub_out`). Same verdicts as G-2's `pycheck` run.
* **INIT 10 / 10 rejected**: 6 by the AIR (`clm_kind`, `clm_byte`, `ini_lb`, `pub_ctx`, `lbshift`,
  `pub_psr`); 4 prove and verify and are rejected by the **statement check** only: `pre_byte`,
  `blk_byte`, `wit_byte` (honestly re-hashed changes of the claim / section B / witness: a
  different chunk, so a different `claimDigest` / `ctxRoot` — the correct place to reject them),
  and **`psr_slot`** (another slot's `prev_state_root`): the open slot-selection obligation
  (`walkSegment`, leaf spec §6) — the AIR does not fix which slot is the main one.

**`BndRec` gap (lane E, `E2E/Boundary.lean` + `View.lean`) — what the leaves expose vs. what
`bdigest (V.bnd x).encode` needs.** Not resolved by a format here: lane E's `ViewImpl` is still a
parameter (no concrete `clear`, `stD`, `outD`, `vmD`, `ctxD` in `spec/`), lane G's `ctxD` / `outD`
encodings are proposals (`BOut.lean`, leaf spec §3/§4).

| leaf boundary | `Templates` config | exposed today | missing |
|---|---|---|---|
| INIT `B_in` = `B_0` | `init cb wb` (phase 0) | `claimDigest`, `ctxRoot` (lane G's proposed `ctxD(.raw cb wb)`) | only view constants: `stD .none`, `outD .none` (4 accumulators), `vmD []`, `V.clear (init …)` (presumably 0) — lane E must fix them and adopt `ctxD(.raw)` |
| INIT `B_out` | `eng I start` (phase 1) | nothing (INIT is `InitGPart` only) | `ctxD(.intake I)`, `stD(stOfK (κ I) start)`, `outD(.eng …)`: lane B's INTAKE (`InitBPart`). The standalone INIT can only end at `B_0`; `SegSoundInit` needs INIT ∘ INTAKE in one leaf (joined by the `CLM` bytes + `PSR` bus 22), or lane E's chain treats INIT as `→ B_0` and INTAKE as `B_0 → eng I start`. `prev_state_root` (28..44) is a join value, not a `BndRec` field |
| FINAL `B_in` | `eng I ⟨done out⟩` / `fin I out` (phase 1/2) | `finInDigest = bdigest(0x46 ‖ FinIn)` — **not a `BndRec` field** | `ctxD(.intake I)`, `stD(…)`, `outD(.eng a)`, clear fields: lane B's FINAL + M5c `finK` (`FinalBPart`, `FINB` bus 23). Shape mismatch to resolve with lane E: `FinIn`'s outgoing accumulator is one `chainD` over `u64 shard ‖ u32 ℓ ‖ enc r`, `BndRec.outRcptAcc` is a `List` of digests; `FinIn`'s outcome accumulator (116..158) is `chainD` over `OutD1.leaf` — equal to `B_in.outcomeAcc` only if lane E's `outD(.eng)` is defined that way |
| FINAL `B_out` | `done H o` (phase 4) | `claimDigest`, `ctxD(.header H)`, `outD(.done o).1` (proposals) | `outRcptAcc`, `proposalsAcc`, `bwAcc` of `outD(.done o)` (proposed `[]`, `bdigest []`, `bdigest []`), `stD .none`, `vmD []`, and **`V.clear (done H o)`**: lane I's plan carries `gasUsed`, `gasBurnt`, `compute`, `receiptIdx` into `done`; FINAL has `gasUsed` / `balanceBurnt` only inside `FinIn`, and `gasBurnt`, `compute`, `receiptIdx`, `rPrepaid/rBurnt/rUsed`, `blockIdx`, `actionIdx`, `t` not at all. Either lane E sets the clear fields of `done` to constants (outputs live in `o`), or they must come from `B_in` (pass-through cells), which needs the joint leaf |

So the two proofs drop into the M8 tree as **template leaves with lane D's prototype records**
(as the stubs: INIT's 44 / FINAL's 58 public values as record cells), not yet as `BndRec` digests.

## G-2 (2026-11-21): whole-AIR Lean, the leaf joins, `B_out`, pinned shapes, class census

Log `docs/logs/e2e-laneG-g2-2026-11-21.md`. Plan §5.3.

### Item 1 — from `Holds` of the whole AIR [K]

The package now requires lane B's `StateM5a` (read-only: `Bus`, `ChipStub`, `Sha512If`).
**`Whole.finalAirS`** = `finalAir` + lane B's chip stub `chipStubOn B_IF384`: the AIR the prover
runs (`Holds finalAir` alone is unsatisfiable: `S384` receives on `IF384` and no Lean table sends
there). **`S384Chip.precheck_holds_final`**: a precheck-accepted trace (every bus but `IF384`
balanced, the native chip's sends a permutation of the `IF384` receives) extends, Lean tables
unchanged, to `Holds finalAirS` whose stub sends are exactly the chip's — so every theorem below
is about the deployed relation and the chip premise is lane B's `Sha512IfContract` on the chip's
own sends.

| module | result |
|---|---|
| `BusMem` | generic: `mem_busList` (bus list ↔ an occurrence), `recv_sent` / `sent_recv` under `Holds` |
| `Whole` | `onlyIn` / `occ_in` (who sends / receives a bus, `decide +kernel`), field ↔ natural helpers |
| `HbWhole` | **`hb_bytes`**: `HbBytes` (was a premise) from `Holds finalAirS` — `FIN` `HB` ← `STMT` (`h = 1 ⇒ act = 1`) → `SB` → `S384` data flag (`⇒ act = 1`, monotone flags) → `R8`/`S2`/`S5` → `RNG` (`v = Σ 2^i β_i`); `fin_row0_act`; **`final_template_sound_holds`** (FINAL with `HbBytes` discharged) |
| `RsRow` | (was `lean-wip`, over the heartbeat budget; now 0.8 s) `rs_parity_bit_holds`: parity bit = parity of the selected data bits, `q` bytes from `R8` |
| `RsByte` | **`rs_parity_byte_holds`**: an `RS` row's parity byte `i` = the spec's `parityPart` byte `⊕_j mulRow(M[d+i][j])[d_j]` (with `coeff_linear`, `mat_mem`) |
| `ShaWhole` | **`sha_msg`**: SHA-256 message identification — a received `SHA_DIGEST (id, L, dg)` whose `(id, i)` senders are functional is `sha256` of their bytes (`sha_digest_recv` from lane L5's closed contract; `|msg| ≤ 2^28`) |
| `MrkWalk` | **`walkRoot_eq`**: the `MRK` level walk (hash / carry / terminal / zero rows) is nearcore `merklize` (record level) |
| `S384Rec` | `sha384_of_blocks`: `sha384 m` = the first 48 bytes of `foldl compress IV384` over blocks concatenating to `pad m` |
| `S384Chip` | **`s384_comp`** (an active `S384` row is a chip compression, via lane B's `comp_sound`), `s384_step` / `s384_iv`, **`s384_chain`**: over a message, the compression input of row `r0 + n` is the fold of `compress` over the rows' blocks from IV384 |
| `Split` | item 3, below |
| `BOut` | item 2, below |
| `Cls.All` | item 4: `f1_eq` — the generated F1 class AIR is `finalAir` (`rfl`) |

**Still open for `Computed`** (named, in order of size): the functional-sender facts per SHA-256
consumer (`PART`/`RS` ids `PID0 + p`, `SHD` `SHM0/SHL0 + q`, `MRK` `MID0 + g`: disjoint id ranges
and row counters) — then `sha_msg` gives each digest; the `MRK` table's rows ⇒ `walkLevel` per
level (the `NODE` bus is functional on `(tree, level, index)`: one `TSTART` per tree, counters);
`BODY`/`SEG` ⇒ `encodeRcpts` and the shard routing; `S384`'s padding (the rows' blocks are `pad` of
the received bytes) and digest-byte extraction, which with `s384_chain` + `sha384_of_blocks` gives
SHA-384 of every `SD` message (then the accumulator openings, modulo `bdigest` collisions).

### Item 2 — `B_out`, pinned shapes, lane D's format [M]

* **Prover** (`prover/`): ported to lane B's B-T1 prover — the verifier's backend (frozen
  `pq-e2e-d9` `stark-backend-unified` + `plonky3-ext12`), `Sha384CpuEngine`, **lane D's base
  configuration** (list decoding m = 64, `k_first 2`, `domain_odd_factor 15`, LogUp message length 7,
  `zk = 0`) with **query grinding 24** (not 32) and the template's `(n_stack, log_blowup, w_stack)`;
  `prove … OUT` saves `STATE.proof`, `STATE.vk.json` (SavedVk), `statement.json`; **lane D's driver
  verifies them** (`nearproof-chunk-e2e fs-count VK PROOF 0`, `run.sh` runs it).
* **Pinned heights** (`templates/*.json`, `census.py`): every table — the SHA-256 table and the
  SHA-512 chip included (minimum-height options: `sha_cells_pinned`, `gen_main(comps, 1 << pin)`,
  zero rows) — padded to its class pin; FINAL classes nested by chip height `F1` (≤ 2^13, 120 / 133
  F1 cases), `F1-M`, `F1-L` (all 133); INIT classes `INIT-14 … INIT-18` by chip height (875 / 875 of a
  partial census). `run.sh` picks the smallest fitting template (exit 4 = overflow).
* **`B_out`** (`Final.lean` `Fin.boutInteractions`, `BOut.lean`): `FIN` sends `0x04 ‖ chunk_inner`
  and `0x05 ‖ encOutputsF1 o` (252 B, from the row's `FinIn` / root / header-length cells) through
  `S384`; public values 30..44 = `ctxD(.header H)` = `BOut.ctxHeaderD H`, 44..58 = the first
  component of `outD(.done o)` = `BOut.outDoneD o`. The dump emits **Lean's own** `ctxHeaderD`,
  `outDoneD`, `encOutputsF1` on the case and `tracegen.py` asserts the circuit's bytes equal them
  (T1: `ctxHeaderD = a1d33e43…92c7`, `outDoneD = ef7d1e4e…6c72`). The leaf assembles `h(B_out)` from
  these, `claimDigest` and the view's constants for `done` (§5 of the leaf spec).

| T1 | before (M5d-T1, seg-v1, natural) | G-2 (template, base config) |
|---|---|---|
| FINAL (before `B_out`) | 992,188 B | **480,428 B** at `F1` (27.6 s / 31 ms, 6.9 GB, 268.2-bit), fs-count OK |
| INIT (before the section-B walk) | 790,307 B | **346,723 B** at `INIT-14` (38.8 s / 16 ms, 6.2 GB), fs-count OK |
| FINAL with `B_out` / INIT with `BLK` | | not re-proved (slice saturated); pycheck OK on the honest traces, `run.sh … prove` reproduces |

**INIT decodes section B (G-2, coordinator request)** — `BLK` framing walk, slot bus, the main
slot's `prev_state_root` exposed (public values 28..44; bus `PSR` = 22 in the `.init` join); see
leaf spec §6 (the slot *selection* `(b2i, mainIdx)` = the checker's `walkSegment` is open: mutant
`psr_slot` is accepted by the AIR).

**Mutants (T1, at the templates, on the G-2 AIRs with `B_out` / `BLK`):** the prover batteries
could not run: the shared `zkbuild.slice` (the `heavy` wrapper's cgroup) sat at its 40 GB
`memory.high` from other lanes' jobs and every prover in it stalled. So the batteries ran under
**`pycheck.py`** (pure Python: every exported constraint on every row, multiplicity bits, every bus
balanced as a multiset except the chip's `IF384`, then the statement check; `pymutants.sh`):
**FINAL 35 / 35 rejected** (`logs/G2-T1-final-pymutants.txt`: the 32 of M5d-T1 + `bout_od`,
`pub_hdr`, `pub_out`), **INIT 10 / 10 rejected** (`logs/G2-T1-init-pymutants.txt`: + `lbshift`
(walk end differs from `|pre| + ℓ_B`), `psr_slot`, `pub_psr`), honest traces OK. `psr_slot` (another
slot's `prev_state_root`) is rejected **only by the statement check**; the AIR accepts it (the slot
selection is the open `walkSegment` obligation, leaf spec §6). Under the prover (before the AIR
changes) `hdr_psr` was rejected (precheck + native verifier). Re-run with the prover:
`LEAN=0 ./run.sh CASE OUT mutants` (+ `TEMPLATE=init`).

### Item 3 — the FINAL / INIT leaves as joins [K] (`Split.lean`; lane E's M11i split was not on main)

* `finK_bind` (any driver, any gas cap): the checker's `finK … k = finK … pure >>= k` — `FINAL`'s
  first part splits at `t = (root, congestion, outgoing)` with no checker change; `FinReach I out t`
  (`∀ k, finK … k = k t`), `finReach_of`, and `fin_split` (every successful non-genesis `FINAL` step
  factors through such a `t`: the split is not vacuous).
* **FINAL**: lane B's `FinalBPart` (input digest opens to `fin I out`, `I.d2 = none`,
  `FinReach I out t`, the `FinIn` bus carries `fi` with `FinInOK fi I out t`) + lane G's
  `FinalGPart` (from the bus value: output digest opens to `done I.H o`, `tailNew … t = .ok o`,
  `headerOk I.H o`) ⇒ **`segSoundFinal_join`**: lane E's `SegSoundFinal`; `final_join_headerOk`
  also gives FinalOut on the opened `done`.
* **INIT**: `InitGPart` (input digest opens to `init cb wb` for the bytes on the `CLM` stream) +
  lane B's `InitBPart` (for those bytes, `CM.step (init cb wb) = .ok c`, output digest opens to `c`)
  ⇒ **`segSoundInit_join`**: `SegSoundInit`.
* What lane G's tables give toward `FinalGPart` today: `final_template_sound_holds` (`headerOk` of
  the decoded public header and `tailNew`'s `o`), modulo `ClassF1` / `Computed` and the `B_out`
  digest; `H = I.H` is the statement link (`cm_done_header`: the `done` header is the claim's own
  decoded `chunk_inner`, the window `FIN` reads from the statement whose digest is `ctx`).

### Item 4 — FINAL class census [M] (`shapes.py`, `logs/G2-shapes.{txt,jsonl}`)

7,477 `d3` cases (`d3c7`–`d3c10`, every 4th + the first 3,192), the Lean checker's FINAL per case:
**F1 is 3.7 %**; transactions are in **81 %**; `(d, t)` ∈ {(1, 3) 22 %, (2, 8) 25 %, (5, 16) 23 %,
(33, 100) 27 %}, not tied to the shard count (4 shards 37 %, 5 shards 32 %, 6 shards 31 %);
proposals 3.3 %, bandwidth requests 0.65 %, proposed split 0, header V5 and `|chain_id| = 14`
everywhere; 1 % dump timeouts (600 s). Without transactions / proposals / bandwidth requests every
`(NS, d, t)` combination together is ≈ 18 %; adding transactions reaches ≈ 96 %.
**`gen_class.py NS D T`** generates the class-`(NS, d, t)` FINAL AIR from `Final.lean` (the AIR is
parametric in exactly these; `FI_LEN = 246 + 8·NS`), `m5d-tool air-final-cls NS D T AIR NAMES`
exports it (9 classes generated), and `Cls.f1_eq` checks that the generated F1 is `finalAir`.
Next by frequency: transactions (the `SEG`/`BODY` path with the tx destination + tx accumulator +
`tx_root` merklize), then proposals, then bandwidth requests.

## What this is (M5d-T1)

* **FINAL** (class `F1`): every chunk-header output lane E's `headerOk` compares (13 comparisons)
  is computed in-circuit from the post-`finK` record `FinIn` and compared, byte by byte, with the
  chunk header inside the public statement, whose SHA-384 digest is the public `claimDigest`
  (recommendation 1(b)(ii): FinalOut is carried by the template, the wrap only checks `done`).
* **INIT**: the init boundary's chunk-dependent digests from the claim and witness bytes:
  `claimDigest` (the statement) and `ctxRoot` (the intake context `ctxD (.raw cb wb)`).

Both AIRs are `ZkFormal.Air` values in Lean (`lean/FinalM5d/{Final,Init}.lean`), exported by
`m5d-tool` and interpreted unchanged by the prover (`prover/`, a copy of lane B's M5a prover with
the table list read from the export; same backend, BabyBear Ext12, SHA-384 MMCS 42-B digests,
stacked WHIR, seg-v1 parameters, the native SHA-512 chip v4 on bus 103). Traces come from the Lean
checker's own run (`m5d-tool dump`: lane E's `CM.step` from `init claim witness` to `fin I out`,
then the checker's `finK` and `tailNew` verbatim).

**Targets in lane E's T1 template system** (`spec/lean/v3/NearSpecV3/E2E/Templates.lean`, main
`1461c97f6`): `SegSoundInit` (meaning `MInit`: the whole `CM` intake step `init cb wb → CM.step`)
and `SegSoundFinal` (meaning `MFinal`: a `CM` run from a finished engine configuration to `done`,
including `finK`). **What M5d-T1 covers of them:** INIT proves the init boundary's two
chunk-dependent digests (`claimDigest` bound to the canonical `S` of `StmtEnc`, and the
`ctxD (.raw cb wb)` commitment); the intake step itself (claim / witness decoding, trie
authentication) is lane B's INTAKE, so `SegSoundInit` needs INIT ∘ INTAKE in one leaf. FINAL proves
`tailNew` + `headerOk` from the post-`finK` point (`final_template_sound`); `finK` (main root check,
implicit transitions, outgoing reassignment) is lane B's FINAL root / M5c, so `SegSoundFinal` needs
them joined (leaf spec §4, option (a)). `TmplComplete` for the M5d part: the T1 proofs plus
`T1Check`.

## Commands

```
./build.sh                                     # lake build m5d-tool; cargo build (≤ 8 threads)
./run.sh CASE_DIR OUT_DIR prove                # FINAL: dump, export, tracegen, prove + verify
./run.sh CASE_DIR OUT_DIR mutants              # FINAL mutant battery (tracegen.py MUTANTS)
lean/.lake/build/bin/m5d-tool air-init A.json N.json  # INIT AIR; tracegen.py DUMP N.json OUT
python3 gen_t1data.py DUMP lean/FinalM5d/T1Data.lean  # the Lean non-vacuity data
( cd lean && lake build )                      # every lemma + FinalM5d/Audit.lean
```
`CASE_DIR` for T1: `/data/illia/nearproof-deps/corpora/d3c8/d3/02-h10196-s3`.

## The FINAL AIR (class F1)

| table | rows (T1) | role |
|---|---|---|
| `SHA` | 2^12 (133 blocks) | `ZkFormal.Sha.Table` (contract `sha_digest_contract_closed`): every spec SHA-256 |
| `S384` | 2^5 (26 blocks) | **new**: SHA-384 of byte messages over the native compression chip — receives `(id, pos, byte)`, sends `(id, len, digest[48])`, FIPS padding in-circuit, bytes ↔ 21-bit limbs with split lookups |
| `RNG` | 256 | `R8 (v)`, `S2 (v, v mod 4, v/4)`, `S5 (v, v mod 32, v/32)` lookups |
| `STMT` | 1,007 | lane E's canonical statement `S = stmtPre ‖ u32 0 ‖ stmtPost` (plan §3.4.1, `StmtEnc`) → SHA-384 `claimDigest`; first 424 bytes → `FIN` |
| `FIN` | 1 | header window (fixed layout pins, the 13 comparisons), `FinIn` → `finInDigest`, roots, public values |
| `BODY` | 990 = d·L | the chunk body `u32 0 ‖ u32 n_R ‖ enc r_1 ‖ …` (+ zero padding to `d·L`): Reed–Solomon data cells, per-shard and accumulator-chain message bytes |
| `SEG` | 7 | segments: the two count prefixes, one per outgoing receipt (shard one-hot, length, chain step `acc_{i+1} = bdigest(acc_i ‖ u64 shard ‖ u32 ℓ ‖ enc r)`), padding |
| `RS` | L = 198 | Reed–Solomon parity, **GF(2)-linear**: data bits `x`, per parity bit `Σ A·x = r + 2q` with `r` a bit and `q` an `R8` lookup; part bytes → SHA-256 |
| `PART` | t = 16 | part leaves `sha256(u32 L ‖ part)` |
| `SHD` | 6 | shard leaves `sha256(sha256(u64 s ‖ u32 n_s ‖ receipts routed to s))` (`merklizeBorsh`) |
| `OUTL` | 2 | outcome leaves: accumulator chain `bdigest(acc ‖ leaf)` and Merkle leaves |
| `MRK` | 25 | nearcore `merklize` as a level walk (odd node carried up, `n ∈ {0,1}` terminal rows) for the outcome, shard and part trees |

Public values: `claimDigest` (14 limbs of 3 bytes), `finInDigest` (14), `n` (body length), `L`.
Class `F1` pins: header V5, no proposals / bandwidth requests / proposed split / transactions,
6 shards with `u16` ids, `|chain_id| = 14`, Reed–Solomon `(d, t) = (5, 16)`.

## Results on T1 [M]

| | FINAL | INIT |
|---|---|---|
| trace | 2,689,104 cells (SHA 2.23 M, chip 0.34 M, RS 55.8 k); 26 SHA-512 compressions | 1,616,828 cells (CLM 2^14, chip 2^14); 124 compressions |
| proof | **992,188 B** (whir 689,044, relations 274,548, gkr 25,544) | **790,307 B** (whir 681,396) |
| soundness (calculator) | 268.2 bits | 268.2 bits |
| prove / verify | 30.3 s / 83 ms (8 threads, 0.90 GB peak) | 56.1 s / 58 ms (0.81 GB) |
| outputs | outcome root `49be525c…`, outgoing root `647e6f58…`, encoded root `5a648fbd…`, length 990, state root `1db48e38…`, gas 1,577,739,758,301 — each = the Lean checker's (`dump.checks`, tracegen asserts) and = the header's | `claimDigest` = `bb5aad11…9f2f01` = lane E's `t1_claimDigest`; `ctxRoot` = `0e790a2c…f745f5fe` |

The dump's self-checks: every output recomputed the way the AIR does it (merklize of the outcome
leaves, per-shard `u64 s ‖ encodeRcpts` double hash, `buildMatrix` parity, parts root) equals the
checker's `tailNew` output, and `headerOk I.H o` holds.

**FINAL mutants: 32/32 rejected** (`logs/T1-final-mutants.txt`):
* statement (one byte of each compared header field, the statement re-hashed honestly so only the
  AIR can catch it): `hdr_psr, hdr_por, hdr_emr, hdr_el, hdr_gu, hdr_gl, hdr_bb, hdr_orr, hdr_txr,
  hdr_props, hdr_cong, hdr_bw, hdr_split` — all 13 comparisons;
* boundary (`FinIn`, re-hashed honestly): `fin_root, fin_cong, fin_gas, fin_bal, fin_gl`;
* data (recomputed honestly downstream, so the computed root differs from the header's):
  `leaf, outcome_drop, rcpt_byte, rcpt_shard, rcpt_drop, rcpt_swap`;
* row tampers: `body_byte, rs_par, mrk_node, stmt_byte, fin_ro, s384_pad`;
* public values: `pub_claim, pub_n`.

## Reed–Solomon in-circuit cost (measured on T1, projected) [M][E]

Per body byte, cells (unpadded): `BODY` 17; `RS` `(8d + 16(t−d) + 2)/d` = 43.6 at (5, 16), 40.5 at
mainnet-like (33, 100); **part hashing `(t/d)·144.5`** (a SHA-256 block is 17 rows × 544 = 9,248
cells per 64 B) = 462 at (5, 16), 438 at (33, 100); receipts also pay their shard-message SHA-256
(144.5) and the accumulator chain's SHA-384 (S384 3.5 + chip 83). On T1 the part messages are
64 of 133 SHA-256 blocks (48 %); the parity arithmetic itself is 55.8 k cells (2 % of the trace).
**The cost of `encoded_merkle_root` is the spec's SHA-256 over `t/d ≈ 3×` the body, not the GF
arithmetic**: ≈ 500 cells per body byte, i.e. ≈ 0.5 G cells for a 1 MB body [E]. Levers: none on
the hash (spec); the part tree's `t − 1` nodes are fixed per chunk (≈ 2·t blocks).

## Lean [K] (`lean/FinalM5d/`, std axioms only — `Audit.lean`)

* `Decode.decode_F1`: the class-F1 byte layout `encF1` decodes (the spec's `decodeChunkInner`) to
  `hdrF1` with the slices as fields.
* `HeaderLink.row_headerOk`: `RowOK hb fi ro rs rsh n` (the `FIN` row's relations, as naturals) ⇒
  `decodeChunkInner (win hb) = .ok (hdrOf hb)` ∧ **`headerOk (hdrOf hb) (outputsOf fi ro rs rsh n)`**.
* `FinRow.rowOK_of_constraints` / `fin_headerOk`: on any row of any trace where the exported
  `Fin.table`'s constraints vanish over BabyBear with `act = 1` and byte-valued statement cells
  (`HbBytes`, a named premise: `S384`'s lookups range-check them), `RowOK` holds of the cells — so
  the row gives `headerOk`.
* `Tail.tailNew_outputsOf` / **`final_template_sound`**: with `FinInOK` (the `FinIn` cells are the
  projection of the post-`finK` point `(I, out, t)`), `ClassF1` and `Computed` (the received roots
  are the spec's outcome root, outgoing root and `encodedMerkleRoot` of the body), the checker's own
  `tailNew afDriver I out t = .ok o` and `headerOk H o` for the decoded public header `H`.
* `RsCoeff.coeff_linear` (kernel, 93 s): for every parity coefficient of the class matrix, every byte
  `x` and bit `k`, bit `k` of the spec's `gfMul c x` is the GF(2) sum the `RS` row constrains.
* `T1Check`: **non-vacuity on T1** — T1's actual row values satisfy `RowOK` (`decide +kernel`), the
  window is T1's public `chunk_inner`, `outputsOf` = the checker's outputs, `headerOk` holds.

Open (named premises, not yet theorems; `lean-wip/RsRow.lean` has the RS row's parity-bit lemma,
not yet within the heartbeat budget): `Computed` from `Holds` of the whole AIR (the `MRK` walk ⇒
`merkleRoot`, `RS` rows ⇒ `parityPart`, `BODY`/`SEG` ⇒ `encodeRcpts`, `SHD` ⇒ `outgoingRoot`, the
SHA-256 contract, the `S384` table ⇒ SHA-384 under lane B's `Sha512IfContract`); `HbBytes`;
`FinInOK` is the upstream segment's obligation (leaf spec §2).
