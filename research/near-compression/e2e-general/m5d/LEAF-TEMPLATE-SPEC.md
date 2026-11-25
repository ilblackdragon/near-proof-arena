# M5d leaf-template spec: INIT and FINAL as tree leaves (lane G → lane D)

Status 2026-11-21, M5d-T1. What lane D needs to wrap the M5d templates as tree leaves
(`build_seg_leaf`, plan §5.0.1.4) and what the wrap may rely on. Labels as in the README.
Everything below is built and measured on T1 unless marked **[S]** (proposal / not built).

## 1. Common to both templates

| item | value |
|---|---|
| stack | lane B's M5a prover family (`prover/`): unified SWIRL, BabyBear Ext12, SHA-384 MMCS 42-B digests, stacked WHIR, `NEARPROOF_{DIGEST_BYTES=42,COSET_LEAF=1,TSTAR=1}` |
| parameters | seg-v1: `l_skip 2`, `log_blowup 1`, `k 4`, `k_first 1`, final poly `2^7`, list decoding `m = 16`, query PoW 24, 268-bit target, LogUp `2^30` / message length `2^6`, `max_constraint_degree 9` (the chip); `n_stack` = least of 14/18/22 with `2^(n+2) ≥` max height and `w_stack ≤ 24`; `w_stack = ⌈cells / 2^(n+2)⌉ + 4` (≥ 8). T1 FINAL: `n_stack 18`, `w_stack 8` |
| AIRs | the Lean export (`m5d-tool air-final` / `air-init`) in table order, then `Sha512Air4`, `TableAir4` (native chip v4, buses 100–103) |
| cached / public tables | **none**. No tape, no cached root: nothing of the template is checked natively except its public values |
| public values | every table carries the first `num_pub` global public values (the interpreter's convention); the template's public-value vector is §3 / §4 |
| digests | `bdigest m = SHA-384(m)[0..42)` (lane E `Bnd.bdigest`, U-10); as public values: 14 limbs, limb `i` = `65536·d[3i] + 256·d[3i+1] + d[3i+2]` |
| I3 (review-D7) | INIT's input boundary is "before the chunk" (no `B_in`); FINAL's output phase is `done`. Neither accepts a `done` input |

## 2. The statement digest (`ctx` = `claimDigest`) — lane E's canonical encoding [K]

Plan §3.4.1 / `spec/lean/v3/NearSpecV3/E2E/StmtEnc.lean`: `S = PublicStmt.encode s =
stmtPre ‖ u32 0 ‖ stmtPost` (the claim-v3 encoding with an empty section B;
`assemble ci secB secC = stmtPre ‖ encList BlockRec.encode secB ‖ stmtPost`), and
`claimDigest s = bdigest S`. Both M5d templates hash exactly these bytes in-circuit; on T1
`|S| = 1,007 B` and both proofs expose `claimDigest = bb5aad11…9f2f01` (= lane E's `t1_claimDigest`).
V_d computes it from the public statement alone.

## 3. INIT template

**Proves:** `claimDigest = bdigest(pre ‖ u32 0 ‖ post)` (§2) and
`ctxRoot = bdigest(0x00 ‖ u32 ℓ_B ‖ u32 |cb| ‖ cb ‖ wb)` with `cb = pre ‖ blocks ‖ post`,
`ℓ_B = |blocks|`, over the same witness bytes (`CLM` rows feed both SHA-384 messages; the statement
message skips the `blocks` rows and takes the four zero bytes in their place). `blocks`, `wb` stay
private.

**Lane E target:** `SegSoundInit` (meaning `MInit` = the whole intake step). INIT supplies `B_0`'s
digests; the step itself is lane B's INTAKE, so the `.init` leaf is INIT ∘ INTAKE.

**Public values (44):** `[claimDigest (14 limbs), ctxRoot (14 limbs), prev_state_root (16 pairs)]`.
**G-5:** `u32 ℓ_B` and `u32 |cb|` are **big-endian** (`ViewE.u32 = beN 4`, integrator decision I2b-1;
G-2 – G-4 hashed them little-endian: T1 `ctxRoot` `0e790a2c…` → `60498d85…`).

**Leaf (lane D):** check `pv[0..14) = ctx`; `h(B_0) = bdigest(BndRec.encode R)` with `R` lane E's
`init` record (`claimDigest = bdigest []`, phase 0, counters 0, `stRoot = stD(.none)`,
`outD(.none) = (bdigest [], [], bdigest [], bdigest [0])`, `vmAcc = bdigest []`, `wasm = none`)
and `ctxRoot = pv[14..28)` (`Leaf.InitWrap`); expose `s_in = [0, h(B_0)]`. On T1 this is lane I's
`h(c0)` (`T1G5.t1_init_c0`). `B_1` (= `c1`: `ctxD(.intake I)`, `R_0`) is lane B's INTAKE half of the
joined leaf.

**Obligation on INTAKE (lane B) [S]:** INTAKE opens `ctxRoot` (re-hashing `cb ‖ wb`) and must check
that `decodeClaimE cb`'s block list spans exactly `ℓ_B` bytes after `pre`. Without it a prover could
choose `blocks` so that the claim decoder consumes part of `post` as blocks and re-reads section C
from other bytes; with it, `cb = assemble ci secB secC` for the decoded `secB`
(`WitnessExtraction`). (Alternatively INIT and INTAKE share one leaf and the check is a bus.)

**Shape:** `CLM` height = `|cb| + |wb|` rounded up (T1: 14,734 → 2^14), `S384` ≈ `(|cb| + |wb|)/128`
(T1: 124 compressions → 2^7). Height classes by witness size.

## 4. FINAL template (class F1)

**Input point.** Lane E's `FINAL` step is `fin I out → done H o` = `finK` then `tailNew`. The template
covers `tailNew` + `headerOk` and starts at `t = (root, congestion, outgoing)`, the result of `finK`
(main post-state root check, implicit transitions, outgoing reassignment — state work: lane B
M5a FINAL root + M5c). Its input is the record

| `FinIn` bytes | field | source |
|---|---|---|
| 0..32 | post-`finK` state root | `t.1` |
| 32..75 | congestion `0 ‖ u128 delayed ‖ u128 buffered ‖ u64 receipt_bytes ‖ u16 allowed_shard` | `t.2.1` |
| 75..83 | `u64` gas used | `out.gasUsed` |
| 83..99 | `u128` balance burnt | `out.balanceBurnt` |
| 99..107 | `u64` gas limit | `I.slotB2.gasLimit` |
| 107 | proposed split (`0` = none; class F1) | `I.proposed` |
| 108..112 | `u32` proposals count (`0`; class F1) | `out.proposals` |
| 112..116 | `u32` bandwidth requests count (`0`; class F1) | `out.bwRequests` |
| 116..158 | outcome accumulator `chainD(leaf)` over `OutD1.leaf` | `out.outcomes` |
| 158..200 | outgoing accumulator `chainD(u64 routedShard ‖ u32 ℓ ‖ Rcpt.encode r)` | `t.2.2` |
| 200..242 | transaction accumulator (`bdigest []`; class F1: none) | `I.w.newTxs` |
| 242..246 | `u32` shard count (6, class) | `I.L.shardIds` |
| 246..294 | shard ids, `u64` each, layout order | `I.L.shardIds` |

`chainD` is lane E's (`View.chainD`): `acc_0 = bdigest []`, `acc_{i+1} = bdigest(acc_i ‖ item_i)`.
`finInDigest = bdigest(0x46 ‖ FinIn)`.

**Proves (in-circuit):** `claimDigest` of the statement (the template hashes the whole `stmtBytes`
and reads the header from its fixed window); the outcome root (`merklize` of the leaves the
accumulator opens to), the outgoing receipts root (`merklizeBorsh` over the layout's shards of
`sha256(u64 s ‖ encodeRcpts(receipts routed to s))`), the body `u32 0 ‖ encodeRcpts outgoing`, its
Reed–Solomon parts and `encoded_merkle_root`, `encoded_length = |body|`, `tx_root = zeroHash`; and
the 13 `headerOk` comparisons against the header (`Lean: final_template_sound`).

**Public values (30):** `[claimDigest (14), finInDigest (14), n, L]` (`n` = header
`encoded_length`, `L = ⌈n/d⌉`; both are constrained to the hashed header, so they need no check).

**Leaf (lane D):** check `pv[0..14) = ctx`; tie `pv[14..28)` to the input boundary (below); expose
`s_out = [done, h(B_out)]`. The wrap's `B_N.phase = done` then implies FinalOut (rec. 1(b)(ii)).

**Joining the input — G-2 [K] for the logic, [S] for the tables:** option (a) below, stated and
proved in `lean/FinalM5d/Split.lean`: lane B's part `FinalBPart` (input digest opens to
`fin I out`, `I.d2 = none`, `FinReach I out t` — `finK` reaches `t`, `finK_bind` — and the `FinIn`
bus carries `fi` with `FinInOK fi I out t`) and lane G's part `FinalGPart` (output digest opens to
`done I.H o` with `tailNew … t = .ok o` and `headerOk I.H o`) give lane E's `SegSoundFinal`
(`segSoundFinal_join`). The `FinIn` bus carries the §4 table's bytes `(j, FinIn[j])`, `j < FI_LEN`,
`FI_LEN = 246 + 8·NS` (G-2: the layout is per shard-count class); today the M5d template hashes
them to `finInDigest` (public values 14..28), which the joint leaf replaces by the bus.
Same for INIT: `InitGPart` + lane B's `InitBPart` (joined by the `CLM` bytes) ⇒ `SegSoundInit`.

Earlier options:
* (a) *one segment*: lane B's FINAL rows (post-state root) + M5c's implicit transitions + M5d's
  tables in one trace, `FinIn` carried on a bus instead of `finInDigest` (no digest, no new
  configuration). **Recommended.**
* (b) *a cut at `finK`*: a boundary with `phase = fin2` and `stRoot = finInDigest`; this needs lane E
  to split `CM`'s `fin → done` step at `finK` (a new configuration `fin2 I out t`).

**`B_out` (G-2, re-encoded in G-5) [M].** `done H o` in lane E's view `ViewE.viewE`:
`ctxRoot = ctxDE(.header H) = bdigest(3 ‖ Ser.enc H)`, `outcomeAcc = outDE(.done o).1 =
bdigest(Ser.enc o)`, `outRcptAcc = []`, `proposalsAcc = bdigest []`, `bwAcc = bdigest [2]`,
`stRoot = stD .none`, `vmAcc = bdigest []`, `wasm = none`, `claimDigest = bdigest []`, and the M12
clear fields `gasUsed = o.gasUsed`, `balanceBurnt = o.balanceBurnt`, every other counter `0`.
`Ser ChunkInner` / `Ser Outputs` are `ViewSer`'s fixed-width serialisers (G-5, lanes E ∧ G): a
natural is `natW n = 0 ‖ beN 16 n` (`n < 2^128`; `1 ‖ vnat n` otherwise), a 32-byte string
`hashW b = 0 ‖ b` (`1 ‖ Ser.enc b` otherwise), lists and options `Ser.enc` (`[0]` when empty);
field order = the structure's. On class F1 the template sends `3 ‖ Ser.enc H` (389 B, from the
statement window: `Fin.hdrBytes`) and `Ser.enc o` (304 B, from the `FinIn` cells and the computed
roots: `Fin.outBytes`) through `S384`; on T1 both equal Lean's `BOut.encHdr` / `encOut` byte for
byte (the trace generator asserts it against `m5d-tool dump`).

**Public values (82, G-5):** `[claimDigest (14), finInDigest (14), n, L, ctxD(.header H) (14),
outD(.done o).1 (14), gasUsed (8 bytes, big-endian), balanceBurnt (16 bytes, big-endian)]` —
digests as 14 limbs of 3 bytes big-endian; the two counters one byte per value, in the boundary
record's `natC 8` / `natC 16` byte order, constrained (`Fin.clearConstraints`) to the `FinIn` gas /
balance cells reversed, which `eqGu` / `eqBb` equate to the header's `prev_gas_used` /
`prev_balance_burnt` (Lean `Leaf.fin_clear`).

**Leaf (lane D), G-5:** check `pv[0..14) = ctx`; `h(B_out) = bdigest(BndRec.encode R)` with `R` the
view's `done` constants with `ctxRoot = pv[30..44)`, `outcomeAcc = pv[44..58)`,
`gasUsed = beToNat pv[58..66)`, `balanceBurnt = beToNat pv[66..82)` (`Leaf.FinWrap`); expose
`s_out = [4, h(B_out)]`. On T1 this is lane I's `h(c10)` (`t1/chain.py`, Lean `T1G5.t1_final_c10`).

**Class F1 pins** (fixed in the AIR; another class = another template in `{C_t}`): V5 header, no
proposals / bandwidth requests / split / transactions, 6 shards with `u16` ids, `|chain_id| = 14`,
`(d, t) = (5, 16)`, `n < 2^24`, `≤ 2^16` receipts per shard. General classes add: the transaction
segments (same `SEG`/`BODY` path, destination the tx hash + tx accumulator), proposal and
bandwidth-request encodings (variable header layout), the split option, other `(d, t)`.

**Heights on T1** (lane D's pinned `(log)` vector would be a class cap ≥ these): `SHA 12, S384 5,
RNG 8, STMT 10, FIN 2, BODY 10, SEG 3, RS 8, PART 5, SHD 3, OUTL 2, MRK 5, SHA512 12, SHA512T 7`.
Every table but `SHA` and the chip accepts padding rows (activity is a prefix, the last row is
inactive), so padding to class caps is a generator change; the `SHA` table and the chip pad by
their generators (`sha256gen`, `s384::trace`) — a minimum-height option is needed there.

**Lane E target:** `SegSoundFinal` (meaning `MFinal`: finished engine → `done`, `finK` included);
M5d proves the `tailNew` + `headerOk` part (`final_template_sound`), `finK` comes from lane B / M5c.

**Measured (T1, canonical `S`):** FINAL 992,188 B, 268.2-bit, prove 30.3 s, verify 83 ms; INIT
790,307 B, prove 56.1 s, verify 58 ms.

## 5. The join buses (G-2) — fixed here for lanes B / D / E

Bus ids are in the joint leaf's numbering = lane G's `FinalM5d.Dsl` numbering (buses `0..18` as
in `Dsl.lean`, then the G-2 ones). A joint leaf is one AIR: lane B's tables are added with their
buses renumbered past these, except the two join buses below, which both sides use as written.

| bus | id | messages | sender → receiver |
|---|---|---|---|
| `FINB` (`FinIn`) | **23** | `(j, byte)`, `j < FI_LEN = 246 + 8·NS`, multiplicity 1 each | lane B's IF FINAL (bytes `0..32`: `post_state_root`, from `TCH(n, post)`; lane B's `pack2` limb `t` = bytes `2t, 2t+1`, big-endian) and M5c (congestion, …) → lane G's `FIN` (`fi[j]`), in place of `finInDigest`. In the standalone FINAL template these bytes are hashed to `finInDigest` (public values 14..28) instead. |
| `PSR` | **22** | `(j, byte)`, `j < 32`, multiplicity 1 each | lane G's `INI` (the main chunk slot's `prev_state_root`, read from the claim) → lane B's IF INTAKE (`WSB`'s public limbs 0–15). In the standalone INIT template the bytes are public values 28..44 (16 big-endian byte pairs = lane B's `pack2`). |
| `CB`, `LB`, `SLOT` | 19, 20, 21 | INIT-internal (claim byte reads, section-B span, slots) | — |
| `LAY`, `IX` | 23, 24 | INIT-internal (G-4: layout walk start + shard id + main index; main index to `BLK`) | — (INIT numbering; `FINB` = 23 is FINAL's) |

## 6. INIT: the claim's section B (G-2) and the main-slot selection (G-4) [M]

INIT now decodes the framing of section B (`BLK`, `Init.lean`): the block vector
`encList BlockRec.encode secB` is walked field group by field group (count, per block
`u8 ‖ hash ‖ u32-bytes ‖ u32-bytes ‖ u32 m`, per slot `u32-bytes ‖ u64`), contiguous, from `|pre|`
to exactly `|pre| + ℓ_B` — the `ℓ_B` hashed into `ctxRoot`. So `ℓ_B` is the span `decodeClaimE`'s
`pVec dBlock` consumes, the obligation of §3 (no longer lane B's). Every slot is on `SLOT
(block, slot, inner start, inner length)`; `INI` takes the main slot `(b2i, mainIdx)` (private,
from the checker's walk) and reads its `prev_state_root` (inner bytes 33..65, `inner length ≥ 65`).
**G-4: the selection is in-circuit** (closes the G-2 open item; `psr_slot` is now rejected by the
AIR). On the INIT class **E1** — the claim's epoch table has one record (`INI` reads `#epochs = 1`
at `|pre| + ℓ_B + 4`; every `d3` claim, 19,007 / 19,007) — the checker's `walkSegment` reduces to
the D2 rule: `mainShard = H.shardId`, `mainLayout` = that record's layout `L`, and `b2i` is the
first block whose slot `L.index H.shardId` is new (`height_included = height`)
(`WalkSel.walk_single` / `main_slot_single` [K]). The AIR mirrors it:

* `INI` reads the claim's shard id (`u64` at chunk inner + 145; the inner starts at
  `P_CH + 40 + |chain_id|`, `P_CH = 60` = `|borshBytes claimTag| + |borshBytes statementIdV3| + 4`,
  `WalkSel.p_ch_eq` [K]) and sends `(|pre| + ℓ_B + 56, shard limbs, mainIdx)` on `LAY` (bus 23) and
  `mainIdx` on `IX` (bus 24).
* `LAY` (new table, pinned 2^8) walks the layout prefix `u8 tag ∈ {2,3} ‖ boundary_accounts ‖
  shard_ids ‖ id_to_index` (`Layout.decodeLayout`, V2 and V3 alike) and selects the **first**
  `id_to_index` pair whose key is the shard id (`Layout.index` = `find?`); its value is `mainIdx`
  (`InitSel.lay_first_pair` [K]).
* `BLK` reads every block's height (`inner_lite[0..8]`) and every slot's `height_included`; a slot
  row is a target iff its index is `mainIdx`, new iff the three limbs of the two `u64` are equal;
  `sel` = the first new target slot (row order = block order), exactly one (`InitSel.blk_main_slot`
  [K]). The `SLOT` message of the selected row is what `INI` receives, so `(b2i, mainIdx, sst, sln)`
  and the `prev_state_root` read are forced.

Out of class E1 (an epoch table with ≥ 2 records: a segment that crosses an epoch, possibly a
layout boundary with resharding transitions) the INIT AIR rejects; that class needs the general
walk (layout per block, `parentV3` at a boundary) — not built. Completeness bounds of E1: layout
index `< 256`, lengths `< 2^24` (as G-2), the layout walk ≤ 255 rows (≤ 126 shards). Still [S]: the
row ↔ decoded-structure correspondence of these walks (as for `BLK` since G-2).
