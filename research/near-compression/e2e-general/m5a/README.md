# E2E milestone M5a: INTAKE, working-set tree and FINAL in-circuit (state lane B)

Plan: `docs/zk-formal/E2E-GENERAL-CHUNK-PLAN.md` §3.2 (the `stRoot` working set), §4 (M5a).
Date 2026-11-03. Labels: **[M]** measured here, **[K]** kernel-checked Lean (std axioms),
**[S]** stated / design only.

## B-T4 (fifteenth session, 2026-11-25): lane B's T1 leaves chain — `stD .none`, the IF's openings, the STATE cut at the `rt` boundaries

Log `docs/logs/e2e-bt4-state-2026-11-25.md`. Plan §3.5 ("Lane B status (B-T4)"); tracker
`docs/zk-formal/E2E-T1-CRITICAL-PATH.md` §2. Nothing here changes `S`, `claimDigest` or the checker
(one circuit change, `STC`'s trie equations, is a soundness fix of lane B's own table).

### Item 1: `stD .none` [K][M]

`StNone.lean`: `.none` has no overlay, so it is in the circuit form for every lane-E part with
`idxOf .none < 2^64` (`fitsB_none'`), its working set is empty and its commitment is
**`stD_none_eq`**: `bdigest (ser ⟨0, zd nodeH zero48 depth, 0, hashOf (.hash 0³²), idxOf .none,
bdigest (encRestB E (strip .none, none))⟩)` (`wsRoot_nil`: the empty tree's root is the zero-subtree
digest). For lane E's `stViewE` the kernel evaluates it (`join-check/StNoneE.lean`,
**`stD_none_viewE`**, run by `join-check/run.sh`):

    stD .none = 799a6864c921b6955b6a85356d65c7a612fa488d824fcb1d79623dac5a750e820ff93e8510b26828fe9e

(`rest` preimage `01 00 00`: `lp (encStV .none) ‖ optEnc none`; trie hash `0³²`). `t1/chain.py`
`ST_NONE` (and `st_none()`, the record recomputed in Python) replaces the `0^42` placeholder at `c0`
/ `c10`: **`h(c0)` `ac01792e…` → `039f9e01…`, `h(c10)` → `dfaf4cfe…`**. Lane G's INIT / FINAL wrappers
take this constant (their T1 kernel lemmas `k0_viewE` / `k10_viewE` used `0^42`).

### Item 2: the IF halves expose `stRoot` (`m5tIFC`) [M][K]

* **`Stc.m5tIFC D` = `m5tIF D`'s tables ++ `[STC, SRNG]`** (`m5a-tool tmpl-ifc`; tracegen `--ifc`).
  The IF's public values are the indices `STC` already reads (0–15 prev root, 16 `wsLen`, 17–34 /
  35–52 the two `ws` roots), so one `STC` row opens **`c1`'s commitment** (tag 1, `ws = R_0`: the
  INTAKE half's `stRoot`, `InitBOut`'s state part) and closes **`c9`'s** (tag 3, `ws = R_n`: the
  FINAL half's `stRoot`, `FinPre`'s state part); `wsLen`, trie, `idx` shared.
* **Soundness fix (`Stc.trieEqs`)**: B-T3's `STC` left the 32 opened trie bytes free (a segment never
  reads the trie). The IF-FINAL half runs on the trie the commitment carries (lane E's `FinHalfB`:
  `final_glue` when the IF's trie is `o.trie`), so `STC` now ties bytes 57–88 to the public
  `prev_state_root` (16 constraints `b₅₈₊₂ᵢ + 256·b₅₇₊₂ᵢ = pub[i]`), in every template that has `STC`.
  Lean: `StcRow.trieI`, `StcSound.comI_trie`, **`StcOKT`** (= `StcOK` with `c.trie = T`;
  `stcOK_of_T`), `stc_row_okT`, **`stc_holdsT`** (any AIR), **`stc_ifc`** (`m5tIFC` from `Holds`:
  `StcOKT r₁ r₉ R_0 R_n wsLen (pubTrie pub) mi mo ∧ wsLen ≤ 2^D`; `srng_send_ifc`, `rng_vT`).
* **The header link** (`HeaderLink.lean`): lane G's named FINAL premise `decodeChunkInner window =
  .ok I.H` is a chain invariant from INIT, not a state-lane row: **`init_header`** (a non-genesis
  `CM.step (init cb wb) = .ok (eng I e)` gives `decodeClaimE cb = .ok I.c`, `decodeChunkInner
  I.c.chunkInner = .ok I.H`, `e` at `start`; from the machine's `intakeK_post`), `header_link`. What
  closes it in the tree: `ctxRoot = ctxD (.intake I)` copied `c1 … c9` (every leaf between copies it)
  and INIT ∧ FINAL sharing `ctx = claimDigest s` with `cb = assemble s.ci secB s.secC` (lane G's
  `InitDig`; `PublicStmt.decode_encode`), so the window FINAL reads is `I.c.chunkInner`.

### Item 3: the STATE segment cut at the `rt` boundaries [M]

`t1cut/make_cut.py` (from lane F's Lean run: `acc.before.committed` = the 8 changes before receipt
1, `after` = all 10) writes `t1cut/seg-keys.json` (tracegen **`--seg-keys`**: segment `s` = the
writes of the keys in entry `s`, ordered by segment; a segment may be empty) and
`t1cut/stc-meta.json` (**`--stc-meta`**: per-dump tags / rests). A segment without writes closes
`RCH(0, R_in)` with `RCH(0, R_out)` (`WSX` `sb = 0`, `R_out = R_in`; mutant `segsb0` shows a segment
with writes cannot). `rest` = `0^42` everywhere (lane I's placeholder; **`encRestI` not adopted**:
`rest` is the hash of the engine position, whose preimage only lane F's rows hold; `STC` is
agnostic — B-T3 — so adopting it is lane F's `rest_out` change plus lane I's chain field).

| dump | chain edge | template | changes | `R_in → R_out` | tags | `stRoot` in → out |
|---|---|---|---|---|---|---|
| `if` | `c1` / `c9` (INIT ⊕ IF, finalize / FINAL) | `m5tIFC` | INTAKE + FINAL (10) | `R_0 = ca91c86e…`, `R_n = 2d2e132a…` | 1 / 3 | `33b13fab…` / `e433137f…` |
| `seg0` = STATE seg A | `c1 → c2` | `m5tSegC` | 8 | `R_0 → R_A = 44e7e021…` | 1 → 1 | `33b13fab… → c6b5dacb…` |
| `seg1` = RT resume's state half | `c6 → c7` | `m5tSegC` | 2 (`t`, receiver account) | `R_A → R_n` | 1 → 1 | `c6b5dacb… → de024944…` |
| `seg2` = STATE seg B | `c7 → c8` | `m5tSegC` | 0 | `R_n → R_n` | 1 → 1 | `de024944… → de024944…` |
| `seg3` = finalize's state half | `c8 → c9` | `m5tSegC` | 0 | `R_n → R_n` | 1 → 3 | `de024944… → e433137f…` |

**Proved on T1 at S** (`logs/BT4-T1-prove.txt`; 8 threads, `HEAVY_MEM=8G`, one at a time beside lane
D's `m8-tree`), native verify + statement check OK, **`m8-import` OK** for all five
(`t1cut/import.sh`: `state-if`, `state-a`, `state-resume`, `state-b`, `state-fin`), 268.2 bits:

| leaf | proof | prove | peak RSS | compressions |
|---|---|---|---|---|
| IF (`m5tIFC`) | **592,280 B** (B-T1b `m5tIF`: 491,416) | 30.9 s | 7.69 GiB | 157 |
| STATE seg A | **510,342 B** (B-T1b one segment: 473,236) | 28.1 s | 7.30 GiB | 109 |
| RT resume, state half | **509,250 B** | 26.5 s | 7.29 GiB | 79 |
| STATE seg B | **509,502 B** | 25.9 s | 7.27 GiB | 61 |
| finalize, state half | **509,460 B** | 27.0 s | 7.22 GiB | 61 |

Saved: **`/data/illia/nearproof-deps/laneB-t1/t4/T1C/{if,seg0,seg1,seg2,seg3}/out/`** (`STATE.proof`,
`STATE.vk.json`, `statement.json`, `htape.json` = the `STC` stand-in's `STMQ` / `STMA`) and
`…/T1C/tmpl/<name>/` (`TMPL.*`, `INFO.json`, `htape.json`; `SHA256SUMS`). The four segments share one
vk (`c063cefe…`). `leaf_chain.py`: `R_0 → R_A → R_n → R_n → R_n = IF's R_n`, `wsLen` 17, IF post root
= the Lean oracle's — **LEAF CHAIN OK**.

**Against lane I's chain** (`t1/chain.py plan`, `leaf_table`): for every lane B leaf the `STC` row's
`r_in` / `r_out` **is the cut's `stRoot`** and the records assembled with them (the other fields:
lane F's engine half / lane D's wrapper) are the chain's **digest for digest**: IF `h(c1)` `4ae97236…` /
`h(c9)` `f7c8b2b6…`; seg A `4ae97236… → 3d9f81b4…`; resume state half `10f87ec9… → afe47194…`; seg B
`afe47194… → afe47194…`; finalize state half `afe47194… → f7c8b2b6…`. Placeholders removed:
`stD .none`, `stRoot.ws` at `c2` (`R_A`, input field `R_A`). New cut digests: `c0` `039f9e01…`,
`c2` `3d9f81b4…`, `c3` `bff8b633…`, `c4` `4d961418…`, `c5` `de147d2d…`, `c6` `10f87ec9…`, `c10`
`dfaf4cfe…` (`c1`, `c7`–`c9` unchanged).

**Mutants** (`t4_mutants.sh … check`, `logs/BT4-mutants-check.txt`): **13 / 13 rejected** —
`stctrie` / `ifctrie` (a consistently hashed opening with another trie: only `trieEqs` fails),
`ifcws` (the IF's opening with another `ws` than `R_0`), `ifcrout` (the FINAL half's `stRoot` not the
closed one: `STMA` unbalanced), `segsb0` (a segment with writes closing like an empty one: `RCH`
unbalanced), and B-T3's 8 `STC` mutants on the cut's seg A.

### Item 4 (`SegLeavesN`'s content half): not done

`LastNew` / `Untouched` from `Holds` stay open (B-T3 item 3).

### Lean [K] (std axioms, no `sorry`; `logs/BT4-axioms.txt`)

`StNone.lean` (`stD_none_eq`, `wsRoot_nil`, `fitsB_none'`), `join-check/StNoneE.lean`
(`stD_none_viewE`, kernel), `Stc.lean` (`trieEqs`, `m5tIFC`), `StcRow.trieI`, `StcSound` (`pubTrie`,
`comI_trie`, `stc_row_okT`, `stc_holdsT`, `ifc_*`, `ns_if`, `rng_vT`, `srng_send_ifc`, `stc_ifc`),
`StHalfC` (`StcOKT`, `stcOK_of_T`), `HeaderLink.lean` (`init_header`, `header_link`).

## B-T3 (fourteenth session, 2026-11-25): the `STC` table, the HOST trie-key prefix (B2-4), `SegLeaves` restated

Log `docs/logs/e2e-bt3-state-2026-11-25.md`. Plan §3.5 ("Lane B status (B-T3)", the `stRoot`
interface) and §5.1; tracker C4 / C5. Merged main (lane E M13) mid-session; nothing here changes
`S`, `claimDigest` or the checker.

### Item 1: the `STC` table [M][K]

`lean/StateM5a/Stc.lean` (AIR), `m5a-tool tmpl-segc` exports **`m5tSegC D`** = `m5tSeg D`'s tables
++ `[STC, SRNG]`; `stc.py` + `tracegen.py` build the row; the prover's `HTAPE` stand-in also plays
lane F's side (`STMQ` sent, `STMA` received). `leaf.sh` now proves STATE segments at `m5tSegC`
(`NO_STC=1`: the B-T2 template).

* **One active row** opens the input `stRoot` and closes the output's: the 139 message bytes of
  `ser c` (`[tag] ‖ ws ‖ u64 wsLen ‖ trie ‖ u64 idx ‖ rest`) are columns; the padded message's 32
  words are built from them in the chip's limb form (`wordW`: bytes 5 and 2 of a word straddle the
  21/42-bit limb cuts, split as `lo5 + 32·hi3`, `lo2 + 4·hi6`); **two SHA-512 compressions per
  opening** on `IF384` (`IV384 → hi → di ‖ xi`); the digest's 48 bytes `ri` are the limbs `di`. The
  output message shares bytes 49–96 (`u64 wsLen ‖ trie ‖ u64 idx`) with the input and has its own
  tag / `ws` / `rest` (`ot`, `ow`, `or`), two more compressions, digest bytes `ro`.
* `ws` of the input = public `R_in` (values 17–34), of the output = `R_out` (35–52); `wsLen` (bytes
  49–56, little-endian) = public value 16, bytes 52–56 zero; **`wsLen ≤ 2^D` in-circuit**:
  `2^D − wsLen = g₀ + 256 g₁ + 65536 g₂` with bytes `g`.
* **`STMQ` (211)** received `[r_in (14 limbs), tag_out, rest_out (14 limbs)]`, **`STMA` (212)** sent
  `[r_out (14 limbs), tag_in, rest_in (14 limbs)]`; a limb is 3 bytes big-endian
  (`65536·b₃ᵢ + 256·b₃ᵢ₊₁ + b₃ᵢ₊₂`). `SRNG` (bus 31) is `RNG`'s byte table on its own bus (the M5a
  premise "extra tables never touch `RNG`" is kept): a byte cell and a high split part are looked
  up once, a low split part twice (`x`, `2^(8−k)·x`).
* Size: `STC` width 670, 955 constraints (degree 2), 755 interactions, height 4 (1 active row);
  `SRNG` 256 rows; 4 more compressions in the segment's chip (T1: 111 → 115).
* **`rest`**: opaque 42 bytes to the table. Lane E's M13 `encRestI` (`join/RestI.lean`: `rest =
  bdigest(d_static ‖ d_queue ‖ d_move)`) changes what lane F hashes into `rest_out`, not the
  opening, so it is adopted by lane F's rows without a change here.

**Lean [K]** (std axioms, no `sorry`; `logs/BT3-axioms.txt`):

| file | what is proved |
|---|---|
| `StcBytes.lean` | `beN_beToNat`, `wbytes_words` (the bytes of consecutive words), **`limbs_word`** (a word's chip limbs from its bytes and split parts), `pad_stc` (FIPS padding of 139 bytes), `blocks_two`, **`sha384_stc`** (SHA-384 of the message = `toB` of the two-compression chain over its 32 words), `limbBytes_limbs`, `u64_bytes`, `leN_leNat` |
| `StcRow.lean` | an active row from its constraints and lookups: `dec3_wordW` / `word_split` / `word_pad`, `wordI` / `wordO` / `blockI` / `blockO` (message words), `digI` / `digO` (digest limbs = digest bytes), **`wsI` / `wsO`** (the opened `ws` bytes = the public `R_in` / `R_out`), **`lenI`** (the opened `wsLen` = public value 16, **`wsLen ≤ 2^D`**) |
| `StcSound.lean` | `two_comps` (chip contract over two chained compressions), `sha_in` / `sha_out`, `comI` (the opened commitment), `ser_comI`, `ser_close`, `qv_dec` / `av_dec` (the `STMQ` / `STMA` limbs as bytes); **`stc_row_ok`**, **`stc_holds`** (any AIR, `STC` at any index, `SRNG` sends bytes): `StcOK r_in r_out R_in R_out wsLen mi mo ∧ wsLen ≤ 2^D` — `r_in`, `mo` from `STMQ`, `r_out`, `mi` from `STMA`; `srng_send_lt`, **`stc_seg`** (the template `segAir D (stcTables D ++ extra)`), **`stHalf_seg`** (with `ws_moves_seg`: lane B's state half of a STATE leaf from `Holds`, `wsLen ≤ 2^D` no longer a premise), **`holdsSt_seg`** (`StHalfC.HoldsSt`, the premise of `stHalf_inst` and of lane E's M13 `StateW.state_sound_stRoot`) |

**Measured on T1 at S [M]** (`leaf.sh … check`, `logs/BT3-stc-mutants-check.txt`): the IF and the
`m5tSegC` segment pre-check OK (5,041 messages), leaf chain OK. **STC mutants** (`stc_mutants.sh`,
precheck): 8/8 rejected — the engine's input `stRoot` (`stcrin`), the taken output `stRoot`
(`stcrout`), the input tag (`stctag`), the output rest (`stcrest`) all leave `STMQ` / `STMA`
unbalanced; an opened `ws` byte ≠ `R_in` (`stcws`) and an opened `wsLen` byte (`stclen`) fail
constraints; **`wsLen = 2^D + 1` with consistent `WSL` rows (`stcbig`) fails only on the `g` byte
lookup**; a non-byte message cell with the same chip limb (`stcbyte`: `b₆₃ + 256`, `b₆₂ − 1`) fails
only on `SRNG`. The B-T1 battery (23 mutants) re-run at `m5tSegC`: 23/23 rejected (precheck).

### Item 2: B2-4, the HOST join key [M][K]

`StHostIf.lean` (changed), `StHostPfx.lean` (new); `tracegen.py --host` routes each write.

* **`StbH`'s key run is the trie key**: row kinds `k0` (`0x09`, only at `j = 0`), `kr` (a receiver
  byte, `CTXB [j − 1, b]`), `kc` (`0x2c`, `CTXL [j − 1]`: its index is the receiver's length),
  `kh` (`HOSTB [ts, hid, 0, base + j, b]`); inside a run `k0 → kr* → kc → kh*`, a run does not end
  in the prefix, a value run (`hid = 314`) is all `kh`. `StwH` gets `pl` with `CTXL [pl − 2]`,
  `HOSTQ` `key_len = klen − pl`, key descriptor `base = kptr − pl` (so `HOSTB` rows `j ≥ pl` read
  `kptr + j − pl`), `ke = 0`. SHA-256 ids `ID_STH = 5·2^24 + m` (disjoint from `STB`'s).
* **`m5tSegH D` = `m5tSeg D` ++ `[STBH, STWH]`**: the runtime's writes (account / access-key
  records, T1's 9 other changes) stay on `SREQ`/`HB` (`STB`/`STW`), only the receiver's
  `ContractData` keys go through the HOST rows. The prover loads both cached stand-ins (`HTAPE`,
  `HOSTTAPE`; the latter also plays the WASM leaf's context: `CTXB`, `CTXL`).
* **Proposed cross-lane ids**: `CTXB` 215 `[i, byte_i]`, `CTXL` 216 `[|receiver|]` (lookups;
  provider: lane A's `vmCtxDigest` remainder / lane F's `RX` receiver bytes).
* **Result [M]** (`logs/BT3-join-laneA.txt`): lane A's 8 `storage_write` messages **verbatim**
  (`HOSTQ` with `key_len = 1`, the key byte `t` at address 0, `HOSTR`, the 5 value bytes) in
  `m5tSegH` on T1: **`PRECHECK OK`, 4,782 messages, no control hack**; the run is `0x09 ‖
  "s5k210.s2a00" ‖ 0x2c ‖ t`, the `t` row reading address 0. Mutants (precheck, 4/4 rejected,
  `logs/BT3-host-mutants-check.txt`): no prefix (`hostnopfx`: the contract key hashed alone —
  `WRITE` and the context lookups unbalanced), a receiver byte changed and consistently hashed
  (`hostrecv`), the tag row claimed as a receiver byte (`hostkind`), `pl` off by one (`hostpl`).
* **Lean [K]** (`StHostPfx`): **`prefix_run`** — if row 0 is not a `HOSTB` row, the kinds follow the
  automaton and the lookups are the receiver's, then the run's bytes are `0x09 :: recv ++ 0x2c ::
  rest` and the `HOSTB` rows are exactly `j ≥ |recv| + 2`; `prefix_kinds`; row facts from
  `StbH.constraints` (`stbh_tag`, `stbh_sep`, `stbh_last`). Open: the cross-table step (row 0 not a
  `HOSTB` row: `HOSTB` rows are `j ≥ pl` by lane A's `HostIf` sends), the `StSound` restatement over
  `m5tSegH`, `stwH_hid` unchanged.

### Item 3: `SegLeaves` (finding B3-1) [K]

* **B3-1**: B-T2's `WsBridge.SegLeaves` quantifies over every `wsLen`-long `Ok` entry list; with a
  repeated key `updE` updates every copy while the rows touch one leaf per key, so it is false in
  general (`ws_final` itself needs distinct key digests). **`SegLeavesN`** (`SegLeavesN.lean`) adds
  distinct keys and the input root; `WsMovesN`, `ws_moves_segN`, `st_stepN` (the view's working set
  key-distinct: lane E's `keysOf` is the chunk's key set) and **`stHalf_segN`** are the results over
  it.
* **Reduction proved**: `segLeavesN_of` — `SegLeavesN` from `l.i < wsLen` (`wsl_ok_seg`) and two
  per-index content facts, `LastNew` (a latest touching row writes the updated entry's leaf) and
  `Untouched` (an untouched index keeps its entry); `wsAt_cases` (what the batched update holds at
  an index). **Open**: `LastNew` / `Untouched` from `Holds` — the M5b chain `write_sent` → `WRITE` →
  `WSA` chain (`ws_final`) → `WSL` leaf (`LeafCR`) restated on the template's indices.

### Item 4: not done

`HOSTR` answer (`EVK`), `storage_read` / `has_key` rows, `regFill`.

### Proofs

**Not re-proved this session.** Lane D's `m8-tree` prover held the box the whole session (≤ 5 G
rule); a `m5tSegC` segment proof needs ~7.6 GB (B-T1b: 7.6 GB peak for `m5tSeg`) and an attempt under
`HEAVY_MEM=5G` was killed after keygen. Everything above is pre-checked (every constraint, every
bus, on T1's real traces). To re-prove in lane D's leaf format (saved `STATE.proof`,
`STATE.vk.json`, `statement.json` per dump, `m8-import`):
`TARGET_DIR=… HEAVY_MEM=12G ./leaf.sh STATE_JSON OUT templates/S.json prove` (STATE leaf at
`m5tSegC`; the IF leaf's AIR is unchanged), and the HOST segment with
`--host --host-join join/t1-laneA-storage-write.json`. Lane D's STATE_SEG template spec must bind
the new `HTAPE` root (it now carries `STMQ`/`STMA`) — the leaf's public values are unchanged.

## B-T2 (thirteenth session, 2026-11-25): lane B's half of the STATE split, the `stRoot` interface for lane F, the HOST join

Log `docs/logs/e2e-bt2-state-2026-11-25.md`. Plan §3.5 ("Split leaves", lane B status) and §5.1.
New Lean: `lean/StateM5a/{WsBridge,StHalfC,T1Ws,T1WsData,GlueRel}.lean` (std axioms, no `sorry`, no
`native_decide`); changed: `StateView.lean` (two fixes below). Tools: `t1_leaves.py` (T1's leaves as
Lean data), `join_laneA.py` + `tracegen.py --host-join` (lane A's messages in the state trace).

### Findings and fixes

* **B2-1 (lane F's `ApplyFaithful` is unprovable) [K].** `SplitC.ApplyFaithful` asks for a
  *function* `apply` with `apply q (root ov) = root (upd q ov)`; that forces any two overlays with
  one root to keep one root after every update (`StHalfC.applyFaithful_coll`) — a property of
  SHA-384 on all overlays, not a consequence of collision resistance. The circuit establishes the
  **relational** statement (every input whose root is `R_in` goes to `R_out`). Replaced by
  `StHalfRel` (lane B) + `ReqsRel` (lane F) and **`split_sound_relC_rel`** (with lane F's
  `EngHalfRC` restated verbatim) ⇒ `TmplSoundRel8C`; the functional split is the special case
  (`rel_of_fun`). Lane F: use `split_sound_relC_rel` in place of `split_sound_relC` + `glue_of`.
* **B2-2 (the view's leaf digest was not the circuit's) [K], fixed.** `StateView.cmp384` applied
  `SHA512.compress` (which reads its block as 128 *byte* values) to `leafBlockN`'s 16 *words*, so
  `stD`'s `ws` field could never equal a leaf proof's `R_in` (binding was unaffected). Now
  `cmp384 b = … compress IV384 (wbytes b)`. Checked in the kernel against T1's real roots (`T1Ws`).
* **B2-3 (non-final position check), design adopted [K].** `stD` tags an engine state at `done`
  with `3` (`StateView.tagOf`; was `1` for every engine state), so "the position is not final" is
  one byte of an opening of `stRoot`: `StPosOK d := ∃ c, c.WF ∧ c.tag = 1 ∧ bdigest c.ser = d`.
  Not a change of `S`, `claimDigest` or the checker (a lane-B view commitment).

### Item 1: the state half [K]

| file | what is proved |
|---|---|
| `WsBridge.lean` | the circuit's digests are the view's: `cW` (the real compression on a word block), `cW_ok` (`CompressOK cW`, no assumption), `toB` / `toB_inj`, **`toB_nodeH`** (one compression of `a ‖ b ‖ padW` from `IV384` = SHA-384 of the 96 bytes, FIPS padding), **`toB_leaf`** (circuit leaf digest = `cmp384`), generic `root_map` / `extUp_map` / `extUp_shift`; **`wsRoot_dig`** (the view's depth-24 root = `toB` of the circuit's depth-`D` root extended by `24 − D` zero levels) and **`ws_moves_seg`**: from `Holds` of `m5tSeg` (+ the chip contract, `NodeCR cW`, the same premises as `seg_rin_rout`), `WsMoves P wsLen R_in R_out upd` — every entry list with the view root `R_in` (the public limbs as bytes) goes under `upd` to the view root `R_out` — given **`SegLeaves`** (named, open: the touched leaves' new digests are the leaves of `upd es`; the per-template restatement of M5b's `write_sent` / `ws_final` / `final_val`) and `wsLen ≤ 2^D` (named: not constrained by the segment template; the IF / `STC` must fix it) |
| `StHalfC.lean` | **position**: `posOK_sound` (`StPosOK (stD P v)` ⇒ `v` an engine state at a non-final position, or `Sha384Coll`), `posOK_stOfK`, **`rtPos`** (lane F's `RtView.pos` in the form `Sha384Coll ∨ ∀ out, c.pos ≠ .done out`), `posOK_complete` (honest side). **`stRoot` step**: `StcOK` (the statement of the new `STC` table: open the input `stRoot` to a well-formed `c` with `c.ws = R_in`, `c.wsLen = wsLen`, hand `(c.tag, c.rest)` to the engine half, close `stRoot' = bdigest (ser {c with tag, ws := R_out, rest})` with the engine half's output meta), **`st_step`** (`StcOK` ∧ `WsMoves` ⇒ every `fits` state committed by `stRoot` and related to `v'` by the requests (`StepRel`: `wsOf v' = upd (wsOf v)`, same trie root and index, `metaOf v' = mo`) has `stD v' = stRoot'` and `metaOf v = mi`, or `Sha384Coll`). **Split**: `EngHalfRC` (lane F's, verbatim), `StHalfRel`, `ReqsRel`, **`split_sound_relC_rel`**, `rel_of_fun`, `applyFaithful_coll`; the STATE / RT instance (`StQ = (w, mi, mo)`, `W` = the 42-B `stRoot`, `stRel`, `HoldsSt`): **`stHalf_inst`** (`StHalfRel` from `StcOK` ∧ `WsMoves`, `Bad = Sha384Coll`) and **`stHalf_inst'`** (with lane F's `EngHalfRC` and `ReqsRel`: `TmplSoundRel8C`). **Overlay reduction for lane F**: `updE` (apply a committed-change list), `entryAt_upd`, **`wsOfB_upd`** (same trie, committed lookups = `w` over the old ones ⇒ working set = `updE w` of the old one). |
| `T1Ws.lean` (+ `T1WsData`, generated) | **non-vacuity on T1's real state leaf, by the kernel**: the segment proof's public `R_in` / `R_out` limbs (`statement.json`) read as the circuit reads them are `ca91c86e…` / `2d2e132a…` (`t1_pub_rin/rout`), `wsLen = 17`; the view's depth-24 root of T1's INTAKE leaves is `R_in` and of the after-leaves `R_out` (`t1_rootL0/1`); T1's change list applied by `updE` gives exactly the after-leaves (SHA-256 of every written value in the kernel, `t1_upd`); **`t1_ws_nonvac`**: for every view with lane E's depth and lane B's leaf block and every entry list with T1's keys and leaves, the conclusion of `WsMoves` holds at the proof's public values; `t1_stc`: the honest commitment satisfies `StcOK`. 35 s under a 4 GB cap (`lake env lean`; the data are byte-list literals — the kernel evaluates `ofHex?` on long strings too deeply). |

**Against lane E's M12 glue (merged mid-session, `NearSpecV3/E2E/Glue.lean`) [K]:** M12 restates
lane B's side as `Glue.ApplyFaithfulS root apply` — the same functional shape, unprovable for the
same reason (B2-1). `GlueRel.lean`: **`state_sound_relC_rel`** closes lane E's own STATE instance
(`stateSem`, `W` = optional working-set root) from lane F's `EngHalfRCOn` and lane B's relational
`StHalfRelS` through lane E's `state_reqs` (no `ApplyFaithfulS`); `entries_updK` (the entries of
`updK q f` are `updE q` of the entries, so `StHalfRelS` is `WsMoves` with `upd = updE q`). Caveat:
with `W` = the bare working-set root nothing carries `wsLen` or the value bounds that `WsMoves`
needs, so lane B recommends `W = stRoot` (`stHalf_inst`), where the `STC` opening fixes them.

**What remains for lane B's half (open):** `SegLeaves` (the per-template restatement, wide but
mechanical — the M5b proofs exist); the `STC` table itself (2 SHA-512 compressions per opening of the
139-B preimage, a byte ↔ limb decomposition of the 48-B roots, `c.wsLen ≤ 2^D`) — the Lean
statement it must meet is `StcOK`; nothing is re-proved this session because no AIR changed.

### Item 2: the interface lane F's F3-1 needs (resume / STATE / enter) [S][K]

Lane F's resume AIR copies `stRoot`; under this interface the output `stRoot` comes from lane B's
rows in the same leaf. One joined leaf trace = lane F's rows + lane B's `m5tSeg` tables + `STC`:

* **`STMQ`** (engine → state, one message, first row): `[r_in (14 limbs: the 42 B of the input
  record's `stRoot`, 3 B per limb), tag_out, rest_out (14 limbs)]` — `r_in` copied from the input
  record (`engF.off "stRoot"`), `(tag_out, rest_out) = metaOf (stOfK κ I c')` of the output engine
  state (`tag_out ∈ {1, 3}`: `3` iff `c'.pos = done`; `rest_out = bdigest (encRest (restOf …))`).
* **`STMA`** (state → engine): `[r_out (14 limbs), tag_in, rest_in (14 limbs)]` — `r_out` is
  written into the output record's `stRoot`; `(tag_in, rest_in)` is the input's opening (the engine
  rows may use `rest_in`'s preimage to open the input position).
* **`SREQ` / `HB`** (engine → state, as M5b): `SREQ [ts, pr, seg = 0, klen, kptr, vlen, vptr]`, `HB
  [ts, addr, byte]`; the committed-change list `w` of the step is the requests' overlay
  (`StSoundF1.ovl`: last request per key, `none` for a remove).
* `wsLen`, `R_in`, `R_out` stop being public values of a joined leaf (they are inside `stRoot`).
* Proposed cross-lane bus ids (the integrator's joined numbering): `STMQ` 211, `STMA` 212, `SREQ`
  213, `HB` 214 (after lane A's `HOSTQ/R/B` 208–210); lane F's local `B_SREQ 9`, `B_HB 8` and lane
  B's local ids are renumbered by the AIR export.
* **Enter's position check**: the enter leaf sends `STMP [r_in]` and lane B's `STC` row opens it with
  `tag = 1` (`StPosOK`); Lean: `rtPos`, and `RtView.pos` takes `Sha384Coll ∨ _` (one line in
  `EnterC.in_fields`; `enter_relC`'s `Bad` already contains `Sha384Coll`).
* **Lean, lane F's side**: `EngHalfRC` with `W = Bytes`, `Q = StQ`, `wIn x = V.stD (stV V x)`,
  `qOf x x' = ⟨changes of the step, metaOf (stV x), metaOf (stV x')⟩`; `ReqsRel` for `stRel`: both
  states `fits`, `wsOf` updated by `updE w` (via `wsOfB_upd`: the overlay's trie is unchanged —
  OvlInv's `reach_trie_nodup` — and `committed` after = `w` over before), trie hash and index
  unchanged (`idxOf = 0`); then `stHalf_inst'` gives `TmplSoundRel8C`.
* **Open for lane E / F**: `rest_out` is `bdigest (Enc.encStV (strip v'))`, a witness-sized hash
  of the whole stripped engine state per step; a cheaper `rest` (a chain / tree of the position's
  parts so one receipt step touches O(1) of them) is lane E's encoding choice.

### Item 3 (M6.4): the HOST join on T1 [M]

One joined trace (lane A's Wasm segment AIR + `m5tSegH` in one prover) is **not feasible this
session**: lane A's segment trace is generated inside lane A's Rust prover (its own AIR JSON format,
bus numbering and SHA-512 chip), and lane A's build worktree is gone. What was done instead is the
message-level join: **lane A's own 8 messages for T1's `storage_write` fed into lane B's state rows**.

* `join_laneA.py` reads lane A's `a-t1/logs/j-t1-segcheck.txt` (the 8 messages its joined AIR
  leaves unbalanced on T1: HOSTQ, HOSTR and the key byte verbatim, the 5 value bytes at
  `value_ptr + j` under wire 314 = T1's committed value `again`) and writes
  `join/t1-laneA-storage-write.json`: `ts = 18`, `S = 18`, `register_id = 1`, `key_ptr = 0`,
  `value_ptr = 16`, evicted `1`, `g_after` lane A's.
* `tracegen.py --host --host-join FILE`: that write's `STWH` / `STBH` rows carry lane A's call
  (time, scope, register, buffer addresses, answer), and the `HOSTTAPE` stand-in carries lane A's
  messages verbatim for it (the other 9 writes are the runtime's, stand-in as before).
* **Result [M]** (`logs/BT2-join-laneA.txt`, T1 at S, `m5tSegH`, prover pre-check): **18 unbalanced
  messages, all on the key**: HOSTR and the 5 value bytes (wire 314, addresses 16..20) balance;
  HOSTQ differs only in `key_len` (lane A 1, lane B 15) and the 16 `HOSTB` key bytes differ (lane A
  sends the contract key `t` at address 0; lane B's rows read and hash the **trie key**
  `0x09 ‖ "s5k210.s2a00" ‖ "," ‖ "t"`). Control (`logs/BT2-join-control.txt`): the same messages
  with the key buffer replaced by the trie key **balance** (`PRECHECK OK`, 4,792 messages).
* **Finding B2-4 (the trie-key prefix).** `storage_write(key)` names the contract-level key; the
  working set is keyed by `TrieKey::ContractData { account_id, key }`. The state rows must hash
  `0x09 ‖ receiver ‖ 0x2c ‖ key` with the receiver from the call's context, not from `HOSTB`.
  **Precise remaining step:** `STBH`'s key run gets a prefix part — rows `j < 1 + |receiver| + 1`
  read the bytes `0x09`, the receiver account id (a bytes run on a context bus the WASM leaf
  exposes: lane A's `vmCtxDigest` remainder / lane F's `RX` receiver bytes) and `0x2c`, rows after
  read `HOSTB [ts, 58, 0, key_ptr + j − p, b]`; `StwH`'s `HOSTQ` `key_len` becomes `klen − p`
  (`p` = prefix length) and its `DESC` the whole trie key. Lean: `stwH_hid` and the `StSound`
  restatement over the prefixed run. Then the joined trace itself needs one prover for lane A's AIR
  + `m5tSegH` (lane D / integrator: a common AIR JSON, unified bus ids, one SHA-512 chip instance).
* Still open from B-T1b: the HOSTR answer (evicted flag from `WSA`'s `WM` read via `EVK`; lane A
  computes `g_after`), `storage_read` / `has_key` rows, `regFill`. Proving the joined segment
  (7.7 GB) was not run: lane D's tree prover held the build slice (≤ 4 G rule).

## B-T1b (twelfth session, 2026-11-21): per-template soundness, an IF soundness fix, the lane G / lane E interfaces

Log `docs/logs/e2e-bt1b-state-2026-11-21.md`. Item 1 mostly done (the segment template end to end
at digest level, the `WSX` bus step for both templates, the IF's roots; the IF's FINAL/INTAKE
restatement is open, below), **one soundness fix found and fixed** (the IF `RCH` matching), items
2–4 design only.

### Item 1: the templates' soundness theorems [K] (std axioms, no `sorry`; `Audit.lean`)

**How the M5a stack is reused (`TmplSeg.reix`).** The M5a decoders and field lemmas are pinned to
`fullAir`'s table indices (`WSA 7`, `RNG 9`, `WSL 10`, `WSP 11`). `reix σ tr` reads table `σ t` of
`tr` at index `t` (`Expr.eval e (reix σ tr) t r = Expr.eval e tr (σ t) r` by `rfl`), so with
`trS tr := reix sigSeg tr` every row decoder (`wsl`, `wsa`, `wspF`) and row lemma (`wsp_rowF`,
`WsCost.wsa_gap`, `WsLen.wsl_lt_wsLen`, …) applies verbatim to the template's tables. Only the
lemmas that read `Holds` of the whole AIR (bus decomposition, `RNG`/`IF384` membership) are
re-proved for the template (`segAir D extra = m5tSeg D ++ extra`):

* `TmplSeg`: `busList_seg` (WM/PT/RCH only on `WSA`/`WSL`/`WSP`/`WSX`), `pt_traffic_seg`,
  `wm_traffic_seg`, **`rch_traffic_seg`** (`WSX`'s `RCH(0, a₀)` / `RCH(sb₀, b₀)` in place of
  `WSN`'s roots), `rng_send_lt_seg`, `wsa_gap_seg`, `wsl_ok_seg`, `wsp_ok_seg`, `node_comp` (any
  AIR), **`ws_decoded_seg`** (= `WsDecode3.ws_decoded` for the template) and
  **`m5tSeg_ws`**: for every depth-`D` working set `ws0` with root `a₀`, the working set after the
  segment (`WsSeg.wsAt`: each touched leaf → its `WSL` row's new digest) has root `b₀`; every touched
  leaf is a real entry (`i < wsLen`) whose old digest is `ws0`'s leaf; and, given distinct key
  digests among a segment's touched leaves (`hkd` — the INTAKE-key property, which the IF proof
  establishes for `ws0`), each closing value is its entry's latest write (the `WM` chain).
* `TmplWsx`: **`wsx_ext`** (the `WSX` bus step, any AIR / table index): from the constraints
  (`FieldWsx`) and the chip contract (each active row's `zo = H(z,z)`, `ao = H(a,z)`, `bo = H(b,z)`),
  `z₀ = Z_D` and `extUp H Z_D 0 (24 − D) a₀ = pubDig pub 17`, the same for `b₀` and `pubDig pub 35`;
  `wsx_ext_seg`, `wsx_ext_if`; **`seg_rin_rout`**: every working set whose depth-24 root is the
  public `R_in` becomes, after the segment, one whose depth-24 root is the public `R_out`
  (`ext_inj` under `NodeCR`).
* `TmplIf`: `busList_if_rch` (RCH only on `WSN` 6 / `WSX` 9), `sb_one`, `rch_traffic_if`,
  **`rch_if`** (with `WSN`'s root messages `[(0, r₀)]`, `[(nw, r_F)]`: `r₀ = a₀`, `r_F = b₀`,
  `nw = 1`) and **`m5tIF_roots`**: the INTAKE tree's root extended to depth 24 is the public `R_0`,
  the FINAL tree's the public `R_n`.
* `TmplDeploy`: the deployed extra tables (cached `SREQ`/`HB` tape, `ChipStub.chipStub`) meet the
  bus premises (`seg_extra_ok`, `if_extra_ok`), so with `ChipStub.holds_of_holdsX` (the prover's
  precheck ⇒ `Holds`) the theorems apply to the saved T1 dumps.

**Non-vacuity on T1 [M]:** the re-proved T1 dumps (below) pass the precheck (every constraint, every
bus, the native chip's `IF384` sends a permutation of the receives), i.e. `HoldsX` + the chip list,
which `holds_of_holdsX` turns into `Holds (segAir 5 [htape, chipStub])` /
`Holds (ifAir 5 [chipStub])`; the premises `hx` hold by `TmplDeploy`; `ws0` = the INTAKE leaves
(root `R_0 = ca91c86e…`, `leaf_chain.py`); the conclusions' roots are the dumps' public values
(`R_in = ca91c86e…`, `R_out = 2d2e132a…`).

**Open [S]:** (a) the IF's INTAKE / FINAL halves restated for `m5tIF` (`m5b_final`'s premises
`ws_entries` / `final_key` cross the cut: a FINAL leaf has its INTAKE key only *because* the
segments keep keys — so the IF statement must be conditional on the FINAL leaf list, `ws_final`'s
shape, and `FinalOrder`/`SnFinal6` need that hypothesis in place of `ws_entries`; wide, not done);
(b) `WsDecode4.wsn_roots` for `ifAir` (the singleton `WSN` root messages `rch_if` takes; same
tables, same indices 5/6 — a port); (c) `hkd` from `ws0`'s distinct keys (`wsl_leaf` + `LeafCR`
for the template); (d) the composition IF ∧ segments ∧ equal public roots ⇒ `m5b_final`'s
conclusion, and `m5tSegH` (the HOST-fed tables at indices 5/6 change only `nb_seg`/`ns_seg`).

### Soundness fix: the IF's `RCH` matching (`Tmpl.Wsx.sbPin`) [K][M]

In `m5tIF` both `WSN` (INTAKE root `(0, r₀)` sent, FINAL root `(nw, r_F)` received) and `WSX`
(`(0, a₀)` received, `(sb, b₀)` sent) use `RCH`, with `nw` and `sb` free columns. Besides the
honest matching there was a second one: `nw = sb = 0`, `r_F = r₀` (a FINAL tree equal to the INTAKE
tree: no changes, `post = prev`) and `WSX` closing itself (`a₀ = b₀ = X` for **any** `X`). So an IF
proof could publish `R_0 = R_n = ext(X)` for an arbitrary working set `X` (fabricated pre-values),
and segments whose writes leave `X` unchanged would chain to it. **Fix:** `WSX` of `m5tIF` pins
`isFirst·(sb − 1)` (`sbPin`); `tracegen.py --split` sets the IF's `sb` and `WSN`'s `nw` to 1 (the
segment template is unchanged: `sb` there is the top row's `seg + 1`). `TmplIf.rch_if` proves the
matching is now unique. Mutant `wsxsb` (`sb = nw = 0` with honest roots, balanced): **accepted by
the B-T1 AIR, rejected by B-T1b's** (`precheck: WSX: constraint 118 fails on row 0`,
`logs/BT1b-wsxsb.txt`). The M5b monolithic AIR is not affected (no second `RCH` source).

**Re-proved [M]** (the IF AIR changed; the segment AIR did not): T1 at S — IF **491,416 B**, 35.2 s,
verify 44 ms, 7.3 GB; seg0 473,236 B (unchanged AIR, re-proved), 37.2 s; chain OK, post root
`1db48e38…249628` = Lean oracle (`logs/BT1b-T1S-prove.log`). T2 at M — IF **515,982 B**, prove 855 s on the loaded host (load ≈ 35; was 123 s), verify 56 ms, 25.7 GB, precheck OK (`logs/BT1b-T2M-prove.log`); its segment AIR is unchanged (B-T1: 510,652 B).
Mutants on T1 at S (full prover, `logs/BT1b-T1S-mutants.txt`): **23 / 23 of B-T1's rejected** on the new AIR; plus the new `wsxsb` **rejected** (precheck `WSX: constraint 118`, then the native verifier): **24 / 24**.

### Lane G's requests (coordinator, 2026-11-21) [S]

1. **ℓ_B in INTAKE.** The IF template does **not** decode the claim today: `prev_state_root` is a
   public value and the key list / pre-state nodes are witness; no AIR of any lane decodes
   `decodeClaimE cb` (block list, chunk slots) yet, so neither the ℓ_B span check nor the binding of
   `prev_state_root` to the claimed chunk's slot exists. Adding "an ℓ_B check" to the IF without a
   claim decoder would check nothing. Design (for the `.init` leaf = lane G's INIT ∘ this INTAKE in
   one trace): a `CLMW` framing walk over `cb` starting at `|pre|`, one row per field of
   `encList BlockRec.encode` (`u8 headerVersion`, 32-byte `prevHash`, `borshBytes innerLite` /
   `innerRest` = u32 length + bytes, `encList ChunkSlot.encode`), reading bytes by lookup on INIT's
   `CLM` byte rows (`(pos, byte)`), each row's end = the next row's start, the last end
   `= |pre| + ℓ_B` with ℓ_B the cell INIT hashes into `ctxRoot` (`u32 ℓ_B`); the slot rows expose
   the chunk's `prev_state_root` to `WSB`'s public limbs 0–15. Mutant `lbshift` (ℓ_B ± 1, blocks
   re-framed). Not built (a new decoder; lane E/G to confirm the `.init` join).
2. **`SegSoundInit` / `SegSoundFinal` split.** Agreed with lane G's reading: `.init` = INIT ∘ INTAKE
   (the IF proof's INTAKE half: `prev_state_root, wsLen → R_0`), `.final` = this FINAL (`R_n →
   post_state_root`, `m5b_final`'s root) + M5c's implicit transitions + lane G's `tailNew` /
   `headerOk`. **`FinIn` bus (option (a), lane G's recommendation):** the IF's `TCH(n, post)` end
   becomes a send `FINB [k, byte]`, `k < 32`, of `post_state_root`'s bytes (limb `t` of `pack2` is
   bytes `2t`, `2t+1`) received by lane G's `FIN` table at `FinIn` bytes 0..32 (lane G's layout,
   m5d README / leaf spec §4), in place of the public values 53–68. Bus id: lane E's numbering (not
   chosen here). Not built.

### Lane A's join (A-T1, main `4d41313e3`) [K][S]

* **Wire id 314 accepted [K]:** lane A sends `storage_write`'s value buffer on `HOSTB` under wire id
  `58 + 256 = 314`. `StbH` now accepts `hid ∈ {58, 60, 314}` (`HID_WRITE_V`,
  `act·(hid − 58)(hid − 60)(hid − 314)`) and `StwH`'s value-run `DESC` receive expects `hidE + 256`
  (the value run exists only for `pr = 1`, so its id is 314; the key run keeps 58 / 60);
  `tracegen.py --host` emits 314 for value bytes. (`HOSTB`'s 4th field is now lane A's absolute
  address — what `StbH` already reads.)
* **The 8 messages [S].** Lane A's joined T1 segment lacks `HOSTQ [18, 58, 18, 5, 1,0, 0,0, 5,0,
  16,0, 1,0, …]`, `HOSTR [18, 0, 1, 0, g_lo, g_hi, 1, 0]` and 6 `HOSTB` bytes (key `t` at 0, value at
  16..20). The layouts are exactly `StwH.qMsg` / `StwH`'s `HOSTR` send / `StbH`'s receive; what
  supplies them is `m5tSegH`'s rows **inside lane A's WASM-leaf trace** (a storage call happens in a
  WASM segment, not in a VM-free STATE segment), so the WASM leaf carries the working-set tables
  and its `R_in → R_out` (`seg_rin_rout`'s statement for the HOST-fed tables). This session's
  standalone `m5tSegH` dump still routes all 10 of T1's writes through a `HOSTTAPE` stand-in
  (`S = 0`, `rid = 0`, segment-local `ts`); on the joined trace only the contract's write is a HOST
  call (the other 9 are the runtime's, on `SREQ`/`HB` in STATE/RT segments). Building the joined
  trace (lane A's tracer + `tracegen --host` for that one write with lane A's `ts`, `S`, `rid`) is
  the next step; not done.
* **What `StorageJoinObl` needs from these rows:** `hb` (the request bytes are exactly the key /
  value buffers) is `StbH`'s `DESC`-closed runs at `base + j` — to be stated over lane A's
  `hostReqBytes`; `ans` (`st`, the eviction word, `g_after`) and `regFill` (the evicted value's
  register bytes) are M6.4 (below), in lane A's `SpecU` form of `ProducerObl.spec` (lane A found
  the old `spec` unsatisfiable for `storage_write`); not done.

### Item 2 (M6.4: `HOSTR` from the state side) [S]

The evicted flag of `storage_write` is the entry's old present flag `cp`, which only `WSA` sees (its
`WM` receive). Binding it needs `WSA` to export it — a new interaction `snd EVK (act) [seg, t, cp,
cl]` on `WSA`, received by `STWH` as `rcv EVK (act) [0, ts, rlo, ecl]` with `rhi = 0` (`cl` = the
evicted length, which the `storage_write_evicted_byte` gas cost needs). `g_after` is not the state
side's to compute: `HOSTQ` carries no gas, so the state side should return the cost inputs
(`klen`, `vlen`, evicted flag / length) and lane A's HOST chip compute `g_after` from its own
gas-before. `WSA` is shared by the M5b and both templates (and `STW` must then receive `EVK`), so
this is an AIR change to the M5b stack with its re-proofs and mutants: **not done this session**.

### Item 3 (lane B's component of `SegSoundState`) [S]

Lane E's split (`SegSoundState8`, plan §3.5 on lane E's branch `7cf7a4ad1`, not on main) lists the
state field as `stRoot = stD (stOfK (κ I) c)`; who proves which part is not yet written. Against
lane B's proposal (README §B-T1): lane B's component is `seg_rin_rout` — the `ws` field moves
`R_in → R_out` by the segment's writes, `wsLen` and the trie root unchanged — and the IF's
`m5tIF_roots` gives `.init`'s `R_0` and `.final`'s `R_n`. **Missing for a Lean statement over
`stD`:** the bridge between the circuit digest `nodeH compress` on `Dig` and `StateView.nodeH =
sha384 (l ‖ r)` on bytes (a 96-byte SHA-384 is one compression of `IV384`; `zD D` is then
`zeroDig D`), and lane E's overlay of a VM-free run (which requests a run makes).

### Item 4 (completeness): not started.

## B-T1 (eleventh session, 2026-11-21): the state side as pinned-shape tree leaves; the HOST join

Log `docs/logs/e2e-bt1-state-2026-11-21.md`. Milestone B-T1 of the M10 re-centring (T1 =
`d3c8/d3/02-h10196-s3` end to end). Items 1–3 done; item 4 (completeness) not started.

### Item 1: `FitsReach` in the `stOfK` form [K]

`StateViewParams.FitsReach E κ R := ∀ I c, R I c → fitsB E (stOfK (κ I) c)` (was `∀ c, R c → fitsB E
(stOf c)` with `stOf c = stOfK [] c`, unprovable on real runs). Lane E's `StViewE.FitsReachK κ R` is
`FitsReach stViewE κ R` by `rfl`, so lane E's `fitsReachK_engine` discharges it for the engine
(`lean/join-check/`: `run.sh` elaborates lane E's `join/StViewE.lean` with the two bridging
theorems appended — that file is not a lake module; std axioms).

### Item 2: the state segment as a tree leaf [M][K]

**The cut [M].** Only `RCH` (the working-set root between segments) crosses the M5b AIR
(README §M5a-3), so it splits into two templates of the same tables plus one boundary table
(`lean/StateM5a/Tmpl.lean`, `m5a-tool tmpl-if|tmpl-seg D`):

| template | tables | crosses on public values |
|---|---|---|
| `m5tIF D` (INTAKE + FINAL) | `SHA KEY BR SN KCMP WSB WSN SNC RNG WSX` + chip | `prev_state_root`, `wsLen`, `R_0` (after INTAKE), `R_n` (before FINAL), `post_state_root`, the change count `n` |
| `m5tSeg D` (one STATE segment) | `SHA WSA WSL WSP RNG STB STW WSX` + chip + cached `HTAPE` | `wsLen`, `R_in`, `R_out` |

* **`WSX`** extends a depth-`D` root to lane E's committed depth 24 (`Enc.wsDepth`): rows
  `lvl = D … 23`, `x' = H(x, Z_lvl)`, `Z' = H(Z, Z)` from the constant `Z_D` (Lean computes it:
  `Tmpl.zeroLimbs`, equal to Python's), for two roots per proof (3 compressions per row). The
  `TCH` ends that were the public `TAPE` are public values of `WSX` in `m5tIF`: **the IF proof
  has no cached table**.
* **Public values** (one statement vector; every AIR reads a prefix of it and the prover's
  statement check compares all of them): 0–15 `prev_state_root` (16-bit limbs), 16 `wsLen`,
  17–34 / 35–52 the depth-24 roots A / B (18 limbs of 21 bits, the SHA-384 words), 53–68
  `post_state_root`, 69 `n` (IF only). These are `StateView.StCommit`'s `ws` / `wsLen` / `trie`
  fields (+ the post root for FINAL); `idx` is lane E's `idxOf = 0` (times restart per segment).
* **Segments.** One proof per STATE segment; times restart at 1 and the segment is `seg = 0`
  inside its proof (`HB(ts, …)` is then unambiguous: README §M5a-9); `--segs S` cuts evenly,
  `--seg-cap N` cuts on overflow (a new segment when the next write's bytes would pass `N`). The
  INTAKE find walks and the FINAL change walks stay in the IF proof (they share the pre-state
  node store `VER`, keys and key order); the IF proof serves both the INTAKE leaf (statement
  `prev_state_root, wsLen → R_0`) and the FINAL leaf (`R_n, wsLen, prev_state_root → post`):
  each conjunct holds for its own public values, so two different IF proofs at the two leaves
  are still sound. Splitting it would make FINAL re-hash the pre-state nodes it reads (the
  batching gain, 47–82 % of FINAL's SHA-256 work on T1/T2) and duplicate `KEY`/`KCMP`.

**Lean [K]** (std axioms): `Tmpl.m5tIF` / `m5tSeg` (tables = M5b tables + `WSX`: `m5tIF_tables`,
`m5tSeg_tables`); `Merkle.root_pad` (the depth-`(D+k)` root of the leaves padded with zero digests
= the depth-`D` root extended by `k` zero-sibling levels; no hash assumption), `ext_inj`
(collision-free node hash ⇒ the extension is injective), `TmplView.wsRoot_ext` (**lane E's
committed `wsRoot` at depth 24 is that extension of the circuit's depth-`D` root**),
`zeroDig_eq`, `wsxChain_out` (a `WSX` row chain at record level computes `extUp`), and at field
level **`FieldWsx.wsx_layout`** (from the constraints alone: rows `0 … 23 − D` active with
`lvl = D + r`, `top` exactly on row `23 − D`, so the table has ≥ 24 − D rows), `wsx_link`
(`z' = zo`, `a' = ao`, `b' = bo`), `wsx_first_z` (`z = Z_D`), `wsx_top_pub` (the public roots).
**Open [S]:** the bus step joining these to `wsxChain_out` (each row's three compressions are in
the chip's list: `IF384` balance + `Sha512If.comp_node`), and the per-template soundness theorems: the M5a/M5b theorems are stated about
`m5bAir`'s table list (decoders pinned to its table indices); restating them for `m5tIF` /
`m5tSeg` (the same tables, `WSX` on `RCH`/`TCH` in place of `WSP`/the tape) is mechanical but wide.

**Prover [M]** (`prover/`, the same interpreter): now built against **the verifier's backend** (a
frozen copy of lane D's `pq-e2e-d9` `stark-backend-unified` + `plonky3-ext12`; the recursion crate's
own `sha384/{config,mb}.rs` copied unchanged), the CPU engine `Sha384CpuEngine`, and the cached
table committed as `commit_program_part` does. A dump from `tracegen.py --split --template T`
carries its template (`template.json`); then every table is padded to its pinned height (SHA-256
table, SHA-512 chip and `HTAPE` included; zero rows), the tight-height floor is the full height (the
proof's `(log_height, tight_height)` per AIR is the template's), and the parameters are **lane D's
base configuration** (`pq-chunk-e2e/src/profile.rs::shaped_params_geom`: first-order certificates
from `final-soundness/calc/dkt_certs_o2.json` minus `DKTCertsO2_big.keys`, list decoding m = 64,
`k_first` 2, `domain_odd_factor` 15, logup message length 7, `zk = 0`) with **query grinding 24
bits** and the template's `(n_stack, log_blowup, w_stack)`. `prove … OUT` saves `STATE.proof`
(`Proof::encode`), `STATE.vk.json` (the `SavedVk` envelope with `domain_odd_factor`, as
`pq-chunk-e2e` reads it) and `statement.json` (per AIR: public values, heights, cached roots).
**Lane D's own driver reads and verifies them** (`nearproof-chunk-e2e fs-count VK PROOF 0` of the
`pq-e2e-d9` build: `verify_with_points` succeeds on both T1 proofs).

`leaf.sh STATE OUT TEMPLATE [check|prove]` runs the cut end to end and `leaf_chain.py` checks the
proofs' public values: `if.R_0 = seg0.R_in`, `seg_k.R_out = seg_{k+1}.R_in`, last `R_out = if.R_n`,
one `wsLen`, IF's `post_state_root` = the Lean spec oracle (`m5a-tool apply`).

**Templates [M]** (`census_tmpl.py`, `templates/{S,M,L}.json`, `logs/BT1-template-census.{txt,jsonl}`).
A census of the cut over all 19,007 `d3` cases (Lean run, extraction, `tracegen --split
--stats-only` at the natural depth; 16,205 trace, the same 85.26 % as M5a-9) and three nested
classes by working-set depth; per class every pinned height is the smallest common per-table
quantile that keeps the class's joint coverage ≥ 99 %, D-dependent heights moved exactly to the
class depth (a smaller case runs zero-padded):

| class | D (≤ keys) | members | IF covers | IF cells / `n_stack` / `w_stack` | seg cells / `w_stack` | one STATE segment |
|---|---|---|---|---|---|---|
| S | 5 (32) | 13,594 | 13,580 (99.90 %) | 7.91 M / 18 / 10 | 5.03 M / 8 | 99.36 % (82 need 2, 5 need 3, cut on overflow) |
| M | 6 (64) | 2,071 | 2,053 (99.13 %) | 15.81 M / 20 / 6 | 7.82 M / 5 | 99.28 % (4 need 2) |
| L | 7 (128) | 572 | 570 (99.65 %) | 31.59 M / 20 / 10 | 15.63 M / 7 | 99.83 % |

A case left out by its class falls to the next one: **16,203 / 16,205 trace-OK cases (99.99 %)
fit a template**; the other 2,802 state cases are the M5a-9 completeness gaps (item 4), not
heights. Every template: lb 1, grinding 24, 268.2-bit calculator, WHIR queries [100, 71, 45, 33]
(k [2, 4, 4, 4]). Lane D's one-leaf-geometry-per-setup rule makes L's leaf the setup's.

**T1 and T2 at their templates [M]** (8 threads, shared host; `logs/BT1-*-prove.log`,
`logs/BT1-proofs.txt`):

| case / template | proof | bytes | prove / verify | peak RSS | root (= Lean oracle) |
|---|---|---|---|---|---|
| T1 / S | IF | 490,156 | 39.1 s / 43 ms | 7.3 GB | post `1db48e38…249628` |
| T1 / S | seg0 | 473,236 | 37.2 s / 28 ms | 7.7 GB | `R_0 ca91c86e…` → `R_n 2d2e132a…` |
| T2 / M | IF | 516,654 | 123.4 s / 34 ms | 25.7 GB | post `61f5330a…07993006` |
| T2 / M | seg0 | 510,652 | 121.9 s / 22 ms | 27.9 GB | `R_0 c99c4088…` → `R_n 4100fb37…` |

Both chains check (`leaf_chain.py`: `R_0`, `R_n`, `wsLen`, post root = oracle). For comparison
the M5b monolithic T1 proof was 1,476,227 B (seg-v1 parameters); the cut at the base
configuration is 963 kB for both proofs together, and each leaf verifies a ≈ 480 kB child.
T1 at its natural heights (`T1nat`): IF 482,746 B / seg 467,572 B. `--seg-cap 1500` cuts T2
into two STATE segments (chain consistent, `R_1 f121ccb6…`).
**Lane D's driver accepts the files:** `nearproof-chunk-e2e fs-count STATE.vk.json STATE.proof 0`
(the `pq-e2e-d9` build, read only) verifies all four.

**Mutants [M]** (`leaf_mutants.sh`, `logs/BT1-T1-mutants.txt`): **23 / 23 rejected** on T1 at S, every one with the full
prover (precheck failure, then the prover's refusal or the native verifier's rejection):
statement-level `postroot`, `wslen`, `nchange` (the `TCH` index), `ifr0` / `segrin` / `segrout`
(a depth-24 root public value), the M5a/M5b row tampers `node`, `prevalue`, `omitwrite`, `wsstale`,
`wssib`, `wsdrop`, `wsabsorb`, `wsleaf`, `stkbyte`, `stvbyte`, `stdrop`, `tbig`, `twrap`, and the new
`WSX` ones: `wsxzero` (another `Z_D`), `wsxlvl` (the extension one level short), `wsxroot` (another
incoming depth-`D` root: `RCH`), `wsxhash` (an extension step's output: the chip). The HOST-fed
segment (`--host`): `stkbyte`, `stvbyte`, `stdrop`, `omitwrite`, `segrout` **5 / 5 rejected**
(`HOSTB` / `HOSTQ` / `HOSTR` unbalanced).
Plus the cross-proof mix: T1's IF proof with T2's segment fails the chain (`R_0`, `R_n`, `wsLen`
mismatch) — the boundary equality the tree checks.

### Item 3: the state side of the M6 join [M][K]

Lane A's HOST chip (`wasm-base-lean/WasmBase/HostChip.lean`, read; m6/README §3 `HostIf`) sends
`HOSTQ` (208) `[ts, hid, S, np, (aLo, aHi) × 9]` and the request bytes on `HOSTB` (210)
`[ts, hid, dir, pos, byte]`, and receives `HOSTR` (209) `[ts, st, rLo, rHi, gLo, gHi, ar, 0]`; today
its oracle `HOSTO` answers them. **`StHostIf.lean`** (`m5a-tool tmpl-segh D`) is the segment
template with the STATE rows on those buses in place of `SREQ`/`HB`; every other table is the
same, so the working set cannot tell who fed it:

* `STWH` = `STW` + `S`, `rid`, `rlo/rhi/glo/ghi`: receives `HOSTQ [ts, 60 − 2·pr, S, 3 + 2·pr,
  klen, 0, kptr, 0, pr·vlen + (1 − pr)·rid, 0, pr·vptr, 0, pr·rid, 0, 0, …]` — `storage_write`
  (id 58, `key_len, key_ptr, value_len, value_ptr, register_id`) / `storage_remove` (id 60,
  `key_len, key_ptr, register_id`), lane A's ids (`hostStorageFns`) — and sends `HOSTR [ts, 0,
  rlo, rhi, glo, ghi, 1, 0]`; its `WRITE` carries `seg = 0` (one internal segment per proof, so the
  `WM` chain orders all of the segment's writes by `ts`);
* `STBH` = `STB` + a run-constant `hid ∈ {58, 60}`: receives `HOSTB [ts, hid, 0, base + j, b]`;
  the run's descriptor carries `hid`, which `STWH` matches to its request.

**Bus shape the state side needs from lane A (to coordinate; not edited here):** a
`storage_write` reads two buffers in one call, so a request byte must name its buffer. The state
side reads `HOSTB`'s 4th field as the **linear-memory address** `ptr + pos` (lane A's `memAddr`),
not the offset `pos` its `msg` carries today (the byte calls lane A has — `log_utf8`, …,
`value_return` — read one buffer, where the two differ by the constant `ptr`). Lane A's `HOSTO`
must stop answering storage calls in a joined trace (the state rows answer them).

**Not the state side's yet (M6.4):** the response values — the evicted-value flag needs the
entry's value before the write (the `WM` read `WSA` already makes) and `g_after` the host-side
state σ's gas; `rlo…ghi` are witness columns, a free oracle exactly as `HOSTO` is today.

**Measured [M]:** `tracegen.py --split --host` writes the segment dumps with a cached
`HOSTTAPE` standing in for lane A's rows (it sends `HOSTQ`/`HOSTB` and receives `HOSTR`, at lane
A's widths 22 / 5 / 8; `S = 0`, `register_id = 0`, `r` = 1 iff the key held a value). T1's segment proves at S on `m5tSegH`: 476,698 B, 39.8 s,
verify 29 ms, chain to the same IF proof OK (`logs/BT1-T1-SH-prove.log`).

**Lean [K]:** `m5tSegH_tables` (the template differs from `m5tSeg` only in the two STATE tables),
`stwH_hid` (id / argument count per call). The STATE rows' soundness on these buses (M5b's
`StSound.write_sent` with `HOSTQ`/`HOSTB` in place of `SREQ`/`HB`) is open [S]; the request
decoding is the same arithmetic.

### Lane E's T1 template system (main `1461c97f6`, merged): where the state proofs sit [S]

`E2E/Templates.lean` assigns lane B the **STATE** template: `MState (eng I c) (eng I c')` by
VM-free engine steps (`VFSteps`), obligation `SegSoundState V A Bad` (rows open both 42-B boundary
digests to such a pair), honest side `TmplComplete V A .state`; `mstate_trans` merges consecutive
STATE segments. How this session's proofs map onto it:

* **The STATE leaf's state component** is the `m5tSeg` proof: it moves `stRoot`'s working-set root
  `R_in → R_out` (depth 24, `wsRoot_ext`) by the segment's storage requests, with `wsLen` and the
  trie root unchanged. Which requests a VM-free engine step makes — and every other boundary
  field (position, gas, outcome / receipt accumulators) — are the runtime's rows (lane F, `m5t1`),
  not the state rows. So `SegSoundState` is a property of the **joined** STATE trace (engine rows
  + state rows on `SREQ`/`HB`), as `SegSoundWasm` is of the Wasm rows + the state rows on the
  HOST buses (item 3); lane B's part is the component statement "`stD (stOfK K c')` is `stD (stOfK
  K c)` with the run's requests applied to the overlay" — **not built** (it needs the
  per-template restatement of `StSound.write_sent` / `WsBus.seg_root` / `chain_sound` for
  `m5tSeg`, open above, and lane E's overlay semantics of a VM-free run).
* **`m5b_final`** concludes `applyChanges (some T) (sortKV (committedOf T reqs)) = some (some T')
  ∧ rootHash T' = post` — the spec's `Ovl.finalize` fold, i.e. the state root that **FINAL**
  (lane G, `SegSoundFinal`) outputs; the IF proof's FINAL half is that statement at `R_n`, and its
  INTAKE half is the `stRoot` the **INIT** leaf (lane G) publishes. Connecting `m5b_final` to
  `MFinal` needs lane G's FINAL relation (finalize as `CM` steps from `eng I ⟨.done out, _⟩`); not
  done this session.
* Proposal to lane E (the plan, §5.1): state lane B's STATE obligation as that component
  statement over `stD`, joined with lane F's engine obligation in one `SegSoundState`; and let the
  IF proof serve the INIT and FINAL leaves' `stRoot` / post-root fields.

### Open after B-T1

1. Lean: `WSX` at field level; the per-template soundness theorems (`m5tIF`, `m5tSeg`, `m5tSegH`)
   restated from the M5b ones; a composition statement (IF ∧ segments ∧ matching public roots ⇒
   the M5b conclusion).
2. M6.4: the `HOSTR` answer (evicted-value flag from the `WM` read, `g_after` from the host-side
   state σ), reads (`storage_read`/`has_key` + register fill bytes), and lane A's `HOSTB` address
   field (above).
3. Item 4 (completeness, census order): squash onto an extension sibling (M5a-8 design `RK_XD`),
   the old-leaf-ends split, `VBITS` 7 → 9 — not started this session.
4. A production class set per lane D's leaf geometry (one setup per leaf-geometry family), and the
   IF / seg split if lane D prefers single-use proofs.

## M5a-9 (tenth session, 2026-11-03 … 11-21): corpus coverage census; extraction fix

Log `docs/logs/e2e-m5a9-state-2026-11-21.md`. **No AIR change, no Lean change** this session (the
session was paused by a usage limit). Item 3 (census) is done. Items 1 (branch-end split), 2 (`STB`
packing) and 4 are **not built**. The census re-ranks them below.

### Corpus census [M] (`census.py`, `logs/M5a9-census*.{jsonl,txt}`)

All 19,007 `d3` cases of `d3c7`–`d3c10` (M5b AIR at `61d19af1f`, `D` = smallest with
`2^D ≥ |working set|`). Every case is Lean-accepted and changes state in its main transition.
Pipeline: Lean `--emit-full`, `extract_state.py` (with the fix below), `tracegen.py`, then the
prover's `check` (every constraint on every row, every bus balanced). 57 min wall on 8 workers.

| outcome (first failure) | cases | share |
|---|---|---|
| **OK** (tracegen + `check`) | **16,205** | **85.26 %** |
| squash onto an extension sibling | 1,074 | 5.65 % |
| split, old leaf's key ends at the branch (`splitLeaf.oldEnds`: `alice` exists, `alice.near` inserted) | 691 | 3.64 % |
| squash to a value leaf (`squash.valueLeaf`; never `squash.empty`) | 353 | 1.86 % |
| `VBITS = 7`: a node with ≥ 128 version readers (working set ≥ 128 keys) | 301 | 1.58 % |
| squash onto a branch sibling | 214 | 1.13 % |
| squash after a branch-value delete | 146 | 0.77 % |
| split, written key ends inside a leaf (`splitLeaf.newEnds`) | 23 | 0.12 % |

* **No `CHECKFAIL`, no tracegen error** besides `VBITS`. Every trace that generates satisfies every
  constraint and balances every bus.
* **Prove sample:** 15 OK cases spread by size all verify (native verifier and statement check).
  Proofs run from 1,096,701 B (4 keys, D = 2, 7.6 s) and 1.46–1.49 MB (D = 4–5, 45–71 s) to
  1,858,489 B (125 keys, D = 7, 50 M cells, 480 s, 18.2 GB RSS). Roots are in the summary file.
* **Every gap per case** (a fault-tolerant pass that continues past each unsupported walk): of the
  2,501 UNSUPPORTED cases, 1,982 need one shape, 470 two, 45 three, 4 four. Also found: "long
  extension key under a delete" (2 cases). Walk occurrences: delete / squash onto an extension
  sibling 3,624, onto a branch sibling 954, upsert / old-leaf-ends split 847, squash to a value
  leaf 370.
* **Priority from the census** (greedy, cases fully unlocked by each step): squash onto an
  extension sibling +808 → 89.5 %; old-leaf-ends split +586 → 92.6 %; `VBITS` +424 → 94.8 %; squash
  onto a branch sibling +436 → 97.1 %; squash to a value leaf +367 → 99.05 %; squash after a
  branch-value delete +154 → 99.86 %; written-key-ends split +25; long extension under a delete +2
  → 100 %. The "key ends at the branch" split ranks 2nd (mostly the *old* key ends). The "written
  key ends" direction and the extension `newEnds` case are rare. The squash family (designed in
  M5a-8, `RK_XD`) is the most frequent gap.
* **`VBITS`:** the root is read by every walk, so a working set of N keys gives it about N readers.
  680 cases (3.6 %) have ≥ 128 keys; no case with ≥ 128 keys passes today. Widening `vm`/`vmn` is an
  AIR change (more bit columns). The Lean proofs should need only small changes, since they use
  only the bit decomposition (not checked).
* **Distributions** (all state cases, OK cases in brackets): keys p50 23 (22), p90 56 (39), p99
  541 (103). `D` mostly 4–6 (`{4: 3,106, 5: 11,636, 6: 2,771}`), up to 11. Transitions per case:
  `{1: 17,353, 2: 1,352, 3: 140, 4: 135, …}`. 2,156 implicit transitions with changes, each 2 keys
  and 1 change, all trace OK (tracegen only). For item 2: `STB` rows on OK cases p50 1,558, p90 3,735,
  p99 10,864, max 21,008 (height 2^11 for 9,080 cases, 2^12 for 3,285, up to 2^15). `HTAPE`
  heights are nearly identical. Packing 4 bytes per `STB` row would cut its height by two powers of
  two on most cases.

### `extract_state.py` fix [M]

Witness nodes that the clean-room checker first reads *during finalize* were dropped: it skipped
every read once `update` began. These are mostly squash siblings no find walk touched. tracegen
then saw an unrevealed (`hash`) sibling. Pre-state nodes read during finalize are now recorded.
Effect: 1,682 cases. 1,171 go from "squash onto a hash sibling" to OK; the rest go to their real
gap shape. T1 is unchanged (48 nodes; same trace). Checked on `d3c7/00-h10026-s0`: tracegen ok,
`check` PRECHECK OK.

### Timestamps per boundary (lane E's `idxOf = 0`) [M]

A tracegen copy restarted the write time `t` at 1 in every segment. T2 (D = 6, 5 extra writes)
with `--segs 3` and with `--segs 47`: `check` PRECHECK OK for both. In the second run, one key is
written in segments 0 and 1, both at `t = 1`. So the working-set side (`WRITE(seg, t, …)`, `WSA`,
the `WM` chain, `RCH`) accepts per-boundary restarts. The M5b STATE rows key the execution bytes
`HB(ts, pos, b)` by `ts` alone. A restart is therefore safe in one proof per segment. One proof
spanning boundaries would need `seg` added to `HB` (an AIR change, not made); `StHost.MemAgree` is
stated per `(ts, pos)`.

### Lane E `FitsReach` → `stOfK`; lane D leaf requirements [S]

* `StateViewParams.FitsReach` uses `stOf c = stOfK [] c` (empty key list): unprovable for real runs
  (lane E's `fitsB` counterexample). The intended statement is lane E's `FitsReachK κ R` (`StViewE`,
  main `7358a938d`). `stOfK` is defined in `spec/lean/v3/NearSpecV3/E2E/StEnc.lean` on that main,
  not on this branch's base (`61d19af1f`). The switch replaces the definition once lane B is rebased
  onto that main (`FitsReach` is not used by `m5b_final`). Not done here (no merge on lane branches).
* Lane D tree leaf (next milestone; costs estimated, not measured): (1) pinned shape — pad every
  table to a template height (e.g. `STB` 2^12, SHA-512 2^16, `D` ≤ 7 covers 99 %; the proof costs
  the template's size, ≈ 1.5–1.9 MB at today's AIR); (2) roots in the statement — the `TCH` ends
  (`prev/post_state_root`) are already public inputs; `HTAPE` goes once lane A's `HOST` rows feed
  `HB`/`SREQ`, or becomes a committed public table; (3) fixed-shape segments — `RCH` already chains
  segments (`WsSeg.ws_compose`), and timestamps can restart (above); the walks need a per-segment
  cut (M-sized); (4) proof + vk to disk — a prover change only (S).

### Open after M5a-9

1. Completeness, by census frequency: squash onto an extension / branch sibling (M5a-8 design
   `RK_XD`), the old-leaf-ends split (M5a-8 design: `oLX` with `mL`, `oSL` with a value and one
   child), `VBITS` 7 → 9, squash to a value leaf, squash after a branch-value delete, the rare
   `newEnds` splits, a long extension under a delete.
2. `STB`/`HTAPE` packing (item 2; the census heights above).
3. `FitsReach` → `FitsReachK` after the rebase; `seg` in `HB` if one proof spans boundaries.
4. Lane D leaf requirements (above), `HostReqs` from lane A's `HOST` rows, reads.

## M5a-8 (ninth session, 2026-11-03): continued keys from `Holds`, keys up to 2 KiB, `SHAS` merged

Log `docs/logs/e2e-m5a8-state-2026-11-03.md`. **AIR change** (`SN` column `hph`, `STW` flag `ke`,
`SHAS` merged into the SHA-256 table); every case re-proved, roots = Lean oracle
(`logs/M5a8-proofs.txt`), 121 mutant runs: 119 rejected, 2 not applicable (`logs/M5a8-mutants.txt`).
Lean: `lake build StateM5a m5a-tool` green (379 jobs), std axioms only (`Audit.lean`).

### Headline [K]: `M5bFinal.m5b_final` without continued-key premises

Premises now: `HostOK`, `Holds` of the M5b prover AIR, `CompressOK`, the SHA-512 chip contract,
`1 ≤ D ≤ 20`, the named CR (`NodeCR`, `LeafCR`, `Sha256CR`), the producer premise `HostReqs`,
`n < p`, `|prev| = |post| = 32`, and the pre-state facts (`T.hashOf = prev`, `Full T ∧ T.wf`).
`SnFreshLong`, `SnContRest`, `hlongS`, `hlongM` are discharged (sub-agent C):

* `SnContKey1..5`: a continued head hashing a node has a key `K` (`klen = 62 + odd + rl` nibbles,
  all `< 16`) whose record is `Hashed` to its digest; its first `62 + odd` nibbles are the head's
  cells (`hpDec_head`, pure); every `SNC` chunk `c + 1` of head `r` has `p = d + 62 + odd + 64c`,
  `kA = kid`, `fA = 1 − gA`, `kB = kid2`, `gB = g2` (`snc_kc`, induction over the `KC` chain); the
  message bytes at `37 + i` are the chunks' `hp_m` (`cont_msg_snc`, `Sha256CR`); so with `gA = 0`,
  `K = K_kid[d .. d + klen)` (`cont_key`), with `g2 = 1` also `K_kid2[…]`; `cont_old` / `cont_new`
  are `OldOK` / `NewOK` over `K`, `cont_leaf_nmem` the new leaf's memory `< p`.
* `SnContResp`: `hlongS_of`, `hlongM_of`, `snFreshLong_of`; `SnContLocA/B/X`: every walk op over the
  full key (`cont_mismatch`: `ajm = 1` puts the mismatch in the head, `mL·cont = 0`);
  `SnContRestAll.snContRest_of`; `SnFinal6.air_final_sorted_sn6` (new static premise `hrK`, no extra
  table touches `KCR`, discharged in `M5bFinal`).
* **`StHost.m5b_final_tape`** (item 5): on the T1 tape of a request list (`hostOf reqs`, what
  `tracegen.py` writes), `HostReqs` holds for every trace given `MemAgree` (two `HB` entries at the
  same `(ts, pos)` agree), bounds `< p` and `(seg, ts)` order of the public list
  (`hostReqs_of_tape`) — so the producer premise is a check of public data on T1, not vacuous.

### u32 hex-prefix length and the empty key (item 2) [M][K]

The `SN` head sent `u32 |hp|` as `(hplen, 0, 0, 0)`, so node keys of more than ~509 nibbles could
not be proved. Now `(hplen − 256·hph, hph, 0, 0)` with a new column `hph`, both bytes checked by the
SHA-256 table, and `(1 − cont)·hph = 0`. Lean: `SnSer.sn_hph0` (a head-only key has `hph = 0`, so
`sn_ser_ok` is unchanged), `SnContRec2.u32_split` (`lo = H − 256·hi` in the field with `lo, hi`
bytes and `H < 2^27` gives `H = lo + 256·hi < 2^16`), `cont_node` (`serC` head
`[tag, H % 256, H / 256, 0, 0]`), `SnRec.u32_mid`, `grecK_hashed`. `STW` gets `ke` (`ke·klen = 0`,
`ke·(dk − sha256 [])`, the key's `DESC` / digest receives gated by `act − ke`): an empty key needs no
`STB` run (`StSound.stw_key`). New synthetic case **`synth.py longkey`**: keys of 1,006–2,046 bytes
(NEAR's 2 KiB storage keys), node keys up to 4,088 nibbles (`hplen` 2,045, `hph` 7), 571 `SNC` rows;
a long leaf replaced, split near its head (`oLX`), deleted with its sibling leaf squashed, a long
extension descended, finds: root `ed9f4baf…0f22` = Lean oracle, **proof 1,266,342 B**, 71 s.
Mutants `hphshort`, `hphlong`, `kempty` (and `chain` on a 2 KiB key) rejected.

### `SHAS` merged into the SHA-256 table (item 3) [M][K]

`STB` sends `SHA_BYTES(ID_ST + m, j, b)` and `STW` receives `SHA_DIGEST` of the M5a SHA-256 table;
`SHAS`, `SB2`, `SD2` removed. Lean (sub-agent S): `KeyDigest.XSbHi` — every `SHA_BYTES` message an
extra table sends carries an id `≥ ID_ST` — replaces "extras never send on `SHA_BYTES`" in every
signature (`xsbHi_of_silent`; `sender_set_hi`; `sender_lo` at the four roots, whose ids are below
`ID_ST`; `m5a_sb_lo`: `KEY`/`BR`/`SN`/`SNC` ids `< ID_ST`); `FinalOrder.Prem.hxB` from `Holds`
(`M5b.x_hxB`); `StSound.sb_sent_hi` / `sd_sent` / `desc_msg` over the merged table. Tooling
auto-detects the merged AIR (no `SHAS` in the names JSON → STATE messages in `sha_msgs.json`;
prover `NAMES_B8`).

| M5b T1 | proof | relations | whir |
|---|---|---|---|
| M5a-7 (`SHAS`) | 1,526,081 B | 330,180 | 1,161,664 |
| `hph` + `ke`, before the merge | 1,531,265 B | 330,324 | 1,166,704 |
| **final** (`n18 w9`) | **1,476,227 B** | 277,996 | 1,164,054 |
| M5a T1 (no STATE rows) | 1,237,850 B | 273,744 | 930,060 |

The merge saves ~50 kB (the `SHAS` openings; the main table stays at 2^12 rows, the STATE messages
fit its padding). The remaining +238 kB over M5a T1 is `whir` on the `STB` / `HTAPE` tables (2^11
rows each) — the next lever (pack several bytes per `STB` row; `HTAPE` is T1-only).

### Item 4 (completeness gaps): scoped, not built [S]

Both sub-agents designed one gap each and judged it several sessions of Lean (new `UChain` /
`DChain` constructors and their ~100 case sites), so nothing was built:

* *split where a key ends at the new branch* (`alice` vs `alice.near`): `oLX`/`oEX` with the
  existing `mK` (walk key ends) / `mL` (old leaf ends) mismatch kinds, `oSL` with a value
  (`nhv = mK + mL`) and one child, value from the walk or the old leaf via `SPQ`;
* *squash onto an extension / branch sibling, squash after a branch-value delete*: result kind
  `RK_XD` (extension descriptor) beside `RK_LD`, sibling reads `SN.oXS` / `BR.oBS`, `BR.oDX` +
  `SN.oXM` to materialize, `SN.oED` merging an `XD` child. Fixture `synth.py squashx` (spec oracle =
  transcription `419b6589…2dc9c4`; tracegen: `Unsupported: squash onto a ext sibling`).

### Open after M5a-8

1. Completeness gaps: the two designs above; a mismatch past the head's first `62 + odd` nibbles;
   a long extension key under a delete (`retag_sn`); a final node over an in-memory child of a
   continued key; an empty trie / empty *trie* key (the `KEY` table has no 0-byte key; `ke` covers
   the STATE rows); node keys over ~65,000 nibbles (`memChain` limb `< 2^17`; NEAR's are ~4,100).
2. `HostReqs` from lane A's `HOST` rows and memory argument (on T1: `StHost`, a check of the tape).
3. Reads (`storage_read`/`has_key`) — design only (§M5b).
4. M5b size: `whir` on `STB`/`HTAPE` (+234 kB over M5a T1).
5. Lane E `StViewE`.

## M5a-7 (eighth session, 2026-11-03): split rows compiled, every short-key and memory premise from `Holds`, STATE rows sound, M5b end to end

Log `docs/logs/e2e-m5a7-state-2026-11-03.md`. **No AIR change** this session (the AIR, the
exported `m5a.json` / `m5b` AIR and every root are those of M5a-6 / M5b; nothing to re-prove).
Lean: `lake build StateM5a m5a-tool` green, std axioms only (`Audit.lean` prints every new
headline), every module compiles in seconds under 1 GB.

### Headline [K]: `M5bFinal.m5b_final` — the M5b AIR end to end

From `Holds` of the AIR the prover runs for M5b (`fullAir D (m5bX host prev post n)`: M5a tables,
STATE rows `SHAS`/`STB`/`STW`, the public tape), the semantic premises of `M5b.prem` (chip
contract, `CompressOK`, `NodeCR`, `LeafCR`, `Sha256CR`, `1 ≤ D ≤ 20`), the named producer premise
`StSound.HostReqs` (below) and the **continued-key premises** (`SnFreshLong`, `SnContRest`,
`hlongS`, `hlongM`):

```
∃ T', applyChanges (some T) (sortKV (committedOf T reqs)) = some (some T') ∧ rootHash (some T') = post
```

where `committedOf T reqs = ((reqs.foldl Req.apply (Ovl.ofTrie T)).commit).committed` is the
**spec's own overlay** (`NearSpecV3.D2.State`: nearcore's `TrieUpdate` set / remove / commit) of the
execution's storage requests. Pieces:

| piece | statement | module |
|---|---|---|
| STATE rows sound | every `WRITE` an `STW` row sends is `(seg, ts, pack2 (sha256 key), pr, |v|, pack2 dv)` for an `SREQ (ts, pr, seg, klen, kptr, vlen, vptr)` and the bytes `key` / `val` carried by `HB (ts, kptr + j, key[j])` (`dv = sha256 val`, `sha256 []` for an empty value, `0` for a remove); bytes `< 256` from `SHAS`'s own contract; `ID_ST + m` does not wrap (`m ≤ row < 2^20`) | `StSound` (`write_sent`, `write_recv`, `stw_row`, `desc_msg`; `StSoundA/B/E`) |
| `committed ~ cs` | `final_changes_m5b`: `∃ cs, |cs| = |wrRows| ∧ FinalChanges cs ∧ (committedOf T reqs).Perm cs` | `StSoundW`, `StSoundF1/F2/F3`, `StSoundF` |
| split rows | `oLX`/`oEX` at `cont = 0` `LocalOK` | `SnSplit*` |
| memory limbs | `SnUpLimbs`, `SnMatLimbs`, `OslNodeLimbs`, `oEP`/`oEM` `unm` (and `SnContMem` for continued keys) | `SnLimbsAll`, `SnFreshLimbs`, `SnCont*` |
| assembly | `SnFinal5.air_final_sorted_sn5`: `air_final_sorted_sn4` with all of the above discharged | `SnFinal5` |

**`HostReqs`** (premise, the producer side; lane A's memory argument on the full AIR): the host only
sends; the `SREQ` messages sent are exactly `reqs`' messages; there is `mem : Fp → Fp → Fp` with
every `HB` sent `= (ts, p, mem ts p)` and each request's key / value bytes read from it; `ts`, `seg`,
lengths `< p`; requests in strictly increasing `(seg, ts)` order. Honest T1 satisfies it (the
public `HTAPE` has one `SREQ` per executed request, its `HB` entries are the call's memory bytes,
`ts < 2^24`, segments are consecutive chunks of execution). `reqs` must be the committed requests
in execution order (one commit of all = commit per receipt).

### Split rows: why `SnSplit` needed > 24 GB, and the fix

The memory went to `omega` on goals whose atoms are `ev tr 3 r pub (Sn.c "…")` (string-indexed
column lookups): `fresh_flags` (~25 flag atoms, a disjunction, 6 goals) alone exceeded 12 GB and
was killed at 16 / 20 GB (`omega`'s atom comparison unfolds the column lookups). Stating the
arithmetic over plain naturals (`SnFresh.fresh_arith`, `SnLimbsAll.gnew_arith`, a small
`gX_of_split`) and applying it to the hypotheses makes the file compile in about a second. The
M5a-6 `lean-wip/` files are now modules (`lean-wip/` removed): `SnFresh` (`FreshRel`, `fresh_short`),
`SnSplitHop` (`SPR` decoding, `gX_of` re-proved, `osl_of_split`, `ep_of_split`), `SnSplit`
(`split_ans`), `SnSplitKeys` (`split_keys`, `split_row`), `SnSplitLX` (`localOK_oLX`), `SnSplitEXA`
(`ex_mem`), `SnSplitEX` (`localOK_oEX`); the never-compiled proofs needed small repairs (missing
`RowBrN` open, `bE`/`E` abbreviations under `rw`, metavariables in `memChain_sound`'s bounds,
`gX_of`'s field arithmetic).

### Memory limbs from `Holds` [K]

* `SnLimbsAll.snUpLimbs_of` / `snMatLimbs_of`: `UP` positions `20..23` are `gnu·NM + gX·sm` (a new
  node's limbs; a split row's `sm` = its `SPR` sender's new memory: `oSL` `BR` `NM` or `oEP` `SN`
  `NM`), `24..27` are `(mU + mD)·M`; `MATR` is the `oLM` row's new memory.
* `SnFreshLimbs`: `oslNodeLimbs_of` (`nm2 = xm` over a node: `0` on a leaf split, the
  extension's child memory `CM` (`cmb` in `RNG`) or the re-keyed extension's `sxm` = an `oEM` row's
  `NM`), `oep_unm_lt` (`SPR`), `oem_unm_lt` (`SXQ`: the split row's `CM`), `snFreshNew_of`.
* `SnCont*` (sub-agent): `snContMem_of` — the continued keys' memory limbs. A continued head is
  always hashed; its SHA-256 message has length `serLen`, `SNC` chunk bytes land at
  `5 + 32c + m < 5 + hplen` (never on payload / memory positions), so the memory bytes are message
  bytes `< 256`. Modules `SnContHead` (head facts: `a_j`, `ha_m = [m < 32]`, `hplen = 32 + rl/2`),
  `SnContChain` (`SNC` chunk shape, `snc_head`: every active chunk belongs to a continued head
  whose `rl` it determines, from "sent `KCR` ⇒ received"), `SnContByte` (`cont_byte`: who sends a
  byte under an `SN` id), `SnContSer`, `SnContMem` (`cont_msg`), `SnContLimbs`. New static premise
  `hxRr` (no extra table touches `KCR`; true of the tape and the STATE tables).

### Continued keys: full-key records [K], row relations left [S]

For `cont = 1` rows the decoder's `snKey` (and so `snOld` / `snNew` / `gRecS`) reads `Sn.c "k" j` for
`j < klen` with `klen = 62 + odd + rl > 64`, i.e. columns past the 64 head nibbles, so the internal
records of a continued row need the full key. `snRow` itself (`din`/`dout`/`uin`/`uout`) carries no
key, so `SnContRest` as stated is the right target. Done (sub-agent, `SnContSer2`, `SnContRec1..4`):

* `SnContRec2.cont_node`: a continued head's digest is `sha256 ([3·isE, hplen, 0, 0, 0] ++ hp₀..₃₁ ++ M
  ++ payload ++ memory)` with `M` the `SNC` part, every entry a byte, `hplen < 256`;
* `SnContRec3.grecK_hashed`: the record over the decoded key (`hexPrefix` of the decoded nibbles) is
  `Hashed`; `snOldC` / `snNewC` = the record over `ckey` (a key of length `2(hplen − 1) + odd`,
  nibbles `< 16`, whose record is hashed to the head's digest; exists by `cont_old_key` /
  `cont_new_key`);
* **`SnContRec4.cont_oldOK` / `cont_newOK`**: `OldOK σ (snIn r) (snOldC r)` / `NewOK σ (snOut r)
  (snNewC r)` for every continued row with an old / new node — no CR needed.

Left: (i) `ckey`'s link to the walk key (its first `62 + odd` nibbles are the head's `k_j` — a
pure `hp_m` lemma; its later nibbles are an `SNC` row's `k_i`, whose position / key id / lookup flag
the `KC` chain forces, so its `NIB` lookups tie them to `keyOf kid`); (ii) the `LocalOK` cases over
`snOldC` / `snNewC` (`SnContRest`); (iii) `hlongS` / `hlongM`, `SnFreshLong`. None of these
premises is used on T1 / T2 / the synthetic cases (no key longer than the head there).
**New completeness gap:** the head serializes the u32 hex-prefix length as `(hplen, 0, 0, 0)`, so
`hplen < 256`: keys longer than ~509 nibbles (≈ 254 bytes) cannot be proved; NEAR contract-data
keys go up to 2 KiB.

### Tooling (item 4) [M]

`tracegen.py`: a tamper with no target row in the trace (e.g. `vbyte` needs a version-published
`SN` leaf; synthetic `bval` has none) now prints `NOT APPLICABLE` and exits 3; `run.sh` reports it
and continues the battery (before: `StopIteration`, the battery aborted). `logs/M5a7-mutants-tooling.txt`.

### The +287 kB of the M5b proof (item 3, "tune if cheap") [M]

Prover overrides `N_STACK` / `W_STACK` (env; unset = the old rule). M5b T1
(`logs/M5a7-stacking-sweep.txt`): default `n 18, w 10` 1,526,081 B; `w 12` 1,530,407 B (+4 kB);
`n 22, w 8` 1,897,033 B (359 s). So the jump is **not** the stacking width: against M5a-6 T1 the
proof gains `relations` +57 kB (the 544-column `SHAS` table's openings) and `whir` +231 kB with the
four extra tables. The lever is fewer tables — `SHAS` merged into the first SHA-256 table (the
id-space generalization of `KeyDigest.sb_only` etc.), `STB`/`STW` folded — not cheap; left open.

### Open after M5a-7

1. Continued keys: `ckey` ↔ walk key (head and `SNC` lookups), then `SnContRest`,
   `hlongS`/`hlongM`, `SnFreshLong` (the full-key records `cont_oldOK` / `cont_newOK` are done).
2. `HostReqs` from lane A's `HOST` rows and memory argument (on T1 a statement about the public tape).
3. Reads (`storage_read`/`has_key`: `WM` read access, value bytes back) — design only (§M5b).
4. `SHAS` merged into the SHA-256 table (the +287 kB above).
5. Completeness gaps: keys longer than ~254 bytes (`hplen < 256`, new), empty key (`klen = 0`: no
   `STB` run, so no `DESC(mk, ts, kptr, 0)`), an empty
   value must use `ve = 1`; a mismatch past the head's first 63 nibbles (known); lane E `StViewE`.

## M5b (first STATE rows, 2026-11-03): writes produced from raw key / value bytes

Until now the working-set writes `WRITE(seg, t, kd16, present, len, vh16)` (received by `WSA`) came
from the public tape with the digests precomputed. M5b produces them from execution-side messages
carrying the **raw trie key and value bytes**; `kd = sha256 key` and `vh = sha256 value` are
computed in-circuit and `t` is the request's timestamp. Lean: `lean/StateM5a/St.lean` (AIR),
`M5b.lean` (which theorems apply); `m5a-tool airb D` exports the M5b AIR, `M5B=1 run.sh …` runs it.

### Design [S] (implemented for writes and removes on T1 [M])

**Execution-side interface** (the shape of lane A's host buses, plan §3.3; on T1 the public tape
`HTAPE` sends them, later lane A's `HOST` rows / the receipt-action rows):

* `SREQ [ts, pr, seg, klen, kptr, vlen, vptr]` — `storage_write` (`pr = 1`) / `storage_remove`
  (`pr = 0`, `vlen = 0`) at time `ts`, in NEAR's argument order (key length / pointer, value
  length / pointer). In lane A's form this is `HOSTQ [ts, hid, S, args…]` with `pr` from `hid` and
  `seg` the segment's own index (a constant of the STATE segment).
* `HB [ts, pos, byte]` — a byte call `ts` read at linear-memory address `pos`: exactly lane A's
  `HOSTB`. The execution side sends, the STATE rows receive; the producer side assumes memory is a
  function of `(ts, pos)` (one byte per address and call — lane A's memory argument).

**STATE rows:**

| table | rows | role | w / c / i |
|---|---|---|---|
| `STB` | one per message byte | runs, one per message `m = 0, 1, …` (consecutive: each `m` has exactly one run), `j = 0, 1, …` in a run, `ts`/`base` constant on a run; sends `SB2(ID_ST + m, j, b)` to the SHA-256 instance, receives `HB(ts, base + j, b)`; the run's last row sends `DESC(m, ts, base, j + 1)` | 7 / 15 / 3 |
| `STW` | one per write | receives `SREQ`, `DESC(mk, ts, kptr, klen)` + `SD2(ID_ST + mk, klen, dk)`, for a non-empty value `DESC(mv, ts, vptr, vlen)` + `SD2(ID_ST + mv, vlen, dv)` (empty value: `ve = 1`, `dv = sha256 []`; remove: `dv = 0`), sends `WRITE(seg, ts, pack2 dk, pr, vlen, pack2 dv)` | 75 / 77 / 6 |
| `SHAS` | per SHA-256 block | a **second instance** of the unchanged SHA-256 table (`ZkFormal.Sha.Table.table B_SB2 B_SD2`) | 544 / 1028 / 17 |

**Id spaces.** `STB` messages hash under `ID_ST + m` (`ID_ST = 4·2^24`, disjoint from `KEY`/`BR`/
`SN`) in their own SHA-256 instance on their own bus pair (`SB2`/`SD2`). The second instance is
what keeps every M5a theorem applicable unchanged: their premises forbid extra tables from sending
on `SHA_BYTES`/`SHA_DIGEST` (the id-space lemmas `KeyDigest.sb_only`, `br_byte`, `key_byte`, … rely
on the known senders). Merging into one table (saves its padding) needs those lemmas generalized to
"extra senders use ids `≥ ID_ST`" — a mechanical but wide change, left for later.

**Time discipline.** `t` = the execution side's `ts` (the Wasm step counter, segment-local
`< 2^24` per plan §3.2), prover-chosen but checked: `WSA` ranges it (`t < 2^24`, M5a-6) and each
entry's `WM` chain orders its accesses (`idp < t`, distinct times). Accesses to different keys need
no order between them. Within a call all bytes carry the call's `ts`.

**storage_read / has_key (design only).** A read is a `WM` access that consumes the entry's latest
value and sends it back unchanged at the read's `ts` (a `WSA` row with `new = old`, `wr` unchanged);
the reader gets `(present, len, vh)`. Returning the **value bytes** (to a register) needs the bytes
themselves, not the digest: the STATE row re-hashes the bytes the execution side receives
(`HB`-style bytes sent by the state side, hashed in `SHAS`, digest = the `WM` value's `vh`) — the
same `STB` machinery in the other direction. `storage_write`'s evicted-value return and
`storage_has_key` are the same read access.

**Cost per write** [M, T1]: 10 writes (7 values, 3 removes), 17 messages, 1,356 bytes (keys 1–49 B,
values up to 901 B), 35 SHA-256 blocks. Used cells ≈ 35.7 k per write: `SHAS` 17 rows × 544 per
block plus one 544-cell row per message (≈ 145 cells per byte with the padding block), `STB`
7 per byte, `STW` 75 per write (the execution side's `HTAPE` 10 per byte, public). Committed
(padded) cells 5,152,964 → 5,745,492 (+592.5 k, `SHAS` 2^10 rows). With `SHAS` merged into the
first SHA table the padding share goes away; the per-byte SHA-256 cost (~145 cells) is the floor.

### Results on T1 [M]

| | T1 (M5a-6 AIR, public `WRITE` tape) | T1 (M5b AIR, STATE rows) |
|---|---|---|
| committed cells | 5,152,964 | 5,745,492 |
| proof (268.2-bit) | 1,238,006 B | 1,526,081 B (stacking width 9 → 10) |
| prove / verify / peak RSS | 78 s / 97 ms / 1.29 GB | 80 s / 221 ms / 1.59 GB |
| root (= `m5a-tool apply`) | `1db48e38…249628` | `1db48e38…249628` |

The proof grows by 287 kB because the extra tables push the stacked commitment past a width
threshold (`w_stack` 9 → 10); not tuned. Mutants (`logs/M5b-mutants.txt`): **9/9 rejected** —
`stkbyte` / `stvbyte` (one key / value byte changed in `STB`, the SHA message and `STW` digest
recomputed: `HB` and `WRITE` unbalanced), `stdrop` (a requested write left out of the STATE rows:
`SREQ`, `HB`, `WRITE`), and on the M5b AIR `omitwrite`, `postroot`, `prevalue`, `wsstale`, `tbig`
(request and access at time `2^24`, consistently on the execution side: `RNG`), `twrap` (the new
`WSA` constraint). Logs `logs/M5b-T1-prove.log`, `M5b-T1-stats.json`; hashes `SHA256SUMS-v6`.

### Lean [K] (std axioms; `lake build StateM5a` green)

* `St.lean`: `Stb`, `Stw`, `shaTableS`, `m5bAir D = (m5aAir D).tables ++ m5bExtra` (exported by
  `airb`).
* `M5b.lean`: the prover's M5b AIR is `fullAir D (m5bX host prev post n)` (+ the native chip, as
  in `ChipStub`): the M5a tables, the M5a tape with **no writes** (`m5aTape [] prev post n`),
  `SHAS`/`STB`/`STW`, and the execution side's tape `tapeTable host` (`HostOK`: `SREQ`/`HB` entries;
  the prover's `HTAPE`). `x_buses`/`rest_buses`: these tables use only `TCH`, `SB2`, `SD2`, `SREQ`,
  `HB`, `DESC`, `WRITE`, so every static premise the M5a theorems put on extra tables holds
  (`x_hx`, `x_hsil`, `x_hxV`, `rest_hr`, `rest_hrN`, `rest_hrS`), and **`M5b.prem`** builds
  `FinalOrder.Prem` from `Holds` of the M5b AIR plus the semantic premises. Hence
  `WsEntries.ws_entries`, `FinalOrder.air_final_sorted`, `SnResp.air_final_sorted_sn2` etc. apply to
  the AIR the prover runs, with `writes := []`, `rest := m5bRest host`.
* **What they say about the new rows:** nothing beyond what they say for any `WRITE` producer — the
  working set (`ws_entries`: every FINAL leaf is its INTAKE entry with its latest `WRITE`) and the
  trie (`air_final_sorted*`) are proved from the `WRITE` messages whoever sends them. **Open:** the
  new rows' own soundness — that every `WRITE` an `STW` row sends is `(pack2 (sha256 key), pr, |v|,
  pack2 (sha256 v))` for the key / value bytes `HB` carried for its request (`SHAS`'s digest
  contract `sha_digest_contract_closed` on the second instance, single run per message id from the
  `STB` transition constraints, `DESC` balance) — and with it `committed ~ cs` (overlay ↔ writes).

### Open after M5a-6 / M5b

1. The STATE rows' soundness theorem (above), then `committed ~ cs`.
2. `SHAS` merged into the first SHA-256 table (generalize the `SHA_BYTES` id-space premises).
3. Reads (`storage_read`/`has_key`, `WM` read access + value bytes back), registers, the `HOSTQ`
   form with `hid`; the segment cut (`seg` = segment-local constant, `RCH` in the boundary).
4. Of *Open after M5a-5*: item 3 done (`WSA` times ranged); item 2 done (`OslApart`, `hVl`,
   `hVP`); item 1 partly done (`SN` records, `Hashed`, limb ranges at `cont = 0`, see the M5a-6
   Lean section). Left of `air_final_sorted_sn4`'s premises:
   * `SnRest2`: split rows (`lean-wip/SnSplit*.lean`: split `SnSplit` into lemmas that fit the
     24 GB budget, compile `SnSplitLoc`/`SnFinal3`; residual premises there: `unm` limbs of
     `oEP`/`oEM`, `OslNodeLimbs`) and continued-key rows (`cont = 1`: a full-key record over the
     `SNC` chain, its SHA argument with the `SNC` byte positions, then `LocalOK`, `hlongS`/`hlongM`);
   * `SnUpLimbs` / `SnMatLimbs`: from `SnRange` at `cont = 0` plus the split rows' `sm` (`SPR`
     senders: `BR` `oSL` / `SN` `oEP` new-node limbs) and the continued-key rows' limbs;
   * items 4–6 of M5a-5 (`committed ~ cs`, lane E's `StViewE`, completeness gaps) unchanged.

## M5a-6 (seventh session, 2026-11-03): two range checks, re-proved

### AIR changes [M][K]

| change | why | constraint / lookup |
|---|---|---|
| `BR`: version-published value-length bytes `nvl` in `RNG` (gate `nref`; commit 7e176cb9a) | a kept branch value copies `vl`, which a `VER` reader holds only as two 16-bit limbs; a non-byte cell with the same limb (`vl₀ + 256`, `vl₁ − 1 mod P`) passed every other check of an unhashed node | `RNG [nvl t]`, `t < 4`, multiplicity `nref` |
| `WSA`: the access time `t` is 3 bytes | before M5b makes times prover-chosen: the gap bytes give `idp < t` only for times `< 2^24`, and with a free `t` a closed `WM` cycle of ~120 accesses whose gaps sum to `0 mod P` balances on its own | `act·(t − Σ 256^k tb_k) = 0`, `RNG [tb_k]` |

Lean [K]: `WsCost.wsa_t_lt` (field level: bytes ⇒ `t < 2^24`), `WsDecode3.wsa_t_rng` (from
`Holds`: every active `WSA` row has `t < 2^24`). The tape-time premise `htape` is **gone**:
`wsa_gap_rec`, `ws_decoded`, `ws_decoded_final`, `WsDecode4.ws_decoded_final2`,
`WsKey.ws_decoded_final3`, `WsEntries.ws_entries` and `FinalOrder.Prem` no longer take it (no
theorem has a premise on where the `WRITE` times come from). The old `wsa_t` (from the tape) is
kept. `lake build StateM5a` green, std axioms.

Results on the final AIR [M] (same stack and parameters as M5a-5, 8 threads, shared host):

| | T1 (D = 5) | T2 (D = 6) | synthetic `bval` (D = 4) | T2 seg 3 × 5 | synthetic `bvnref` (D = 4, new) |
|---|---|---|---|---|---|
| committed cells | 5,152,964 | 10,733,472 | 1,988,684 | 10,733,472 | 1,011,288 |
| proof (268.2-bit) | 1,238,006 B | 1,264,046 B | 1,214,996 B | 1,263,542 B | 974,892 B |
| prove / verify / peak RSS | 78 s / 97 ms / 1.29 GB | 123 s / 102 ms / 1.70 GB | 42 s / 92 ms / 1.01 GB | 124 s / 105 ms / 1.78 GB | 19 s / 87 ms / 0.19 GB |
| root (= `m5a-tool apply`, Lean) | `1db48e38…249628` | `61f5330a…07993006` | `b2142cc9…bd07895` | `61f5330a…07993006` | `617e704e…20787749` |

`synth.py bvnref` (new): two changes below the branch holding `alice`'s value, so the first
rewrite of that branch keeps the value under a version id and the second reads it from `VER` —
the only trace with a row the `nvlbyte` mutant can tamper (T1, T2 and `bval` have no
version-published branch with a value).

Mutants (`logs/M5a6-mutants.txt`): **83/83 rejected** — T2 29, T1 21, synthetic 19, T2-seg3x5 7,
`bvnref` 7: all 68 of M5a-5 plus `tbig` (an access at time `2^24`, time cells encoding it exactly,
one cell 256 → `RNG`), `twrap` (the same with bytes encoding `t mod 2^24` → the new `WSA`
constraint) on T2, T1, synthetic, T2-seg3x5, `bvnref`, and `nvlbyte` on `bvnref` (rejected by
`RNG` alone: 2 unbalanced `RNG` messages, nothing else catches it). Logs `logs/M5a6-*-prove.log`,
hashes `logs/SHA256SUMS-v6` (the prover binary there is the M5b one; for the M5a AIR it only
differs in where it inserts `TAPE`, which is the same position).

### Lean: premises of the batched FINAL from `Holds` [K] (std axioms, no `sorry`)

Headline **`SnFinal4.air_final_sorted_sn4`**: `applyChanges (some T) (sortKV committed)` reaches
`post_state_root` from `Holds` of the AIR the prover runs, `Sha256CR`, the chip contract and only:
`SnUpLimbs`, `SnMatLimbs` (memory limbs every `SN` row sends on `UP` / `MATR`), `SnRest2` (`LocalOK`
of split rows and continued-key rows), `hlongS` / `hlongM` (continued-key responders). Discharged
since M5a-5 (`air_final_sorted_sn2` took them all as premises):

| premise | now | where |
|---|---|---|
| `hnd` (distinct version ids) | `snVers := SnStore2.snVers tr pub`, `vers_nodup` (`256·(ID+2r+1) mod P`, BR vs SN id ranges disjoint) | `SnStore2` |
| `BR` `hVl`, `hVP` | every `BR` record on `VER` has length bytes `(ℓ₀,ℓ₁,ℓ₂,0)`: hashed (SHA bytes) or version-published (the new `RNG [nvl]`), `nvl₃ = 0` from `oUV·nvl₃` / the kept-value equations; a reader's limbs are the publisher's (part 16) ⇒ limbs `< 2^16`, `brVlen < 2^24` | `BrVl.hVl_of`, `hVP_of` |
| `BR` `OslApart` | a non-descending row is the deepest of its walk; one split row per walk | `WalkEnd.oslApart` (sub-agent) |
| `SN` `SnOldAll`, `SnOldAny` | `sn_oldOK`: hashed here, or read on `VER` (3 parts, `SnVer.sn_rd_part`): under a version id all parts from the one row with that id; under a digest from records hashed to it, equal by `Sha256CR`, the reader's key assembled from part 0's length and parts 1/2's nibbles through the common key (`key_of_parts`; the `BR`-side `PartDec` does not apply: raw nibbles past the key's end are not determined by the record) | `SnStore`, `SnStore2` |
| `SN` `SnNewAll`, `SnNewAny` | `sn_newOK` (hashed or under its version id) | `SnStore2` |
| `SN` `Hashed` (new) | a head with `cont = 0` hashing its old / new node: every byte it sends is the `snSerF` entry at its position (`sn_ser_ok`); every SHA byte under its ids comes from it (`SNC` rows only serve continuing heads, `snc_cont`), so the message is `snSerF`, all bytes, and the record is `Hashed` (`grecS_hashed`: hex-prefix from `sn_hexPrefix`, key nibbles `< 16` by `sn_k16`) | `SnSer`, `SnDigest`, `SnHashed`, `SnRec` |
| `SN` `SnLimbs3`, `SnLeafMemLt`, `SnMatLeaf` | `nmem` / leaf `nx` bytes (hashed or `RNG` under `nref`), old memory limbs (hashed or the `VER` publisher's), new leaf memory `< 2^25` (`nmem₃ ∈ {0,1}`, `nmem₄..₇ = 0`) | `SnRange` |

**Restated premises.** `SnOldAll`, `SnNewAll`, `SnOldAny`, `SnNewAny`, `SnLimbs`, `SnLimbs3`,
`SnLeafMemLt`, `SnMatLeaf` now quantify over rows with `cont = 0` only. Before, they also covered
continued-key rows, for which `snOld` / `snNew` read the head key only (`klen` counts the whole key,
so `snKey` reads columns past the 64 nibbles) — a premise no honest trace satisfies there; the
consumers (`hloc_sn`, `hloc_sn2`, `hloc_sn3`, `snSibOK_of`, `snMatOK_of`) only used them at
`cont = 0` (continued keys are in `SnRest2` / `hlongS` / `hlongM`).

**Split rows (sub-agent, partial).** Committed and green: `WalkEnd` (`OslApart`), `BrOsl` /
`BrOslSplit` (`osl_split`: `SplitRel` of a split's new branch `BR.oSL` from `Holds` + `SnMatOK`),
`SnSplitBus` (`SPR`/`EPQ`/`SXQ`/`SXR` senders, `oslQ_eq`). In `lean-wip/` (not built):
`SnSplit.lean` (`FreshRel` of `oEP`/`oEM`, `split_ans`: `SplitAns` from `Holds`), `SnSplitLoc.lean`
(`localOK_oLX`, `localOK_oEX` at `cont = 0`), `SnFinal3.lean` — `SnSplit` exceeds the 24 GB Lean
budget as written (to be split into smaller lemmas), the other two were never compiled.

## M5a-5 (sixth session, 2026-11-03)

Log `docs/logs/e2e-m5a5-state-2026-11-03.md`. Six AIR changes (`wsLen`, and five soundness
fixes — two real holes — found by the per-row decoding and an audit), T1/T2/synthetic/T2-seg3x5
re-proved, all mutants rejected; Lean: one upsert semantics, the premises of
`air_batched_changes` discharged from `Holds` except the `SN`-side ones listed under *Open*, the
working set from `Holds`, `StViewParams` for lane B, a non-vacuity witness.

### AIR changes [M][K]

| change | why | constraint / lookup |
|---|---|---|
| `wsLen` = public value 16 (integrator decision) | the entry count is in the state commitment; a real leaf must not equal a zero padding leaf | `WSB`: `real ↔ i < wsLen` in both phases (4 constraints); `WSL`: `i < wsLen` (bytes `ix` of `wsLen − 1 − i`, `RNG`) |
| `BR` `oDH`/`oDL`: `om ≤ mem` | the spec's `Kids.delAt`/`squashBranch` computes `m − old + new` with truncated subtraction; the row's chain is exact. They differ when a child's old memory exceeds the parent's, which `PTrie.wf` allows | `dm = mem − om` (8 `RNG` bytes, no-final-borrow `memChain`, carries `cyd`) |
| `BR` `oUV`: written length `< 2^24` | **soundness hole**: the 4 length bytes were tied to the walk's `dvlen` over BabyBear; `2^32 > P`, so the bytes could encode `|x| + P`, serialized and charged as the u32 length | `oUV · nvl₃ = 0` (as `SN`'s 3 length bytes) |
| version-published nodes: value bytes ranged | a node published on `VER` under a version id is not hashed, so its value bytes were tied to the walk only by pair sums / `vlenOf`; a non-byte cell with the same combination entered the record later rows read | `RNG` receives: `BR` `nvh` (gate `nref`), `SN` leaf payload `nx` (gate `nref·isL`) |
| `SN` `oLR`/`oLM`: new leaf memory `< 2^25` | **soundness hole**: the memory was one field equation over `limb₀ + 65536·limb₁` of byte columns (up to `2^32 − 1 > P`), so `leafMem + P` passed and the parents' exact 64-bit chains carried it into the root | `(oLR + oLM)·nmem₃·(nmem₃ − 1) = 0` |
| `BR` old value length `< 2^24` | the find answer carries the 4 length bytes as one field element; `PTrie.wf` allows lengths `< 2^32`, so a length in `[P, P + 2^24)` answered `L − P` (no attack on NEAR's ≤ 4 MiB values, but a state premise) | `hasv · vl₃ = 0` (as `SN`'s `isL·x₃ = 0`) |

The `oUV`, `oLR`/`oLM` and version-byte findings came from the per-row decoding (the Lean step
could not be proved without a `< P` premise); a read-only audit of the whole AIR for this class
(sums of bytes/limbs reaching `P`, unranged bytes, truncated spec subtraction, counter wrap) then
found the old-length case and nothing else in the current AIR, plus two items for later: `WSA`
times `t` must be range-checked once M5b makes them prover-chosen (today they come from the public
tape; with free `t` a closed `WM` cycle of ~120 accesses summing to `0 mod P` would balance on its
own), and the `SN` `u32 |hp|` is sent as one byte (a completeness gap for node keys ≥ ~510
nibbles).

Results on the final AIR [M] (same stack and parameters as M5a-3, 8 threads, shared host):

| | T1 (D = 5) | T2 (D = 6) | synthetic `bval` (D = 4) | T2 seg 3 × 5 |
|---|---|---|---|---|
| committed cells | 5,152,916 | 10,733,280 | 1,988,660 | 10,733,280 |
| proof (268.2-bit) | 1,238,870 B | 1,262,138 B | 1,216,322 B | 1,267,556 B |
| prove / verify / peak RSS | 72 s / 105 ms / 1.27 GB | 130 s / 119 ms / 1.57 GB | 46 s / 118 ms / 1.01 GB | 121 s / 114 ms / 1.65 GB |
| root (= `m5a-tool apply`, Lean) | `1db48e38…249628` | `61f5330a…07993006` | `b2142cc9…bd07895` | `61f5330a…07993006` |

Mutants (`logs/M5a5-mutants.txt`): **T2 27/27, T1 19/19, synthetic 17/17, T2-seg3x5 5/5
rejected** (68): all of M5a-3 plus `wslen` / `wslenlo` (statement claims one entry more / fewer →
the new `WSB` constraint), `dmono` (`mem − om` witness off by one → the new chain), `bvwrap`
(synthetic: length bytes encode `|x| + P`; caught first by `memNew`), `vbyte` (a version leaf's
hash cell non-byte with the same pair sum → `RNG` and `VER`; no version leaf in the synthetic
trace), `lmwrap` (an `oLR` leaf's memory bytes encode `leafMem + P` → the new `nmem₃`
constraint). Logs `logs/M5a5-*-prove.log`, hashes `logs/SHA256SUMS-v5` (prover binary unchanged).

### Lean [K] (std axioms, no `sorry`; `lake build StateM5a`, Audit 530+ `#print axioms`)

* **One upsert semantics** (integrator decision): `Walk.UChain.extSplit` (the spec's `splitExt`,
  `Steps.ext_split'`); `uchain_sound` covers it, so `BusSplit2.step_extSplit`/`localOK_extSplit`
  are on `SemU`/`Sem`. `SemUS := SemU`, `semS_eq_sem : SemS = Sem`, `localOK_semS_iff`;
  `DecodeShape.air_batched_changes` is the one assembly (`*S` are one-line corollaries).
* **Keys, depths, tape** (`KeyDecode`, `KeyLookups`, `DepthBound`, `KcChain`, `KeyDigest`,
  `KeyOrder`, `IntakeKeys`, `Tape`, `FinalOrder`): `keyOf tr = nibbles (keyBytes tr)` from the
  `KEY` table; every `NIB`/`KLEN` receive is a lookup into it (`nib_recv`, `klen_recv`, per
  interaction in `KeyLookups`); `KDIG = sha256 keyBytes` (`kdig_recv`, from the SHA-256 table
  contract and the id spaces); `ORD(ka, kb) ⇒ bytesLt` (`ord_recv`); depth bounds `br_depth`,
  `sn_depth`, and the `SNC` chain bound (`sncDeeper`) replace `hbr`/`hsn`; the public tape is a
  Lean table (`tapeTable`), `tch_perm` gives `hT`, `root_of_row` gives `hroot`; the INTAKE keys are
  strictly increasing and distinct, the writing roots are in key order, and
  **`FinalOrder.air_final_sorted`**: `applyChanges (some T) (sortKV committed) = some (some T')`
  with `rootHash = post_state_root`, for every `committed ~ cs` matching the writing rows.
* **Per-row `LocalOK`** (`RowDec`, `RowBr*`, `RowFacts`, `RowHloc`, `Ver*`, `BrSer`, `BrDigest`,
  `BrRange`, `BrSib`, `BrMat`, `RowSn*`): a concrete decoder `cDc` (`Tape.StdDec`); **all 14 `BR`
  walk ops** `LocalOK` from the row's constraints; `OldOK`/`NewOK` of `BR` records from `VER`
  balance (`VerStore.br_oldOK`/`br_newOK`: parts of one digest from several publishers assemble
  to their common record, `VerDec.dec_of_parts`); `BrDigest.brHashed`: a hashing row's record
  hashes to its digest (SHA-256 contract, single sender per message id, `BrSer.ser_ok`), no
  cryptographic assumption; limb ranges (`BrRange.brRangesW_of`); `MATR`/`SIBA` answers
  (`br_mat`, `br_sib`, via `walk_unique`). `SN`: decoded rows, mismatch witness, and the walk
  ops `oLF`, `oEF`, `oLA`, `oEA`, `oLZ`, `oEZ`, `oLD`, `oLR`, `oEU`, `oES`, `oEB`, `oED`
  (`RowSnAll.hloc_sn`, `RowSnAll2.hloc_sn2`, `SnAssembly.hloc_sn3`; new records `RowSnN.snNew`
  with exact memories), `SnDepthAll.sn_depth_all`, the responder relations `SnSibOK`/`SnMatOK`
  for one-row keys (`SnResp`). Latest assembly **`SnResp.air_final_sorted_sn2`**:
  `applyChanges (some T) (sortKV committed)` reaches `post_state_root` from `Holds` of the AIR the
  prover runs, `Sha256CR`, the chip contract and the premises listed under *Open*.
* **Working set from `Holds`** (`WsLen`, `WsRaw`, `WsDecode*`, `WsSeg`, `WsTree`, `WsKey`,
  `WsLeafF`, `WsEntries`): `wsb_real_iff` (`real ↔ i < wsLen`), `wsb_leaves` (`wsLen` real
  leaves, then zero padding), `wsl_lt_wsLen`; `PT`/`RCH`/`WM`/`TREE` traffic decoded (field
  positions bounded by counting, no wrap); `wsn_roots` (INTAKE / FINAL roots are the Merkle roots
  of the `WSB` leaves); `ws_compose`/`ws_final`; `content_eq` (equal leaf blocks ⇒ equal fields;
  length chunks `< 64` from the chip contract's 64-bit words); **`WsEntries.ws_entries`**: every
  real FINAL leaf has the INTAKE key and pre-value, and its current value / written flag is the
  entry's latest write (or the INTAKE value). Premises: `Sha512IfContract`, `CompressOK`,
  `NodeCR`, `LeafCR` (named), tape times `< 2^24`.
* **`StViewParams` for lane B** (`StateView`, `StateViewParams`): `stD` has a circuit form
  (`fits v`) and a raw form (the M5a-4 `∀ v` range fields could not be met by any projection);
  the trie is committed as root + reveal shape (`shape_binding`); `leafBlockN_inj`,
  `encRestB_inj`, `rawB_inj`, `proj_injB` (`kv_ext`), `stD_binding_B`, `viewImpl_hst_B`.
  **Lane E supplies `StViewE`**: `encE` injective on stripped components (`EPos`/`RS` minus the
  overlay, `Recording`, `MainOutD2`); `keysOf` (the chunk key set — not determined by the overlay
  or the partial trie, so it must be carried in `StV`, e.g. `StV.eng` from the intake record);
  `idxOf`; `depth ≤ 24`; and for segment soundness only `FitsReach` (replaces `trie_ok`: reached
  overlays keep the intake trie `t` of `Ovl.ofTrie`, `t.wf`, `t.hashOf = prev_state_root`, shape
  `erase t` in the rest, `ovlInv`, values `< 2^24`, entries `≤ 2^depth`).
* **Non-vacuity** (`ChipStub`): `IF384` (16) is the only bus without a Lean or tape sender (the
  native SHA-512 chip). `holds_of_holdsX`: a trace satisfying `Holds` except `IF384` balance
  extends by a constraint-free stub sender (`chipStub`) to `Holds` of the AIR with the stub
  appended, tables unchanged, no receive multiplicity forced to vanish; `precheck_holds_tape`:
  every precheck-accepted trace gives a `Holds` instance of the shape our theorems take, and their
  `Sha512IfContract` premise becomes the native chip's faithfulness on its own sends. No theorem
  excludes the stub (`stub_bus_premise`), so none is vacuous.

### Open after M5a-5

1. Premises of `air_final_sorted_sn2` on the `SN` side: the splits `oLX`/`oEX` (step lemmas exist;
   they need `SplitAns` from the `SPQ`/`SPR`/`EPQ`/`SXQ` protocol) and continued keys
   (`cont = 1`, `SnRest2`, long-key responders `hlongS`/`hlongM`); `SN` old/new records from
   `VER`/SHA-256 (`SnOldAll`, `SnNewAll`, `SnOldAny`, `SnNewAny`: an `SN` `PartDec`, the `SN`
   analogue of `br_rd_part`, `snVers`, `SN` `Hashed`); limb ranges `SnLimbs3`, `SnUpLimbs`,
   `SnMatLimbs` (the audit shows each is pinned by SHA bytes / `RNG` / `VER` — a proof task);
   `SnLeafMemLt`/`SnMatLeaf` (`< P`) are now dischargeable from the new `nmem₃` constraint.
2. `BR`: `OslApart` (a split's new branch is not at an active row's walk position); `hVl`
   (16-bit `vl` limbs on rows reading on `VER`) and `hVP` (old length `< P`, now dischargeable
   from `hasv·vl₃ = 0`).
3. M5b: range-check `WSA` times (above).
4. `committed ~ cs`: the spec's committed overlay against the writing rows' changes (overlay ↔
   tape, value preimages) — M5b.
5. Lane E: `StViewE` (above).
6. Completeness gaps (unchanged): squash after a value delete / onto an extension or branch
   sibling, splits where a key ends at the new branch, mismatch past 63 nibbles, the empty trie;
   new: node keys ≥ ~510 nibbles (the `u32 |hp|` is sent as one byte).

## M5a-4 (fifth session, 2026-11-03)

Lean only [K] (std axioms, no `sorry`, no circuit change; T1/T2/synthetic proofs and mutants of
M5a-3 stand unchanged). Modules in `lean/StateM5a/`, all in `StateM5a.lean` and `Audit.lean`.

### From `Holds` of the AIR to `applyChanges` (priority 1)

* **Walk traffic from `Holds`** (`DecodeBus`, `DecodeWalk`, `DecodeM5a`): `walk_traffic` — for the
  AIR the prover runs (`fullAir D extra` = `m5aAir D` followed by any tables that do not use
  `DOWN`/`UP`: the SHA-512 chip, the public tape) and **any** field decoder `Dc` (walk id and
  depth = the first two message elements as naturals, the rest via `Dc.dp` / `Dc.dr`), the decoded
  `BR`/`SN` rows (`walkRows`: one `WRow` per active row, from the table's own `DOWN`/`UP`
  interactions) and `WSB` roots (`walkRoots`: INTAKE and FINAL roots) satisfy
  `downSends ~ downRecvs` and `upSends ~ upRecvs` exactly as `Traffic` takes them. Decoding needs no
  injectivity (`List.Perm.map`). The `DOWN`/`UP` interactions are read off the exported tables and
  pinned by `filter` lemmas (`br_ds`, `sn_ur`, `wsb_ds`, …; an AIR change breaks the build); the
  other nine tables are shown not to use `DOWN`/`UP` (`decide`).
* **Field facts**: `FieldWalk2.sn_gdn_walk` (the M5a-3 open `SN` descend fact, now staged: each
  `omega` sees ≤ 12 flags) — `gdn = 1 ⇒ mF + mU + mD = 1 ∧ isE = 1 ∧ a₀ = 1`, and
  `sn_gdn_klen`: with `cont = 0`, `1 ≤ klen ≤ 64`. `FieldWsb.wsb_index`: the `WSB` rows are phase 0
  with `i = r`, then phase 1 with `i + 2^D = r` (from `isFirst`/`isTransition`/`e`, heights
  `≤ 2^20`).
* **Walk shape** (`DecodeShape`): `walk_rootUniq` — one decoded root per walk id, **from `Holds`
  alone** (`D ≤ 30`): INTAKE id `r < 2^20`, FINAL id `2^20 + i`; `walk_deeper` — a child `DOWN` is
  in the same walk and strictly deeper (`BR` `d + 1`, `SN` `d + klen`), under two premises: the
  depth of a descending row is `< P − 64`, and a descending `SN` row has `cont = 0`.
* **Assembly**: `air_batched_changes` / **`air_batched_changesS`** — `bus_batched_changes` (resp.
  the split-aware `bus_batched_changesS`, below) with its `DOWN`/`UP` permutations and its walk
  shape discharged from `Holds`. Premises still open: the depth bounds (`hbr`, `hsn`), every decoded
  row's `LocalOK` (`hloc`: the per-row facts below), `TCH` against the public tape (`hT`) and the
  writing roots as roots of the committed changes (`hroot`); `Sha256CR` is the only cryptographic
  premise.

### Row-local steps for the remaining ops (priority 2; `BusSplit`, `BusSplit2`)

* Responder relations, one per request / response bus, each proved from the responding row's
  decoded facts: `matRel_oLM` (`MATQ`/`MATR`), `sibRel_oLS` (`SIBQ`/`SIBA`), `sxRel_oEM`
  (`SXQ`/`SXR`), `epRel_oEP` (`EPQ`), `splitRel_oSL` (`SPQ`/`SPR`); carried to the requester by
  `Traffic.reqresp` (`spr_reqresp`, `mat_reqresp`, `sib_reqresp`, `sx_reqresp`;
  `splitAns_of_spr`: the `SPR` answer at the requester's depth is `wrapExt p (splitBr …)`).
* Steps: `step_leafSplit` (`oLX`, via `UChain.leafSplit`), `step_brLeaf` (`oDL`: a kept branch
  whose child is a leaf descriptor, slot from `MATR`; `step_brKeep` does not cover it),
  `step_brOne` (`oD1` + `oLS`: squash onto the one remaining leaf sibling), `step_extSplit`
  (`oEX`); `LocalOK` wrappers for each.
* **`oEX` and `SemU`**: `SemU` is stated through `Walk.UChain`, which has no extension-split
  constructor, so `oEX` is proved against `SemUS` (= `SemU` with the spec equation
  `t₁.upsert (K.drop d) x = some t₁'`, `semUS_of_semU`), with `oUD`/`oEU` re-proved on it and
  `bus_batched_changesS` (same statement, same `Sha256CR`-only premise). `air_batched_changesS` is
  the main assembly.

### Working-set bus step and the SHA-512 chip interface (priority 3; `WsBus`, `Sha512If`)

* `WM` memory chain: `wm_orphan` (every write access has its entry's `WSL` row), `wm_chain` (per
  entry, the time-sorted accesses are exactly `WsCost.chain_sound_any`'s premise: the closing value
  is the last write). `RCH`: `rch_tops` (one top row per segment), `rch_link` (segment roots chain
  from the INTAKE root). `PT`: one row / message per tree position (`pt_rows_le_one`,
  `wsl_unique`, a counting argument as `walk_unique`); `seg_update` rebuilds the segment's
  `Merkle.Upd` from the `WSP`/`WSL` rows; `seg_root` / `seg_root_leaves`: with no collision of the
  node hash, the new `RCH` is the root of the working set with exactly the touched leaves replaced.
* `Sha512If`: the native chip's `IF384` interface (from `prover/src/s384/{air,main}.rs`: 16
  messages per compression over `h ‖ block ‖ compress(h, block)`) as the contract
  `Sha512IfContract` (compression function a parameter); `comp_sound`, `comp_iv` (leaf digest),
  `comp_node` (`o = nodeH l r`), `wsp_hashes` (a `WSP` row's two compressions are `WspOK.hO`/`hN`
  with `H = nodeH compress`), `enc_inj`.

### State component of lane E's `ViewImpl` (priority 4; `StateView`)

The package imports `NearSpecV3.E2E.View` (read only). `stD P v = bdigest (ser (commitOf P v))`,
`StCommit = (tag, working-set root 48 B, entry count, trie root 32 B, change index, rest digest
42 B)`, 139-byte injective serialization (`ser_inj`). Working-set root: `Merkle.root` of
`sha384(l ‖ r)` over leaf digests `cmp384 (leafBlock (sha256 key, vref pre, vref cur, written))`.
Proved: `merkle_binding`, `trie_binding` (fully revealed well-formed tries with equal `hashOf`
are equal or a SHA-256 collision; via `nodeSerInj`), `wsRoot_binding`, **`stD_binding`**:
`Coll (stD P) → Sha384Coll ∨ Sha256Coll ∨ LeafColl` (`LeafColl`: a collision of the one-compression
leaf digest, a named event), `viewImpl_hst` — exactly the `hst` argument of
`viewImpl_binding_bad` — and `viewImpl_binding_st`. Parameters (`StViewParams`, obligations for
M5b/M5d/lane E): `proj_inj` (tag, working set, trie, index and rest determine the `StV`; the
working set's key set must become a function of `StV`), `encRest_inj` (an injective encoding of
the rest of `RS`/`Recording`/`MainOutD2`), `trie_ok` (the trie is fully revealed: the spec's
`Ovl` trie is partial, so lane E must commit its full expansion and put the reveal shape in the
rest), `leafBlock_inj` (from `WsCost.leafLimb_inj`), range facts. Note: the entry count `wsLen` is
not carried by the circuit today (without it a real leaf could equal a zero padding leaf — a
preimage event, not a collision); it can be a chunk constant.

### Open after M5a-4

1. Per-row decoded facts → `LocalOK` for each decoded row (the `step_*` premises: `OldOK`/`NewOK`
   from `ver_store` and the hashing rows, nibble lookups, bounds, kept-branch counts) — needs the
   `VER`/`SHA`/`NIB`/`KLEN` traffic decoded as `walk_traffic` does for `DOWN`/`UP`, and a concrete
   decoder `Dc`.
2. Depth bounds `hbr`/`hsn`: from the `NIB` lookup at depth `d` (`KEY` indices `< 2^21`) — needs
   the `KEY` index lemma and lookup membership; the `SNC` chain bound on a continued head's `rl`.
3. `TCH`: the public tape as an `extra` table in Lean; the writing roots ↔ committed changes
   (`KCMP` order, the `WRITE` tape).
4. Working-set field → record decoding (`WM`/`PT`/`RCH`/`IF384`), range facts, the chip itself
   (its faithfulness argument stays outside `Holds`), composing segments along `rch_link`.
5. `ViewImpl` parameters above; the `UChain` / `SemU` choice (`SemS` adopted for the assembly).
6. Completeness gaps (not started this session): squash after a value delete / onto an extension
   or branch sibling, splits where a key ends at the new branch, mismatch past 63 nibbles, the empty
   trie.

## M5a-3 (fourth session, 2026-11-03)

### Bus-level step [K] (`lean/StateM5a/{Bus,Traffic,BusWalk}.lean`, std axioms, no `sorry`)

From bus balance to `rootHash (applyChanges …)`, with `Sha256CR` the only cryptographic premise:

* **`Bus`** (generic, ZkFormal): `busList A tr pub b s` = the messages sent / received on bus `b`,
  repeated by multiplicity; `count_busList` (= `busCount`), **`holds_perm`**: `Holds A pub tr` ⇒
  on every bus the sent list is a permutation of the received list (the LogUp predicate in list
  form); `perm_decode`: under an injective encoding the decoded message lists are permutations too.
* **`Traffic`** (generic record-level traffic):
  * **`walk_unique`**: at most one active row receives a `DOWN` at each `(w, d)`.  `UP` does not
    repeat the node's ref, so this is what lets a parent trust the answer at `(w, d')`.  Proof:
    the number of open `DOWN` edges of walk `w` crossing depth `d` is 1 at `d = 0` (one `WSB`
    root per walk) and never grows (`cross_step`: a row at `d` that descends replaces the edge
    that reached it), and the rows at `d` are at most the edges ending there.
  * **`walk_sem`**: any property `Sem` that every active row's step carries from its child's
    `(DOWN, UP)` pair to its own holds at every walk root (induction on depth, `child_of`).
  * **`tch_chain`**: `TCH` balance makes the writing `WSB` rows one chain from the public
    `TCH(0, prev)` to `TCH(n, post)` (row count `= n`, `a (j+1) = b j`).
  * **`ver_recv`**: a `VER` reader's record (all parts) is one published record, if publishers
    under one ref agree; **`reqresp`**: on a request / response bus (`MATQ`/`MATR`, `SIBQ`/`SIBA`,
    `SPQ`/`SPR`, `SXQ`/`SXR`) with one request per key, the response a requester receives comes
    from a responder that received exactly its request.
* **`BusWalk`** (the M5a instantiation):
  * **store**: `ver_store` — `σ = storeOf vers` (version-publishing rows' records by id; ids
    distinct); every `VER` reader's record is `OldOK σ ref R` (a version id's record, or a record
    hashed to the digest; digest publishers agree: `hashed_agree`, `Sha256CR` + `NodeSerInj` via
    `shallow_eq`).
  * **views**: `in_view_wf` (the expansion of a row's input ref reveals to its record with expanded
    children, well-formed), `out_view` (a node whose children collapse to the expansions of the
    published record's children collapses to the expansion of the output ref); `Cl` = collapse
    including written values (`.ref |x| (sha256 x) ↦ .val x`, leaf `slot` and branch `bval`),
    `cl_collapse` (keeps refinement), `cl_wf` (keeps `wf`).
  * **walk semantics** `Sem` = `SemF` / `SemU` / `SemD` by mode, and **23 row-local steps**:
    upsert `oLR`, `oUD`, `oEU`, `oUN` (with `MatRel`, the `MATQ`/`MATR` answer), `oUV`; delete
    `oLD`, `oLZ`, `oEZ`, `oES`, `oED`, `oEB`, `oDA`, `oDS`, `oDH`/`oDN`, `oDZ`, `oDV`; find `oLF`,
    `oLA`, `oEA`, `oEF`, `oFD`, `oFA`, `oFV` (`step_*`; `localOK_upsert`/`_delete`/`_find` turn
    them into `Traffic.LocalOK`).
  * **`chain_changes`** / **`bus_batched_changes`**: walk shape + `DOWN`/`UP`/`TCH` balance +
    every row's `LocalOK` + the writing rows as roots of the committed changes ⇒ on any revealed,
    well-formed witness trie with root `prev_state_root`, `applyChanges` succeeds and
    `rootHash = post_state_root`.  **Premise `Sha256CR` only**: `KeepsFW` (false, see below) is
    not used — well-formedness is carried along the walk (rows' memory / length bounds) and
    `Store.keepsFWRows` transfers it to the witness.

* **`FieldWalk`** (field level, from the exported constraints over BabyBear): `br_gdn_gold`
  (`BR`: `gdn = 1 ⇒ gold = 1`, a `DOWN` sender is an active row), `sn_bool` and the `SN` one-hot
  memberships; the `SN` analogue (`gdn = 1 ⇒ gwalk = 1 ∧ isE = 1 ∧ a₀ = 1 ⇒ 1 ≤ klen`) is open
  (the direct proof exhausts memory; needs a staged proof).

**What is still a premise** (open; field level / remaining ops): (1) decoding — each table's
`DOWN`/`UP`/`TCH`/`VER` interaction message is the injective encoding of the decoded record
(`perm_decode`'s hypotheses, refs as flag + 16 limbs); (2) `WalkShape` (`d' > d`: `BR` `d + 1`,
`SN` `d + klen` with `klen ≥ 1` — open at field level (`FieldWalk` has `BR` only), the `SNC` chain bound on `rl` for a continued head is open; one root per walk: `WSB` `i` distinct,
`W_FINAL` offset) and active-row bookkeeping (`gdn ≤ gold` from the one-hot bundles); (3) the
per-row decoded facts each `step_*` takes (`OldOK` from `ver_store` / a hashing row, `NewOK`,
nibble lookups `K.drop d = …`, mismatch witness, memory / length bounds, kept-branch counts);
(4) row-local steps for the split ops (`oLX`/`oEX`/`oSL`/`oEP`/`oEM`/`oLM`), `oDL` and
`oD1`/`oLS` (the bus tool is `reqresp`); (5) the link from the write tape / `WRITE` order to the
change list (`KCMP` ⇒ `sortKV` is `Order`; the leaf ↔ change pairing is the `WSB` table).

### M5a-3 Lean (state, priority 2) [K]

* **`KeepsFW` is false** (`Store.not_keepsFW`: a `2^32`-byte value written into a well-formed
  leaf). Replaced by what holds (`Keep`): `RP P a b` = refinement whose stubs cover subtrees with
  property `P`; `upsert` and `del` commute with it for every `P` (`upsert_rp`, `del_rp`). With
  `P = False`: a change keeps the witness revealed, unconditionally (`full_upsert`, `full_del`,
  `full_applyChange`). With `P = wf`: every node of the spec's result is a node the rows
  rewrote or an old subtree, so `t₁'.wf` (the rows' new trie: range-checked memory limbs,
  nibbles, key / value lengths) gives `T'.wf` (`applyChange_wf_of_rows`). Together
  `keepsFWRows : KeepsFWRows`.
* **`batched_changes'`**: `batched_changes` without `KeepsFW`; premises `Sha256CR` and
  `ChangeRowsW` (the rows of every change, with `t₁'.wf`). The old `batched_changes` and
  `KeepsFW` are kept unchanged.
* Chain constructors `UChain.brVal` (`oUV`), `DChain.brDelVal` (`oDV`), `DChain.brValAbs` (`oDZ`),
  with their memory correspondence to `Br.memNew` in the docstrings; `uchain_sound` /
  `dchain_sound` extended (all other users go through them).
* `StepsBV.br_del_value_one` (+ `_leaf`, `_ext`, `_branch`, `_hash`, `br_del_value_none`): the
  spec step of the squash after a value delete leaving one child, for a future row op.

### M5a-3 cost: the working-set chip [M][K]

M5a-2 left the SHA-512 working-set chip as the largest state cost (T2: 10.9 M of 16.2 M committed
cells; `WSA` 170.6 k cells per write: `4 + 2D` compressions). M5a-3 changes what is hashed, keeps
`RCH` as the per-segment working-set root, and re-proves T1, T2 and the synthetic case. (The
sections below describe M5a-2 and M5a; their `WSA` = one Merkle path per write is replaced.)

#### Design

| | M5a-2 | M5a-3 |
|---|---|---|
| leaf digest | 2 compressions (`compress(compress(IV, B1), B2)`, 32 words, half of them zero) | **1 compression**: 16 words, `(pv₂ₜ, pv₂ₜ₊₁, kdₜ + 2¹⁶·xₜ)` / `(cv₂ₜ, cv₂ₜ₊₁, kd₈₊ₜ + 2¹⁶·x₈₊ₜ)`; the side slots `x` hold `pp + 2cp + 4wr` and the two lengths' 6-bit chunks, range-checked as bytes (`RNG`), with `kd` 16-bit, so the block determines the leaf (`WsCost.leafLimb_inj`) |
| `WSB` (INTAKE + FINAL leaves) | 4 compressions per key | 2 per key |
| one write | one `WSA` row: old leaf + new leaf + old path + new path = `4 + 2D` compressions | one `WSA` row with **no hashing**: it consumes the entry's latest value on a new memory bus `WM(seg, kd, value, wr, id)` (`idp < t`, 3 gap bytes) and sends its own at its time `t` |
| per segment | – (the root moved once per write) | **one batched path update**: each touched leaf once (`WSL`: old and new leaf, 2 compressions; it opens and closes the entry's `WM` chain) and each node on the union of the touched paths once (`WSP`: old and new digest, 2 compressions; an untouched sibling is one digest for both trees). The top row takes `RCH(seg, old root)` and sends `RCH(seg + 1, new root)` |
| `WRITE` (public tape in M5a, STATE rows in M5b) | `(kd, value)` | `(seg, t, kd, value)` |

`RCH` stays the working-set root at each segment boundary (M5b's STATE segments cut there); `WSN`
still builds the full INTAKE tree (`RCH(0)`) and the full FINAL tree (closes `RCH(nseg)`), so
FINAL still enumerates every written leaf. The memory chain is per segment (its messages carry
`seg`); nothing crosses a segment except `RCH`. The trace generator takes `--segs S` (default 1:
the whole M5a write tape is one STATE segment) and `--extra-writes N` (an intermediate write before
the final one for N keys, to exercise the chain); `run.sh` passes them via `GENARGS`.

Per write (T2, D = 6, one segment): 16 compressions → 2·(42 + 51)/42 ≈ 4.4 (touched leaves 42,
union-of-paths nodes 51); per key: 4 → 2. Compressions T1 270 → 150, T2 1,006 → 416, synthetic
146 → 76; T2 now fits a 2¹⁶-row chip (was 2¹⁷), T1 2¹⁵ (was 2¹⁶), synthetic 2¹⁴ (was 2¹⁵).

#### Results [M] (same stack and parameters as M5a-2; 8 threads)

| | T1 (`d3c8/d3/02-h10196-s3`, D = 5) | T2 (`d3c9/d3/00-h10018-s0`, D = 6) | synthetic `bval` (D = 4) |
|---|---|---|---|
| keys / writes / segments | 17 / 10 / 1 | 52 / 42 / 1 | 8 / 7 / 1 |
| SHA-512 compressions (M5a-2 → M5a-3) | 270 → **150** (`WSB` 34, `WSN` 62, `WSL` 20, `WSP` 34) | 1,006 → **416** (`WSB` 104, `WSN` 126, `WSL` 84, `WSP` 102) | 146 → **76** |
| SHA-512 chip rows (padded) | 2¹⁶ → 2¹⁵ | 2¹⁷ → 2¹⁶ | 2¹⁵ → 2¹⁴ |
| cells per write (`WSA` + segment update) | 149 k → 57.8 k | 170.6 k → **47.4 k** | – |
| total used cells (`cost.py`) | 4.83 M → **3.55 M** | 14.97 M → **8.69 M** | 1.33 M |
| committed (padded) cells | 7.87 M → **5.15 M** | 16.18 M → **10.73 M** | 3.35 M → **1.99 M** |
| proof (268.2-bit) | 1,258,042 → **1,238,300 B** | 1,296,042 → **1,264,466 B** | 1,237,614 → **1,216,466 B** |
| prove / verify / peak RSS | 260 s → **180 s** / 156 ms / 1.29 GB | 478 s → **149 s** / 108 ms / 1.73 GB | 130 s → **45 s** / 94 ms / 0.99 GB |
| root (= Lean `stateRoot` / `m5a-tool apply`) | `1db48e38…249628` | `61f5330a…07993006` | `b2142cc9…bd07895` |

Prove times are on the shared host (load ≈ 30, 8 threads). Logs:
`logs/M5a3-{T1,T2,syn-bval}-{prove.log,stats.json,cost.json}`; hashes: `logs/SHA256SUMS-v4`.
The prover binary changed only in its table-name list (`WSL`, `WSP`). With the working-set chip
halved, T2's committed cells are now the SHA-256 table (4.46 M, trie side) and the SHA-512 chip
(5.44 M; 416 of 512 compressions used).

Multi-segment check: T2 with `--segs 3 --extra-writes 5` (47 writes, 3 segments, 5 keys written
twice) and `--segs 7 --extra-writes 10` (52 writes, 7 segments) precheck (every constraint, every
bus); 426 / 472 compressions (still 2¹⁶ rows). The first **proves**: 1,265,600 B, prove 121 s,
verify 176 ms, root `61f5330a…` (`logs/M5a3-T2-seg3x5-*`).

#### Mutants [M] (on the final AIR, `logs/M5a3-mutants.txt`)

**T2 22/22, T1 14/14, synthetic 12/12, T2-seg3x5 4/4 rejected** (each fails the precheck and the
prover refuses it). The 33 of M5a-2 (rerun; `omitwrite` now fails `WRITE` + `WM`), plus new ones
for every new constraint and bus: `wsstale` (an access consumes another value than the latest →
`WM`), `wssib` (an untouched sibling differs between the old and new tree → `WSP` keep
constraint), `wsdrop` (a path node with no touched child → `WSP` child constraint), `wsabsorb` (an
inactive path row absorbs a child → `(1 − act)·tl`), `wsleaf` (a touched leaf with another
pre-length, consistently hashed → `PT`: its old digest is not the working set's leaf) on T2, T1 and
the synthetic case; on T2 with segments and repeated writes: `wsorder` (two accesses to one key
chained against time order → the `WSA` gap constraint), `wsseg` (a write attributed to another
segment → `WRITE`/`WM`), `wsstale`, `omitwrite`.

#### Lean [K] (std axioms, no `sorry`; `lake build StateM5a` prints the audit)

* `Merkle.batch_update_sound`: a segment's update is a description `Upd` (untouched subtree
  `keep h`, touched leaf `leaf o n`, path node `node l r`); with a collision-free node hash, if its
  old digest is the working-set root then every touched leaf's old digest is the working set's leaf
  at its position (`Agrees`) and its new digest is the root of the working set with exactly those
  leaves replaced (`apply`). `root_succ_split` (+ `up_take`, `up_drop`): the level-by-level root
  (`WSN`) is the hash of the halves' roots, so `RCH` means the same thing for both tables.
  `write_access_sound` (one path) is kept.
* `WsCost.chain_sound` / `chain_sound_any`: offline memory checking for one entry — if the sends
  `(v0, 0) :: accesses.(new, t)` are a permutation of the receives `(vEnd, idEnd) ::
  accesses.(old, prev)` and every access has `prev < t`, then sorted by time the accesses have
  distinct times, each read its predecessor's value (`Reads`), and the closing value is the
  latest write (`chain_strict` gives the strict order).
* Field level (BabyBear, from the exported tables' constraints): `wsa_gap` (gap bytes ⇒ `idp < t`
  for times `< 2²⁴`), `wsp_keep` (untouched child: one digest in both trees), `wsp_child` (an
  active path node has a touched child), `wsp_off` (an inactive row has no multiplicity),
  `wsl_kd` (a touched leaf's `kd` limbs are its bytes' 16-bit values); `leafLimb_inj`.
* Open (as for the other buses): the bus-level step — that `WM`'s balance yields the per-entry
  permutation of `chain_sound` (filter by `(seg, kd)`), and that `PT`/`RCH` balance yields an
  `Upd` fitting depth `D` whose old digest is `RCH(seg)`; the leaf block's injectivity over the
  whole block (`leafLimb_inj` is the per-limb step); the SHA-512 chip's interface in Lean.

## M5a-2 (third session, 2026-11-03): batched FINAL in the AIR

Sections below this one describe M5a as first built (every walk row hashes its old and its new
node); the tables and the Lean list there are still valid, with the changes listed here.

### Design

Each trie node is hashed **once**:
* **pre-state nodes**: the first row that reads a node hashes it (`gsha = 1`) and publishes its
  record on a new bus `VER` under its digest, with a multiplicity (`vm`, 7 bits) equal to its other
  readers; every other reader — INTAKE finds and FINAL changes alike — receives the record from
  `VER` instead of hashing (this also batches INTAKE: T2's root was hashed by 53 walks, now once);
* **new nodes**: a node a later change rewrites is not hashed; its row publishes the record on
  `VER` under a *version id* (`nref = 1`; the id is the row's new-node message id
  `ID + 2·rid + 1`, unique per row and table); a node no later change rewrites is *final* and is
  hashed by its row, which publishes it under its digest for later readers (absent deletes read
  without rewriting). A final node's children are final (a rewrite of a child rewrites its parent),
  so its serialization has only digests (`gfin · isn = 0`).
* **refs**: every child slot, every `DOWN`/`UP`/`MATR`/`SPQ`/`SPR`/`SXQ`/`SXR`/`SIBQ` hash field and
  the root chain `TCH` carry a *ref* = (flag, 16 limbs): a digest, or a version id (cell 0 = id,
  others 0). The public ends `TCH(0, 0, prev_state_root)` and `TCH(n, 0, post_state_root)` are
  digests, so the last change must hash the root.
* **records**: a `BR` record is 17 `VER` messages (16 slots `(f, f·isn, f·32 bytes)` and one value /
  memory part), an `SN` record 3 (header with `isL`, `klen`, 36 payload bytes, memory limbs; key
  nibbles 0–31, 32–63): the backend caps a message at 63 fields. Every part carries the full ref.
  A key longer than one row (`cont`) is never on `VER` (always hashed, old and new).
* **range checks**: a published (unhashed) node's 8 memory bytes are looked up in `RNG` (the SHA
  table no longer checks them), as are a written branch value's length bytes.

No timestamps are needed: records are immutable values keyed by unique ids (a persistent store),
so the `VER` bus defines a function `σ : id → record`; the trie between changes is the expansion
of `TCH`'s ref through `σ` (`Store.Exp`). The trace generator runs twice: pass 1 (= the M5a
trace, still valid: `--unbatched`) finds every version's readers; pass 2 assigns `gsha`, `nref`,
`vm`, `vmn`.

### Results [M] (main stack: unified SWIRL, BabyBear Ext12, SHA-384 MMCS, stacked WHIR)

| | T1 (`d3c8/d3/02-h10196-s3`) | T2 (`d3c9/d3/00-h10018-s0`) |
|---|---|---|
| trie-node rows | 156 (unchanged) | 623 (unchanged) |
| SHA-256 messages of trie rows (M5a → batched) | 212 → 84 | 874 → 172 |
| SHA-256 blocks of trie rows | 524 → 172 | 2,370 → 327 |
| trie-row SHA-256 cells | 4.96 M → 1.64 M (−67 %) | 22.39 M → 3.12 M (−86 %) |
| cells per trie-node row (incl. SHA) | 32.6 k → 11.3 k | 36.7 k → 5.8 k |
| total used cells (`cost.py`) | 8.15 M → 4.83 M | 34.25 M → 14.97 M |
| committed (padded) cells | 14.52 M → 7.87 M | 47.33 M → 16.18 M |
| versions published / pre-state nodes hashed / final nodes hashed | 21 / 48 / 36 | 211 / 82 / 90 |
| proof (M5a → batched) | verifies: 1,243,380 → **1,258,042 B**, 268.2-bit, prove 260 s (8 threads, host load ≈ 45), verify 179 ms, peak RSS 1.52 GB | verifies: 1,533,468 → **1,296,042 B**, 268.2-bit, prove 4,392 s (throttled) → **478 s**, verify 190 ms, peak RSS 16.4 → **2.67 GB** |
| root | `1db48e38…249628` = Lean `stateRoot` | `61f5330a…07993006` = Lean `stateRoot` |

The final-node count matches the batching model's `fin` count (T1 36, T2 88 + 2 nodes with keys
longer than one row, which are always hashed). The prover is the M5a binary (unchanged,
`logs/SHA256SUMS-v2`); AIR hashes in `logs/SHA256SUMS-v3`. With the trie side batched, the
SHA-512 working-set chip (10.9 M of T2's 16.2 M committed cells, `WSA` 170 k cells per write) is
now the dominant state cost.

**Root equality.** `tracegen.py` asserts the circuit's last `TCH` root (a digest) = its
transcription's `applyChanges` root = the case's `post_root`; that root is the Lean `allFeatures`
run's `stateRoot` (T1, T2), and `m5a-tool apply` recomputes it with the Lean spec itself
(`revealTrie` → `applyChanges ∘ sortKV` → `rootHash`; `run.sh` step 2b) — equal on T1, T2 and
the synthetic case.

**Mutants** [M] (`logs/M5a2-mutants.txt`, on the final AIR): **T2 17/17, T1 9/9, synthetic
7/7 rejected** — each fails the precheck and the prover refuses it. The 12 of M5a, rerun, plus
five for the batched path: `verslot` (a row reading a version holds another off-path child byte
→ `VER` unbalanced), `vernid` (it claims another version's id → `DOWN` + `VER`), `vmcount` (a
pre-state node published for one reader more → `VER`), `finroot` (the last change leaves the
root as a version id → `TCH` against the public `post_state_root`, + `RNG`), `nidforge` (a version
under another row's id → the id constraint). Synthetic case: `bvalue` (`oUV` stores another value
byte → the `dvh` constraint), `bvmem` (`oDV` memory + 1 → the memory chain); its `node` and
`finroot` tampers do not apply (their helpers expect a leaf / branch root; that trie's root is an
extension). Proof sizes barely move: the WHIR query part (~0.94 MB) dominates and depends on
columns, not rows.

### Completeness: branch values (synthetic case)

New `BR` ops for a walk key that ends at a branch (a key that is a prefix of another): `oUV`
writes the branch value (over an old value or none; `valueMem` in the memory chain), `oDV`
deletes it keeping the branch (≥ 2 children, `squashBranch`'s last case), `oDZ` an absent delete
(no value; result `SAME`). The rewritten branch's value is now its own columns (`nhv`, `nvl`,
`nvh`; equal to the old value on every other op). No corpus case has them, so `synth.py bval`
builds a NEAR-shaped pre-state (`0x00 ‖ account`, `alice` next to `alice.near`, 18 keys) and 7
changes exercising `oUV` ×3, `oDV`, `oDZ`, `oFV` ×5, an extension-internal absent delete and
`extendChild` onto a kept branch; the Lean spec oracle confirms its root. **It proves** (D = 4): 26 `BR` / 31 `SN` rows,
1,237,614 B, 268.2-bit, prove 130 s, verify 172 ms (`logs/M5a2-syn-bval-*`).

### Lean [K] (std axioms, no `sorry`)

* `Store` — the batched-FINAL memory argument: `Ref` (digest | version id), records with ref
  children, the store expansion `Exp σ` and `exp_functional` (a ref expands to one trie: the trie
  one change leaves is the trie the next starts from); `Rv` (reveal: stubs replaced by nodes hashing
  to them) with `rv_refinedBy` (revealing keeps refinement of a revealed, well-formed witness;
  `Sha256CR` + `NodeSerInj` through `refinedBy_of_hash`) and `rv_collapse` (collapsing final nodes
  to digests keeps it; no assumption); `change_step` (one change, any step relation that carries
  refinement), `upsert_step`, `find_step` (INTAKE finds on the revealed pre-state), and
  `batched_upserts`: from `TCH(0) = prev_state_root` through every upsert change to a digest
  `post`, the spec's fold of the changes on the witness trie succeeds with root hash `post`;
  **`batched_changes`**: the same for every change, upserts and deletes (`del_step` from
  `Refine.del_refinedBy`), with `applyChanges` and `rootHash` themselves. Premises: `Sha256CR` and
  `KeepsFW` (applied changes keep the witness revealed and well-formed: a spec property, open);
  `NodeSerInj` is discharged by `SerInj.nodeSerInj`.
* `FieldVer` — the version constraints at field level: a `VER` publisher of an old node hashed it
  (`br_vm_gsha`, `sn_vm_gsha`) under its digest with digest children (`br_gsha_dig`,
  `br_gsha_isn`, `sn_gsha_dig`); a publisher of a new node has one (`*_vmn_gnew`); a version id is
  the row's own (`br_vid`, `sn_vid`); a continued key never uses `VER` (`sn_cont`).
* `StepsBV` — `br_upsert_value`, `br_del_value_keep`, `br_del_value_absent` (the spec steps of
  `oUV`, `oDV`, `oDZ`).
* `SerInj` (Lean sub-lane) — **`nodeSerInj : NodeSerInj` proved** from the spec's encoder (tag
  byte; `u16`/`u32`/`u64` injective under `wf`'s bounds, `leN_inj`; `hexPrefix_inj`,
  `packNibbles_inj`; bitmap + 32-byte child hashes slot by slot, `kids_inj`; a `ValueRef` pins the
  slot, `slot_of_valueRef`). `Shallow` now also requires value slots to be refs (a row holds a
  `ValueRef`; with a revealed row value the statement is false). `refinedBy_of_hash'` needs only
  `Sha256CR`.
* `Refine` (sub-lane) — **`del_refinedBy`**: `del` commutes with refinement for the general spec
  `del` (same deleted flag, refining result; via `squashBranch_refinedBy`,
  `extendChild_refinedBy`), `dchain_witness`, `change_del_witness`, `findRef_refinedBy`;
  **`rows_refinedBy`**: a well-formed rows' trie with ref slots and the root hash of a revealed
  well-formed trie refines it (`nodeSerInj` at every node, `Sha256CR` only); `find_spec`,
  `upsert_spec`, `del_spec` against any spec partial trie.
* `FieldRows2` (sub-lane) — `sn_hexPrefix`: a short-key `SN` row's `hp` bytes are exactly
  `hexPrefix` of its `klen` nibbles and `hplen = 1 + klen/2` (from the `a`/`k`/`ha`/`hp`/`odd`
  constraints, nibbles < 16); `br_sel`: a descending `BR` row has one selector, at a present slot,
  equal to the looked-up nibble.

### Open after M5a-2

1. Bus level: that the rows' `VER`/`DOWN`/`UP` traffic yields `Rv`, the chain relations and
   `Exp` (with `FieldVer` + `rid` = row index giving unique ids, the `VER` receives are a function
   of the ref) and the field facts building `wf` / ref slots of the rows' trie; `KeepsFW`; chain
   constructors for `oUV`/`oDV`/`oDZ`; field level: `BR` children block from `rank`, the other
   one-hot bundles, `cont` rows / `SNC`, `WS*`.
2. Completeness still missing: the squash after a value delete leaving one child, squash to a
   value leaf / onto an extension or branch sibling (`extendChild [i]` with a non-leaf), splits
   where one key ends at the new branch, a mismatch past a head's 63 nibbles, the empty trie.

## Result on T1 (`d3c8/d3/02-h10196-s3`)

| | |
|---|---|
| state accesses | 17 working-set keys (the clean-room checker's lookups ∪ the committed keys), 10 committed changes (7 upserts, 3 deletes), cross-checked against the Lean `allFeatures --emit-full` write log (`lean_matches_clean_room: true`) [M] |
| trace | 156 trie-node rows (`BR` 96, `SN` 60), 229 SHA-256 messages / 541 blocks, 270 SHA-512 compressions, 171 `KEY` rows, 51 `KCMP` rows [M] |
| precheck | every constraint on every row, every bus balanced (30,591 distinct messages) [M] |
| proof | **verifies** on the main stack (unified SWIRL, BabyBear Ext12, SHA-384 MMCS, 42-B digests, stacked WHIR): 1,243,380 B, 268.2-bit calculator, prove 193.3 s on 8 threads, native verify 93 ms, peak RSS 1.81 GB [M] (`logs/prove.log`) |
| root equality | the circuit's post-state root (the `TCH` chain's last root, closed by the public tape) = `1db48e38…249628` = the Lean run's `stateRoot` = the main transition's `post_state_root` (T1 has no implicit transitions, so it is also the header's `prev_state_root`) [M] |
| mutants | 4/4 rejected [M] (`logs/mut-*.log`): **node** (the first written key's leaf with memory usage + 1, parent's child hash unchanged) → `DOWN` (hash link) and `TCH` unbalanced; **prevalue** (one key's claimed pre-value length + 1) → `UP` (INTAKE answer) unbalanced; **omitwrite** (one write access dropped) → `RCH`, `WRITE` and 224 SHA-512 interface messages unbalanced; **postroot** (statement's post-state root, one bit) → `TCH` unbalanced. Each was then handed to the prover, which refuses (non-zero LogUp sum) |

The pre-state root is `9da2fa38…0d4c3f70`.

## What the AIR is

The AIR is a `ZkFormal.Air` value in Lean (`lean/StateM5a/{Trie,Ws,Air}.lean`), exported by
`m5a-tool air D` and interpreted unchanged by the prover (the pq-state-port interpreter).
Tables (width / constraints incl. the generated multiplicity-bit booleanity / interactions):

| table | rows | role | w / c / i |
|---|---|---|---|
| `SHA` | per block | the unchanged SHA-256 block table (`ZkFormal.Sha.Table`, soundness `sha_digest_contract_closed`) | 544 / 1028 / 17 |
| `KEY` | per key byte | key bytes → SHA-256 (the key digest the working set binds) and the `NIB(kid, idx, nibble)` / `KLEN` lookups | 63 / 59 / 6 |
| `BR` | per branch visited | old branch (16 slots, value ref, memory) → old serialization + digest; op (8 kinds, below); rewritten branch → new serialization + digest; 4×16-bit memory chain | 795 / 1331 / 1130 |
| `SN` | per leaf / extension visited | key as ≤ 64 nibbles (looked up in `KEY`), `hexPrefix` bytes, old/new serialization; 8 ops | 419 / 664 / 303 |
| `KCMP` | per common-prefix nibble | `ORD(ka, kb)`: key `a` < key `b` | 14 / 26 / 6 |
| `WSB` | 2^(D+1) | the working-set leaves, phase 0 (INTAKE) and phase 1 (FINAL); leaf digest = 2 SHA-512 compressions; INTAKE find walk per key; FINAL change walk per written key, chaining the trie root | 151 / 152 / 41 |
| `WSN` | 2·(2^D − 1) | inner nodes, SHA-384(`left48‖right48`) | 67 / 27 / 21 |
| `WSA` | per write access | old leaf → new leaf on one depth-`D` path (`4 + 2D` compressions), advancing the `RCH` root chain | 518 / 254 / 227 |
| `SHA512`, `SHA512T` | 128 per compression | the native SHA-512 compression chip v4 (`native/sha384-air4`, bus ids moved to 100–103) | 83 / – / – |
| `TAPE` | public | the write log `WRITE(kd, ref)` and the root chain's ends `TCH(0, prev_state_root)`, `TCH(n, post_state_root)` | – |

Walk protocol: a walk is one spec trie operation along one key (`w` = leaf index for INTAKE
finds, `2^20 + index` for FINAL changes). The parent sends `DOWN(w, d, childHash, kid, mode,
value)`; the child row must hash to `childHash` (it receives its own digest from `SHA`); it returns
`UP(w, d, kind, newHash, newMem, oldMem, leaf descriptor, find answer)`. Result kinds: find answer,
hashed node (upsert), hashed branch (delete), leaf descriptor (delete: a leaf whose key grows by
`extendChild` on the way up, materialized by `SN.oLM` where a branch embeds it), nothing.

Ops implemented (T1 uses the first set, T2 all of them): `BR` find-descend / find-absent (empty
slot) / upsert-descend / upsert-new-leaf / delete-descend with the branch kept (child hashed, leaf
descriptor, child removed) / delete with one sibling leaf left (`squashBranch` → `extendChild`);
`SN` leaf find / replace / delete / sibling read / materialize, extension find / upsert / delete
with a leaf-descriptor child.  **Added for T2 (second session):** `BR.oFV` find ending at a branch
(answers its value; `KLEN` proves the key ends), `BR.oDA`/`oDS` absent delete at an empty slot /
below an unchanged child, `BR.oSL` a split's new branch (two children: the walk's new leaf and the
old-side child); `SN.oLA`/`oEA` absent finds and `oLZ`/`oEZ` absent deletes at a leaf / extension
with another key, `SN.oES` delete below an unchanged child, `SN.oEB` delete whose child is a kept
branch (`extendChild k (branch …)`, the squash onto a branch), `SN.oLX`/`oEX` upsert splits
(`splitLeaf`/`splitExt`, both keys continuing past the common prefix), `SN.oEP` the new extension
over the common prefix (`wrapExt`), `SN.oEM` the re-keyed extension `xs ↦ c`.

An absent / split row carries a **mismatch witness**: the nibbles before `jm` are looked up against
the walk key, and at `jm` the walk key holds another nibble (`mN`, inverse of `y − kj`), ends (`mK`,
`KLEN`) or continues past a leaf's key (`mL`).  Nibbles no key lookup covers are range-checked by
the new 256-row `RNG` table (`v` and `v + 240` in `[0, 256)`); split rows look them up against a
second key `kid2` (the old leaf's full key, or the extension's path padded to bytes, registered in
`KEY`).  A new result kind `SAME` (`del` returned `deleted = false`) carries the node's own hash,
so the root chain `TCH` repeats the root on an absent delete.  **Long keys:** a continued `SN` head
(`cont`) holds `62 + odd` nibbles, and `SNC` rows carry 64 nibbles each (chained by `KC`/`KCR`),
sending `hexPrefix` bytes `32c … 32c+31` (`Layout.hpAt_chunk`).  New buses `SPQ`/`SPR`/`EPQ`/`SXQ`/
`SXR` (splits), `KC`/`KCR` (chains), `RNG`; `MATR` now carries the key id (a split materializes two
leaves at one depth).  Not in the menu (completeness gaps, never soundness): splits where one key
ends at the new branch, upsert/delete at a branch value, squash to a value leaf or onto an
extension sibling, a mismatch past the head's first 63 nibbles, the empty trie.

Working set: leaf = `(sha256 key, pre (present, len, sha256 value), cur (…), written)` in 16-bit
fields; FINAL walks run in leaf order, which `KCMP` makes the spec's raw-key order (`sortKV`), so
the circuit applies `applyChanges` in the spec's order. In M5a the writes come from the public
tape (stand-in for M5b's STATE rows) and the per-segment state is the `RCH` root (a boundary
would carry it).

## Lean lemmas ([K], `lean/StateM5a/`, `lake build StateM5a` prints the axiom audit)

Every theorem depends on at most `propext`, `Classical.choice`, `Quot.sound`; no `sorry`.

| AIR | lemma | spec function it links to |
|---|---|---|
| `BR` | `Steps.br_findRef`, `br_upsert_descend`, `br_upsert_new`, `br_del_keep` (+ `squashBranch_keep`), `br_del_one` | `PTrie.findRef`, `PTrie.upsert`, `PTrie.del`, `squashBranch`, `extendChild` (via `Kids.at`/`Kids.put`: `kids_findRef_at`, `kids_upsert_at`, `kids_delAt_at`) |
| `BR` | `Layout.kidsBitmap_eq`, `hashes_eq`, `block_at` | `PTrie.hashOf (.branch …)`'s bitmap and children block = the row's `Σ f_i 2^i` and slot `i` at offset `32·rank_i` |
| `SN` | `Steps.leaf_findRef`, `leaf_upsert`, `leaf_del`, `leafMem_eq`, `ext_findRef`, `ext_upsert`, `ext_del_leaf` | the leaf / extension cases of the same functions |
| `SN` | `Layout.hexPrefix_eq` | `hexPrefix k leaf` = the row's `hp_m` formula, `1 + |k|/2` bytes |
| `KCMP` | `Order.nibLt_bytesLt` | `bytesLt` (the order of `sortKV`, hence of `Ovl.finalize`) |
| `WSA` / `WSN` | `Merkle.write_access_sound` | the working-set root after a write = the root of the leaf list with that leaf replaced (collision-free `H`) |
| FINAL root | `Steps.applyChange_upsert`, `applyChange_del` | `applyChange` (one committed change of `applyChanges`) |
| `KEY` | `KeyField.key_row_nibbles` — **field level**: from `Key.table`'s constraints vanishing over BabyBear on a row, the row's `NIB` nibbles are `NearSpec.nibbles` of the byte it hashes | `NearSpec.nibbles` |
| T2 rows | `StepsT2.br_findValue`, `br_del_absent`, `br_del_same`, `leaf_findRef_absent`, `leaf_del_absent`, `ext_findRef_absent`, `ext_del_absent`, `ext_del_same`, `ext_del_branch`, `leaf_split`, `ext_split`, `wrapExt_cons`, `kids2_at`; mismatch witness `ne_of_mismatch`, `not_isPrefix_of_mismatch` (`k[jm]? ≠ key[jm]?`) | the new cases of `findRef`/`upsert`/`del`, `splitLeaf`, `splitExt`, `extendChild` |
| `SNC` | `Layout.hpAt_chunk` | `hexPrefix` byte `32c + m` = the nibble pair at key offset `64c − 2 + odd + 2m` |
| `KCMP` / `SN` / `BR` / chains | **field level** (`FieldRows`): `kcmp_fin_lt` (`xb − xa − 1 = Σ 2^t db_t` ⇒ `xa < xb`), `sn_mismatch_ne` (`mN = 1` ⇒ `y ≠ kj`), `br_keep` (kept branch ⇒ `Σ nf ≥ 1`, and `≥ 2` without a value), `memChain_sound` (the 16-bit limb chain ⇒ the exact `nw + minus = m + plus`), `onehot_of_sum` | the premises of `Order.nibLt_bytesLt`, `ne_of_mismatch`, `squashBranch_keep`; the memory arithmetic of the step lemmas |
| walks | `Walk.fchain_sound`, `uchain_sound`, `dchain_sound`, `change_upsert`, `change_del`: a chain of row steps (`FChain`/`UChain`/`DChain`, one constructor per row op) is `findRef`/`upsert`/`del`/`applyChange` on the trie the rows reveal; `fchain_witness`, `uchain_witness`: the same answer (slot up to `SlotRefines`) and the same new root hash on any trie the rows' trie refines; `refinedBy_of_hash` (premises `Sha256CR`, `NodeSerInj`) | `PTrie.upsert_refinedBy`, `hashOf_refinedBy` |

What these do not yet give (open, [S]): (1) field level: done for `KEY` (nibbles), `KCMP` (order),
`SN` (mismatch), `BR` (keep condition) and the `BR`/`SN` memory chains; open: the `SN` key /
`hexPrefix` layout from its 64-term sums (`hexPrefix_eq` is record level), the `BR` children-block
placement from `rank`, the per-op one-hot bundles (helper `onehot_of_sum`), `SNC`, `WS*`, and the
bus-level step (`DOWN`/`UP` balance ⇒ the chain constructors); (2) walk composition: proved on the
rows' trie and carried to the witness trie for finds and upserts given `t₁.refinedBy t₂`; open:
that refinement for the whole rows' trie (an induction along the chain from `refinedBy_of_hash`),
`NodeSerInj` itself (decode ∘ encode of the node preimage: stated, not proved), and
`del_refinedBy` (deletes are proved on the rows' trie only); (3) the SHA-512 chip's interface
soundness (`FAITHFUL-v4.md`, not Lean) used by `write_access_sound`'s `H`.  `Sha256CR` / `Sha384CR`
are definitions taken as premises, never axioms.

## Cost [M] (`cost.py`, `logs/T1-cost.json`; committed cells, before power-of-two padding)

| item | cells |
|---|---|
| per trie-node row, mean | 32,453 (`BR` 42,009 incl. SHA-256 of old + new node; `SN` 17,165) |
| per INTAKE find (T1: 17 walks, 93 rows, 23,671 cells/row) | 129,495 (old nodes only) |
| per FINAL change (T1: 10 walks, 63 rows incl. sibling/materialize, 45,417 cells/row) | 286,132 (old + new nodes) |
| per working-set key | 10,468 (`KEY` + `KCMP`) + 43,064 (`WSB`: two leaf digests, both phases) |
| per write access (`WSA`, D = 5) | 149,254 (14 SHA-512 compressions + the row) |
| tree build (`WSN`, D = 5, both phases) | 662,842 |
| T1 total used | 8.13 M (padded and committed: 14.52 M; the SHA-256 table pads 9,426 rows to 2^14, the SHA-512 chip 34,560 to 2^16) |

The SHA-256 node hashing dominates: a 16-child branch is 523 bytes = 9 blocks = 83 k cells per
message, and FINAL rehashes the shared upper path once per change (nearcore batches the changes;
doing the same — one rewrite per touched node — roughly halves FINAL).

## Commands

```sh
research/near-compression/e2e-general/m5a/run.sh <case dir> <out dir> [check|prove|mutants]   # D=5 (T1)
D=6 research/near-compression/e2e-general/m5a/run.sh <T2 case dir> <out dir> prove              # T2
python3 research/near-compression/e2e-general/m5a/batch_cost.py <out>/state.json <out>/dump <out>/names.json
# M5a-2: synthetic branch-value case (D=4); the spec oracle alone: m5a-tool apply <state.json>
python3 research/near-compression/e2e-general/m5a/synth.py bval <out>/state.json
D=4 research/near-compression/e2e-general/m5a/run.sh - <out> prove
UNBATCHED=1 …/run.sh <case> <out> check     # the M5a (every node hashed) trace, still valid
```

1. `nearspec-v3-check-successor --tier allFeatures --emit-full` (the Lean write log) and
   `extract_state.py` (the clean-room checker's nodes, lookups and committed overlay, cross-checked
   against the Lean log);
2. `lake build m5a-tool` + `m5a-tool air D` (the AIR and its column names);
3. `tracegen.py` (the spec recursions of `ptrie.py`, a transcription of `PTrie.findRef`/`upsert`/
   `del`/`applyChanges`; it asserts the post-state root against both the transcription and the
   checker before writing anything);
4. `prover/` (`cargo build --release`), `check | prove | mutant`.

Builds: Lean from `.lake` copied from the main checkout; cargo into
`/data/illia/nearproof-deps/e2e-m5a/target` from an own copy of the pq-state-port backend tree
(overlay hash `051a037b…`). One deviation from pq-state-port: the per-table `maxLog` cap hook
(`max_log_trace_height`) does not exist in this backend tree and is not passed to keygen (the trace
generator respects every cap). Binary hashes: `logs/SHA256SUMS` (first session), `logs/SHA256SUMS-v2`
(second session; the T2 proof).

## Result on T2 (`d3c9/d3/00-h10018-s0`) — second session, 2026-11-03

| | |
|---|---|
| state accesses | 52 working-set keys (D = 6), 42 committed changes; Lean write log = clean-room overlay [M] |
| spec cases | finds: 10 absent at a leaf, 8 absent at an extension, 1 ending at a branch value; upserts: 8 `splitLeaf`, 1 `splitExt`, 13 new leaves; deletes: 2 absent at a leaf, 1 absent at an empty slot, 1 extension over a kept branch (`extendChild k (branch …)`), 2 `squashBranch` → leaf descriptors; keys of 74, 76, 78, 80 and 90 nibbles (24 `SNC` continuation rows) [M] |
| trace | 623 trie-node rows (`BR` 376, `SN` 247), 24 `SNC`, 929 SHA-256 messages / 2,425 blocks, 1,006 SHA-512 compressions, 1,127 `KEY`, 498 `KCMP`; ops census in `logs/T2-stats.json` [M] |
| precheck | every constraint on every row, every bus balanced (140,241 distinct messages) [M] |
| proof | **verifies** on the main stack: 1,533,468 B, 268.2-bit calculator, verify 158 ms, peak RSS 16.4 GB; prove 4,392 s on 8 threads — the shared `zkbuild.slice` sat at its 40 GiB memory-high mark (sibling replays) and throttled the prover to ~1.3 cores, so this time is not representative (T1: 193 s at 14.5 M cells; T2 is 47.3 M) [M] (`logs/T2-prove.log`) |
| root equality | the circuit's post-state root (`TCH`'s last root, closed by the public tape) = `61f5330a…07993006` = the Lean run's `stateRoot` = the transcription's `applyChanges` root (asserted by `tracegen.py` before writing) [M] |
| mutants | **12/12 rejected** [M] (`logs/T2-mutants.txt`): the four statement-level mutants of T1 (node → `DOWN`/`TCH`, prevalue → `UP`, omitwrite → `RCH`/`WRITE`/SHA-512 interface, postroot → `TCH`) and one tampered row per new row type: `absent` (a present-key leaf find recast as absent with a fake mismatch) and `extabsent` (one more matching nibble claimed) → mismatch constraints; `branchval` (`oFV` answers "no value") → value-zero constraint; `split` (old-side child moved to another slot) → `NIB` and SHA-256 byte buses; `splitext` (`cm` + 1) → the `xm` constraint; `absdel` (mismatch where the nibbles agree) → the inverse constraint; `squash` (`oEB` memory + 1) → the memory chain; `chain` (an `SNC` nibble changed, its hp byte adjusted) → `NIB`/`RNG`/SHA-256 bytes. Each is then refused by the prover (~30 s) |

T1 on the extended AIR: the same 156 rows, precheck OK (the new tables are idle there).

### FINAL batching (nearcore's order): measured model, not yet the AIR

`batch_cost.py` (`logs/T{1,2}-batch.json`) counts the SHA-256 work of FINAL as proved now (every
change walk hashes the old and the rewritten node of every row) against nearcore's `Trie::update`
order, which is also the spec's (`PTrie.upsert`/`del` never hash; only `rootHash` of the final trie
does): apply the sorted changes to the in-memory trie, then hash each touched pre-state node once
(authentication) and each node of the final trie once.  Exact counts on the chunk [M]:

| | now (cells) | batched (cells) | saving | batched, reusing INTAKE's pre-node digests |
|---|---|---|---|---|
| T1 | 2,820,640 (119 msgs) | 1,502,528 (40 open + 36 final) | **46.7 %** | 713,184 (74.7 %) |
| T2 | 14,642,848 (584 msgs) | 2,650,368 (58 open + 88 final) | **81.9 %** | 1,555,296 (89.4 %) |

Every pre-state node a change walk reads is also on an INTAKE find path (the written keys are in
the working set), so with digest reuse only the final trie is hashed.  Of T2's 34.2 M used cells
(`cost.py`) FINAL hashing is 14.6 M; batching takes ~12 M off (35 % of the total).  The AIR change
this needs is in *Next steps* (an offline-memory node store instead of hash-addressed versions).

## Next steps (as of the second session; items 1–3 are done or superseded by M5a-2 above)

1. **Batched FINAL in the AIR** (the model above; done in M5a-2 with immutable versions instead of timestamps).  Per-change walk rows stay (narrow, no SHA) but
   address in-memory nodes by id through a node store bus `NODE(nid, t, record)` with timestamps
   (`t` = change index; read `t_r < t`, write `t`; Blum/Spice offline memory checking), records
   holding keys as `(kid, start, len)` references into `KEY` and children as hash-or-nid slots.
   `OPEN` rows hash a pre-state node once (or take its digest from the INTAKE walk that hashed it)
   and create its record; `FIN` rows hash each final node once, children first (`HASH(nid, h)`),
   the root's hash closing `TCH`.  Nid freshness from `(change, depth)`; key equality across
   records by `KCMP`-style segment rows.  Lean: the chain lemmas of `Walk` stay, the memory argument
   replaces the hash link for in-memory nodes.
2. **Lean**: `NodeSerInj` (decode ∘ encode of `PTrie.hashOf`'s preimage), the refinement of the
   whole rows' trie from `refinedBy_of_hash` along a chain, `del_refinedBy`; field-level `SN`
   key/`hexPrefix` layout, `BR` children block, the op one-hot bundles, `SNC`, `WS*`; then the
   bus-level step from `DOWN`/`UP` balance to the chain constructors.
3. Completeness gaps: splits where one key ends at the new branch (`oldEnds`/`newEnds`),
   upsert/delete at a branch value, squash to a value leaf / onto an extension sibling, a mismatch
   past the head's 63 nibbles, the empty trie.
4. M5b replaces the public `WRITE` tape by STATE rows and cuts segments at the `RCH` root.  The
   state-side boundary stays `(RCH root, TCH root, change index)`; it maps onto lane E's `stRoot`
   field of §3.2 once §3.5's `CM` boundary record is published (not yet on main).
