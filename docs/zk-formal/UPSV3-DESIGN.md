# `upsV3`: the `0x0f` upsert table (M7b design, for review)

Status: **M7c step 1 done** (pass-through mode for empty-key extensions, `UPB` child id, id packing `512τ + j`), 2026-10-06. Branch `lane/v3-trie-h`, built on `lane/v3-trie` at c1fadc7b. M7b's version rejected empty-key extensions on the path; the lead decided that they must be handled (§1.1).
Inputs: STATUS-V3-TRIE §2.3, §2.3.1 and §2.3.2; `spec/lean/NearSpec/TrieUpsert.lean`; `Spec/Absent.lean`; and `Link/Chain3.lean`, where `UpsE (τ, mid, post)` is the abstraction that this table refines.

Labels used below:
* **proved**: kernel-checked in Lean.
* **tested**: model-checked by the script in §9.
* **argued**: the soundness sketch, which is the job of M7c–M7e.

| deliverable | file | state |
|---|---|---|
| table `UpsV3.table` | `zk-formal/ZkFormal/NearV3/Tables/Ups.lean` | builds; degree 4 |
| bus ids | `zk-formal/ZkFormal/NearV3/IdsUps.lean` | `UPB 25`, `MEMD 23`; `S0F 59`, `SPOST 60`, `SPLEN 61` as agreed with v3-sched; `K_VUPS 12`, `idx = 512τ + j` |
| `nodeV3` delta, not applied | `zk-formal/ZkFormal/NearV3/Tables/NodeUpb.lean` (`NodeV3.tableU`) | builds; §7 |
| budget | `zk-formal/ZkFormal/NearV3/BudgetUps.lean` | **proved** (`decide +kernel`; axioms `propext`) |
| model check | `zk-formal/test/UpsExport.lean`, `zk-formal/test/upsv3_model.py` | **tested**: 3,740 random instances (2,540 with empty-key extension chains), 0 failures (§9) |

## 0. Budget (proved, `BudgetUps.lean`)

| table | width | interactions | aux g=1 | degree g=1 | `W_eq` g=1 | aux g=3 | degree g=3 | `W_eq` g=3 | maxLog |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `upsV3` | 187 | 15 | 15 | 4 | **331** | 6 | 8 | **291** | 22 |
| `nodeV3` + `UPB` delta | 186 (+1) | 20 (+2) | 20 | 4 | 370 (+17) | 7 | 8 | 298 (+1) | 22 |
| lane total (6 tables) | | | | | **1202** (with `VSLOT` and the root binding) | | | **1082** | |

M7b had `upsV3` at 176 columns, `W_eq` 320 / 280. The pass-through mode adds 10 columns
(`dep0‥2`, `kPT`, `up`, `rc`, `pdep`, `cN`, `rcid`, `rdc`) and no interaction. The `nodeV3` delta
is unchanged in size: `cid` is an existing column.

The theorems are `ups_g1`, `ups_g3`, `nodeU_g1`, `nodeU_g3`, `weqTrieU_g1` and `weqTrieU_g3`.
* `upsV3` has 582 constraints, all of degree ≤ 4. Every interaction gate is a column, and every message has degree 1.
* Of the 186 columns, 14 walk-row columns are aliases of part-constant columns. The 32-byte register `reg` is reused by row kind (§2.4).

## 1. Interface

| bus | message | `upsV3` side | gate |
|---|---|---|---|
| `MIDROOT` 24 | `(τ, rid, mid[32])` | recv | `W0` (`rid` → segment constant `rootRid`; the root part's source, M7e) |
| `ROOT` 10 | `(τ+1, post[32])` | send | `W3` |
| `S0F` 59 | `(τ, present, vid)` | send | `W0` |
| `SPLEN` 61 | `(τ, L)` | recv | `W0` |
| `SPOST` 60 | `(τ, pos, b)` | recv | value rows |
| `BYTES` 0 | `(msgId 12 (512τ + j), pos, b)` | send | value and node rows |
| `DIGEST` 1 | `(id, len, d[32])` | recv | fresh windows, `W3` |
| `EDGE` 4 | `(N, I, sym, N2, I2, ek, u)` | chained consumer (recv `u`, send `u+1`) | `mS + mK` |
| `BMAP` 11 | `(N, bm, hasVal, u)` | chained consumer | `mB` |
| `UPB` **25** | `(NPOST(n), pos, pb, len, depth, cid, u)` | chained consumer | `rd` |
| `MEMD` 23 | `(τ, j, i, new_i, old_i, qlen)` | send (child) / recv (parent) | `gMs` / `gMr` |

* The `EDGE` and `BMAP` messages are `walkV3`'s (`Extract/WalkView.lean`).
* `S0F`, `SPOST` and `SPLEN` use v3-sched's numbers and formats (`Sched/Ids.lean`, `Codec.lean`).
* SHA ids: `K_VUPS = 12`, `idx = 512τ + j`. `j = 0` is the new value. `j = 1 … nQ` are the new path nodes `Q_j`, with `nQ ≤ 4 + 399 < 512` (§3.3).

**`UPB` format (binding, lead).** `UPB (NPOST(n), pos, pb, len, depth, cid, u)`. `len`, `depth` and `cid` are existing node-constant / window-constant columns of `nodeV3`, so the delta costs 1 column (`mU`) and 2 interactions.

* **`cid`** is `nodeV3`'s window column: on a window byte, the child record of that window (`PARENT (cid, τ, depth+1, …)` when the child is revealed); off windows it is free. An upper part reads it on the first byte of its target window and checks it against the part below (§1.1).
* **`depth`** is the source record's depth. Each part reads at `pdep` (§3.3): the depth jump between walked records shows where empty-key extensions sit.
* **`len`** locates the `MEM` field of a branch and pins its window count. Without it, a rewritten branch could claim fewer windows and read `memory_usage` from window bytes. The alternative is to read the bitmap and count bits, which costs 16 bit columns and a popcount.

### 1.1 Empty-key extensions on the path (pass-through mode)

`nodeV3` admits empty-key extensions (`eext`: `.ext [] c m`, key `[]`, hex-prefix byte `0x00`, 46 bytes `3 ‖ u32 1 ‖ 0x00 ‖ H(c) ‖ u64 m`). Walks skip them: an `eext`'s `res` is its child's `res`. So a walk edge `N_d → (N_{d+1}, 0)` can jump over a chain of `eext` records, and `N_0` (the head's `rres`) can sit below a chain from the root record `rid`. `PTrie.upsert (.ext [] c m) k v = .ext [] c' (m + c'.memD − cm)` (`isPrefix [] k`, `k.drop 0 = k`), so each of them must be rewritten. `buildFor` can reveal them, and a `RelD0a` witness may contain them, so completeness must cover them (**lead decision**).

* **Discovery.** Every part reads its source at depth `pdep`. The walked records `N_0 … N_D` have depths `dep_0 < … < dep_D` (segment constants, pinned by the reads). The records at the other depths `< dep_D` on the path are the `eext`s: `dep_{d+1} − dep_d − 1` between `N_d` and `N_{d+1}`, and `dep_0` above `N_0`.
* **Pass-through part `PT`.** One per `eext`, 46 bytes. Every byte is copied from the record's post bytes (`UPB`, `spos = qpos`), except the child window, which is the fresh `DIGEST` of the part below, and `MEM`, which is `MEMD`-chained like a descend: `new = m + c'.memD − cm`, truncated at 0, with `m` the record's old usage, `c'.memD` the exact new usage of the part below and `cm` the old usage of its source. The part's type is pinned to an empty even extension: `qte`, `nokey` (so `qhk = 1`), `qodd = 0`, and the copied flag byte is `0`. With `plen = qlen` (from the `MEM` anchor), the source bytes are exactly an `eext`'s.
* **Stepping through.** Each upper part (`RDB`, `RDE` or `PT`) reads the child id `cid` on the first byte of its target window (`rdc`). It must equal `cN`, the source record of the part below, which is carried across the part boundary. So the upper parts follow the parent chain upward from `N_D`, one record per depth.
* **Order.** The upper parts have depths `dep_D − 1, dep_D − 2, …, 0` (`pdep = dep_D − (j − nT)`), and the root part has depth 0. A counter `rc` starts at `D` and drops at each descend. A descend at `rc` reads level `rc − 1` at depth `dep_{rc−1}`, and the root part ends with `rc = 0`. Since the depth falls by exactly 1 per part, the part at depth `dep_d` is the descend of `N_d`, and every other upper part is a `PT`.
* **Bounds.** Chains are bounded by the fuel: `depth ≤ 399` (`nodeV3`), so `dep_D ≤ 399` and `nQ ≤ 4 + 399 = 403 < 512`. The model check uses chains of length 1 … 50 and one chain of length 397 (§9).

**nearcore evidence (note).** nearcore 2.13.4 never builds empty-key extensions. Every `Extension` constructed in `core/store/src/trie/ops/insert_delete.rs` has a non-empty key:
* line 171: leaf split, only when `common_prefix > 0`;
* line 202: extension split, `mid(1)` when `len > 1`;
* lines 252/266: partial prefix, with `0 < common_prefix < len`;
* lines 237/405/417: the key is kept.

Even so, completeness covers every `RelD0a` witness, including tries with `eext` chains on the `[0,15]` path.

## 2. Row layout

One **segment per instance `τ`**, in the following order:

```
W0 W1 W2 W3 | value rows (j = 0, pos 0 … L−1) | Q_1 rows | Q_2 rows | … | Q_nQ rows | next segment or padding
```

### 2.1 Walk rows `W0 … W3` (`wk`, `W0 = sf`, `wt1 … wt3`)

These rows are `walkV3` with the key fixed to `[0, 15]`. The symbols are `START`, `0`, `15`, `END`, given by `symE`.

**Modes.** The modes are `mS` (step), `mK` (absent by key), `mB` (absent at a branch) and `mD = wk − mS − mK − mB` (drain).
* `W0` is the head's `START` edge `(0, τ, START, N0, 0, DOWN)`.
* A step leads to the next lookup position.
* `W1` and `W2` steps are `DOWN` or `KEY` edges. A step on `W3` is a `VAL` edge.
* `mK` uses a `KEY` or `LEND` edge with `nib ≠ sym` (inverse `inv`).
* `mB` uses `BMAP` at position 0. On `W1` bit 0 of the bitmap is 0, on `W2` bit 15 is 0, and on `W3` `hasVal = 0`. The bits are held in `reg` on `W1` and `W2`.
* After an absent row, the remaining rows drain.

**Path records.** The level `lv` is one-hot (`lv0 … lv2`) and starts at 0 on `W1`.
* A step enters a new record iff it lands on position 0 (`enter`). The constraints are `enter·I2 = 0` and `(1−enter)(N2 − N) = 0`. Since nodeV3 edges never land on `(N, 0)` from `N` itself, `enter` is determined.
* A lookup row's record is `N_lv`. The segment constants `N0`, `N1` and `N2` are the **path records**.

**Terminal.** The terminal row `t*` is one-hot (`ts1 … ts3`; column `trm`, expression `trmE`).
* `t*` is the first non-step row, or `W3` if every row is a step.
* At `t*` the walk fixes:
  * `D` (one-hot `dd`): the terminal record's level;
  * `I` (one-hot `ti`): the position inside that record;
  * `x = nib` (`tX`, 4 bits, `px = 2^(x mod 8)`): the record's key nibble, for an absent-by-key terminal other than `LSa`.
* The consumed prefix is `c_D = t* − 1 − I`. The next key nibble is `y = 0` iff `t* = 1`.

**Endpoints.**
* `W0` receives `MIDROOT` (into `reg`) and `SPLEN`, and sends `S0F (τ, pres, vid)`. Here `pres = mS(W3)` and `vid = mS(W3)·N2(W3)`.
* `W3` receives `DIGEST (msgId 12 (512τ + nQ), rlen, reg)` and sends `ROOT (τ + 1, reg)`.

### 2.2 Value rows (`vb`, part `j = 0`)

* Row `pos` receives `SPOST (τ, pos, b)` and sends `BYTES (msgId 12 (512τ), pos, b)`.
* The last row has `pos + 1 = L`, with `L = L0 + 256·L1 + 65536·L2`.
* The `L` bytes are emitted as fresh `VLEN` bytes in every case, so SHA range-checks them. The top byte is 0, so `L` is exact (`< 2^24 < P`).

### 2.3 Node parts (`qb`, `j = 1 … nQ`, bottom-up)

Part `j` emits `Q_j`. Row `qpos` sends `BYTES (msgId 12 (512τ + j), qpos, b)`, and the last row is the `MEM` field end with `qpos + 1 = qlen`.

**Field grammar.** The rows follow `nodeV3`'s grammar over `Q`. The states are `TAG HPL HPF KEY VLEN VH BM CH MEM`, with `fs`/`fe`/`idx`. The node type `qtl/qte/qtb1/qtb2`, `qhk` (hplen), `nokey` and `nochild` are part constants.
* Windows have a first-window flag `fw` and `lastw` (the window is followed by `MEM`).
* `tgt`: the target window of a rewritten branch (first window for slot 0, last for slot 15).
* `wfr`: the window is fresh.
* `wy`: the window is the split branch's new-leaf window.
* `wn`: the window holds a new leaf, with `DIGEST` id `j−1` and length 50.

**Byte provenance.** Each byte is one of:
* **copy**: `cp = 1`. Then `rd = 1` and `b = rb (+ bitmap add)`, where `rb` arrives on `UPB` at `spos` from the part's source record `sN = N_sd`.
* **fresh**: the byte is given by a field rule. The rules are the tag; hplen; the hex-prefix flag byte; the key byte `0x0f`; `L` bytes from the shift register `LR`; a digest register byte (`reg0`, loaded by `DIGEST` at the window start); split bitmap bytes `bmL`/`bmH`; or the `MEM` chain output.

**Reads.** `rd = cp +` the header, old-length and old-memory reads listed in §4. Every read position `spos` is pinned by a rule in §4.

### 2.4 Column map (186)

| range | content |
|---|---|
| 0–9 | `act wk vb qb sf wt1 wt2 wt3 pf pl` |
| 10–48 | segment constants: `tau`, `N0..N2`, `L0..L2`, the case one-hot (11), `dd` (3), `ts` (3), `ti` (3), `tX`, `xb` (4), `px`, `bmL`, `bmH`, `pres`, `vid`, `nQ`, `rlen` |
| 49–99 | part constants: `j`, kinds (11), `jo1..4`, `sd0..2`, `sN`, `plen`, `qtl qte qtb1 qtb2 qhk qodd nokey nochild qlen rootP jm clen`, the arithmetic selectors `Kc eL eS useA bN bL cO cS Cc neg`, `phk podd vcp xcp ba0 ba1 spY1 spY2`. On walk rows, 49–62 are `nN nI nib nN2 nI2 ek inv hv wbm enter lv0 lv1 lv2 trm`. |
| 100–128 | `qpos b rd rb spos u`, the 9 states, `fs fe idx fw lastw wfr tgt wy wn gD dI dL cp aft` |
| 129–160 | `reg[32]`, which holds a digest on fresh-window rows, `W0` and `W3`. On `MEM` rows it holds the chain temporaries: `tb[8] cb[3] cc[3] ci ci2 X1 Ein`. On `TAG`/`HPF` reads it holds nibble bits, and on `W1`/`W2` bitmap bits. |
| 161–167 | `LR[3]` (new length bytes), `SR[4]` (old value length bytes) |
| 168–175 | `gMs gMr rx mBv mCv mS mK mB` |
| 176–185 | pass-through (§1.1): segment constants `dep0 dep1 dep2`; part constants `kPT up rc pdep cN`; row columns `rcid` (the `cid` field of a read) and `rdc` (the row reads its target window's child id) |
| 186 | `rootRid` (M7e root binding): segment constant, the `rid` of `MIDROOT`; `qb·rootP·(sN − rootRid) = 0` |

## 3. Case analysis

### 3.1 Case selector (one-hot, segment constant) ↔ walk terminal ↔ `PTrie.upsert`

The key is `r = [0,15].drop c_D` at the terminal record `P_D`, `p = r.take I`, and `y = r[I]` when `I < |r|`.

| case | walk terminal | `PTrie.upsert` branch (spec lemma) |
|---|---|---|
| `LP` | `W3` `mS` (`VAL`), `P_D` leaf | `.leaf k s`, `k = key` → `newLeaf k v` |
| `BR` | `W3` `mS` (`VAL`), `P_D` branch | `.branch (some s) cs m, []` → value replaced, `m + valueMem L − valueMem slen` |
| `BV` | `W3` `mB` (`hasVal = 0`) | `upsert_brVal` |
| `BI` | `W1`/`W2` `mB` (bit `y` = 0) | `upsert_brSlot` (`Kids.upsert .none`) |
| `LSa` | `W1`/`W2` `mK`, `LEND` edge (leaf key ended: `k = p`) | `splitLeaf`, case `[], y::ys` |
| `LSb` | `W3` `mK`, `KEY` edge, `P_D` leaf (new key ended) | `splitLeaf`, case `x::xs, []` |
| `LSc` | `W1`/`W2` `mK`, `KEY` edge, leaf (`x ≠ y`) | `splitLeaf`, case `x::xs, y::ys` |
| `ESl0` / `ESl1` | `W3` `mK`, `KEY`, `P_D` extension; `xs ≠ []` / `xs = []` | `splitExt`, `key.drop |p| = []`; `sub` = shortened extension / `c` |
| `ESn0` / `ESn1` | `W1`/`W2` `mK`, `KEY`, extension (`x ≠ y`); `xs ≠ []` / `= []` | `splitExt`, `y::ys` |
| descend (every case, levels `d < D`) | `W1`/`W2` steps | `upsert_branch_down` / `upsert_ext_down` |

`trmE·(mS − cLP − cBR)`, `trmE·(mB − cBI − cBV)`, `trmE·(mK − Σ splits)`, the `ek` checks and the `t*`-class checks (`sf·ts3·(…)`, `sf·(ts1+ts2)·(…)`) tie the walk to the selector. The remaining distinctions are made from source-record bytes:
* leaf vs extension: the hex-prefix flag byte `B_0` at position 5 has high nibble `2·isLeaf + odd`;
* `LP` vs `BR`: the copied tag;
* `xs = []` vs not: `2(phk−1) + podd = I + 1` for `xcp`, and `|xs| ≥ 1` for `MVE`.

### 3.2 Part kinds and byte provenance

`P` is the part's source record, `m` its `memory_usage`, `hk` its hplen and `len` its length. `q` is the `Q` position.

| kind | source | `Q_j` = (field: provenance) | reads beyond copies |
|---|---|---|---|
| `RDB` (branch descend, level `d < D`) | `N_d` | everything = `P[q]`, except: the target window (slot 0 = first window if `d = 0`, slot 15 = last window if `d = 1`) = `DIGEST(Q_{j−1}, clen)`; `MEM` fresh | `MEM` (`P[len−8+i]`) |
| `RDE` (extension descend) | `N_d` | `TAG … KEY` = `P[q]`; `CH` = `DIGEST(Q_{j−1}, clen)`; `MEM` fresh | `MEM` |
| `RLP` (present leaf) | `N_D` | `TAG … KEY` = `P[q]`; `VLEN` = `u32 L`; `VH` = `DIGEST(VUPS, L)`; `MEM` fresh | `MEM` |
| `RBR` (branch value replace) | `N_D` | `TAG`, `BM`, `CH` = `P[q]`; `VLEN` = `u32 L`; `VH` = `H(v)`; `MEM` fresh | old `VLEN` `P[1..4]` (`slen`), `MEM` |
| `RBV` (branch value set) | `N_D` | `TAG` = 2; `VLEN VH` = `u32 L ‖ H(v)` (inserted); `BM`, `CH` = `P[q−36]`; `MEM` fresh | `P[0] = 1`, `MEM` |
| `RBI` (branch slot insert) | `N_D` | `TAG [VLEN VH]` = `P[q]`; `BM` = `P[q]` + 1 (byte 0, `y = 0`) / + 128 (byte 1, `y = 15`); windows `P[q]` before the inserted window and `P[q−32]` after; inserted window (first if `y = 0`, last if `y = 15`) = `DIGEST(Q_{j−1} = NLF, 50)`; `MEM` fresh | `MEM` |
| `MVL` (moved leaf `xs = k.drop (I+1)`) | `N_D` (leaf `k`) | `TAG` = 0; `HPL` = `u32 hk'`; `HPF` = `0x20 + odd'·(0x10 + lo P[5+e])`; `KEY ‖ VLEN ‖ VH` = `P[q+e]`, i.e. `P[6+e … len−8)`; `MEM` fresh | `P[5]` (`B_0`: leaf, odd), `P[1]` (`hk`), `P[5+e]` |
| `MVE` (shortened extension, `xs ≠ []`) | `N_D` (extension `k`) | as `MVL` with flag `0x00 + odd'·(0x10 + lo)`; `KEY ‖ CH` = `P[q+e]` | the same as `MVL`, plus `MEM` |
| `NLF` (new leaf `ys`) | — | `[0] ‖ u32 1 ‖ [0x3f if y = 0 (ys = [15]) else 0x20 (ys = [])] ‖ u32 L ‖ H(v) ‖ u64 (102 + L)` (50 bytes) | — |
| `WEX` (wrapping extension `p`, `I ≥ 1`) | `N_D` | `[3] ‖ u32 hk' ‖ hp(p)`, with `p = [0]` → `0x10`, `[15]` → `0x1f`, `[0,15]` → `0x00 0x0f`; `CH` = `DIGEST(Q_{j−1} = SPB, clen)`; `MEM` fresh | `MEM` (old usage of `P_D`, forwarded) |
| `PT` (pass-through, §1.1) | the `eext` at depth `pdep` | `TAG HPL HPF` = `P[q]` (pinned to `3 ‖ u32 1 ‖ 0x00`); `CH` = `DIGEST(Q_{j−1}, clen)`; `MEM` fresh | the target window's first byte (`cid`), `MEM` |
| `SPB` (split branch) | `N_D` | `TAG` = 2 (value) / 1; value slot: `LSa` = `P[len−44 … len−8)` (`s`'s ValueRef), `LSb`/`ESl` = `u32 L ‖ H(v)`; `BM` = `2^x` (unless `LSa`) + `2^y` (`LSa`, `LSc`, `ESn`); windows in slot order (`y = 0` first, else `x` first): `x`-slot = `DIGEST(Q_1 = MVL/MVE, clen)` or, for `ESl1`/`ESn1`, `P[len−40 … len−8)` (the old child hash `c`); `y`-slot = `DIGEST(Q_{j−1} = NLF, 50)`; `MEM` fresh | `MEM`; for `ESx1` also `P[5]` (extension, odd), `P[1]` (`hk`) |

Notes on the moved key (`MVL`/`MVE`):
* The hex prefix right-aligns the key nibbles, so `hp(k.drop t)` is `hp(k)`'s last `hk' − 1` bytes with a new flag byte. No nibble shift is needed.
* `hk' = 1 + ⌊|xs|/2⌋` and `e = hk − hk'`. The flag byte takes the low nibble of `P[5+e]` when `|xs|` is odd.
* The constraint is `2(qhk−1) + qodd = 2(phk−1) + podd − I − 1`.

### 3.3 Part plan (bottom-up, `j = 1 …`) and `nQ ≤ 403`

| case | terminal parts (`j ≤ nT`) | then (upper parts) |
|---|---|---|
| `LP` / `BR` / `BV` | `RLP` / `RBR` / `RBV` | one per depth `dep_D − 1 … 0` |
| `BI` | `NLF, RBI` | the same |
| `LSa` | `NLF, SPB`, `[WEX if I ≥ 1]` | the same |
| `LSb` | `MVL, SPB`, `[WEX]` | the same |
| `LSc` | `MVL, NLF, SPB`, `[WEX]` | the same |
| `ESl0` / `ESl1` | `MVE, SPB` / `SPB`, `[WEX]` | the same |
| `ESn0` / `ESn1` | `MVE, NLF, SPB` / `NLF, SPB`, `[WEX]` | the same |

**Upper parts.** The upper part at depth `δ` is `RD` (`RDB` or `RDE`, by the copied tag) if `δ = dep_d` for a walked record `N_d`, `d < D`, and reads level `d`. Otherwise it is `PT` and reads the `eext` at depth `δ` (§1.1). All terminal parts and `WEX` read level `D`.

**Bound.** Each level `d < D` consumes ≥ 1 nibble, and a split consumes `I` more, so `D + I ≤ 2` and `nT = n_case + [I ≥ 1 ∧ split] ≤ 4` (`LSc`/`ESn0` with `I = 1`: 3 + 1). There are `dep_D ≤ 399` upper parts, so `nQ = nT + dep_D ≤ 403`.

**Enforcement.**
* Positions: `jo i` marks `j = i` for `i ≤ 4`. It is shifted across part boundaries (`jo1` on the first node part), so all `jo` are 0 for `j ≥ 5`.
* Terminal vs upper: `up = 1 − Σ_i jo_i·isT_i(case, I)`, where `isT_i` says that the plan has a terminal part at `i`; and `up = kRDB + kRDE + kPT`.
* Kinds: `Σ_k code_k·kind_k = Σ_i jo_i·plan_i(case, I)`, with code 0 for `RD` and `PT`.
* Depth: `pdep = dep_D − up·(j − nT)`; every non-`PT` part has `pdep = dep_sd`; the root part has `pdep = 0` and `j = nQ = nT + dep_D`.
* Descends: `rc = D` on terminal parts, `rc' = rc − kRD` across boundaries, `sd = rc − 1` on an `RD`, and `rc = kRD` on the root part.
* Chain: `cN' = sN` across boundaries; an upper part's target-window `cid` is `cN`.

**Child links.**
* A part's `DIGEST` child is `j−1`, or `jm = 1` for the moved node under `SPB`.
* `MEMD` runs from every part except the root and `NLF` to its parent:
  * `RD`, `PT` and `WEX` receive from `j−1`;
  * `SPB` receives from `j = 1` in `LSb`, `LSc`, `ESl0` and `ESn0`;
  * the remaining parts fold the new leaf's usage `102 + L` into a constant.

## 4. Read positions (`spos`, every `rd` row)

| rows | `spos` |
|---|---|
| `MEM`, every reading part | `plen − 8 + idx` (the anchor: pins a branch's window count) |
| `RDB RDE RLP RBR PT` | `qpos` (incl. the child-id read `rdc` on the target window's first byte of `RDB RDE PT`) |
| `RBV` / `RBI` | `qpos − 36·aft` / `qpos − 32·aft` (`aft`: after the inserted value slot / window) |
| `MVL MVE` | `TAG`: 5; `HPL` row 0: 1; `HPF … CH`: `qpos + phk − qhk` |
| `SPB` | `TAG`: 5; `BM` row 0: 1; `VLEN`/`VH`: `qpos + plen − 45`; `CH`: `plen − 40 + idx` |

Which rows read is a function of kind, field and window flags: `rd = cp + extra` (`cBytes`). A prover cannot read at other positions, and the `UPB` message pins `(record, pos, byte, len, depth)`.

## 5. `memory_usage` arithmetic

Every `Q_j` has `R = E + max(0, A + B − C)`, matching the spec's `Nat` arithmetic:

| kind / case | `E` | `A` | `B` | `C` |
|---|---|---|---|---|
| `RDB`, `RDE`, `PT` | 0 | `m` | `N_{child}` (`MEMD.new`, exact) | `old_{child}` (`MEMD.old` = child source's `m`) |
| `RLP` | `100 + 2hk + L` | | | |
| `RBR` | 0 | `m` | `L` | `slen` |
| `RBV` / `RBI` | `50 + L` / `102 + L` | `m` | | |
| `MVL` | `100 + 2hk' + slen` | | | |
| `MVE` | `50 + 2hk'` | `m` | | `50 + 2hk` |
| `NLF` | `102 + L` | | | |
| `WEX` | `50 + 2hk'` | | `N_SPB` | |
| `SPB` `LSa` | `202 + slen + L` | | | |
| `SPB` `LSb` / `ESl0` | `100 + L` | | `N_{Q_1}` | |
| `SPB` `LSc` / `ESn0` | `152 + L` | | `N_{Q_1}` | |
| `SPB` `ESl1` / `ESn1` | `100 + L` / `152 + L` | `m` | | `50 + 2hk` |

Each row matches the spec:
* `leafMem k l = 100 + 2|hp| + l`, `extOwnMem k = 50 + 2|hp|` and `valueMem l = l + 50`.
* `BR`: `(m + (L+50)) − (slen+50) = max(0, m + L − slen)`.
* `ES`: `cm = m − extOwnMem k` is truncated **inside**, and `extOwnMem xs` / `50 + valueMem` / `leafMem ys` are added outside.

**Rows.** The eight `MEM` rows `i = 0 … 7` compute, little-endian:
* **Inputs.** `X1_i = A_i + B_i − C_i`:
  * `A_i`: the `UPB` byte.
  * `B_i`: the `MEMD` new limb, or the `LR` limb of `L`. `B_7 = byte + 256·H_child`.
  * `C_i`: the `MEMD` old byte, the `SR` limb of `slen`, or the constant `Cc` on row 0.
* **Outside term.** `Ein_i = [i=0]·Kc + eL·L_i + eS·slen_i`.
* **Chain 1 (sign).** `σ·X1_i + ci_i = t_i + 256·co_i`, with `σ = 1 − 2·neg`, `t_i` 8 bits, and `co_i = cb − 3 ∈ [−3, 4]` on rows 0–6. On row 7, `co_7 = cb ∈ [0, 7]` is the high limb `h`.
  * This proves `T = σ(A + B − C) = Σ t_i 256^i + 2^64·h ≥ 0`.
  * With `neg = 0`, `T = A + B − C ≥ 0`. With `neg = 1`, `A + B ≤ C`, so the truncated value is 0. When `A + B = C`, both choices give the same result.
* **Chain 2 (output).** `Ein_i + (1−neg)·t_i + ci2_i = b_i + 256·co2_i`, with `co2 ∈ [0, 7]` (3 bits). The emitted `b_i` is `u64 R`, and SHA range-checks the emitted bytes.
* **Exact high limb.** `H = (1−neg)·h + co2_7`. `MEMD` sends `rx_7 = b_7 + 256·H`, so parents use the exact `Nat`, not `R mod 2^64`. This matches the spec, where `c'.memD` is exact.

**Bounds.**
* `N_D < 2^64 + 2^34`, and each descend adds less than `2^64`, so `H ≤ 3` and `h ≤ 4` (3 bits each suffice).
* Carries satisfy `|co| ≤ 3` and `co2 ≤ 5`.
* `Kc ≤ 610`, `L < 2^24` and `slen < 2^32` (4 limbs; an unrevealed `ValueRef` length is any `u32`).
* Every intermediate is < 2^15, far below `P`.

**Length registers.**
* `LR` holds `L` at `VLEN`/`MEM` field starts and shifts by one byte per row.
* `SR` rotates over the 4 `VLEN` rows, capturing `rb = SR0` on reading `VLEN` rows. It is constant until `MEM`, then shifts.

## 6. Soundness sketch (argued; M7c–M7e)

1. **Walk.** Rows `W0 … W3` form a `walkV3` walk of `[0, 15]` from the head of `τ`.
   * A `WalkR` with these four steps satisfies the hypotheses of `walk3_find`. The key comes from fixed symbols instead of `KEYNIB`.
   * So `present`/`vid` are `find (T_mid) [0,15]`, and an absent terminal is an `AbsentWitness` (`absent_find`).
   * The levels give the records `N_0 … N_D` and the positions on the path. `N_0` is `rres` of head `τ`, which is unique per `τ` by `root_chain`.
2. **The path, including skipped records.** The upper parts form a chain by `cid`: the part at depth `δ` reads source `S_δ` with `depth(S_δ) = δ`, and its target window's `cid` is `S_{δ+1}` (`S_{dep_D} = N_D`). The descends sit at `S_{dep_d} = N_d`.
   * Each `N_d`'s target window is revealed (`rv = 1`): the walk's `DOWN`/`KEY` edge out of it exists only then. So its `cid` is the real child (`PARENT`).
   * For a `PT` source `E`: if `E`'s child were unrevealed, `res E = E`, and the walk's edge out of the record above would end at `E`. That is impossible, because `E` provides no edge, so the walk could not continue (a walked record is a lookup position and is never an `eext`). So `rv(E) = 1`, and `cid` is the real child. (`cid` is free on unrevealed windows, so this step is needed.)
   * By induction, `S_δ` is the unique ancestor of `N_D` at depth `δ` (each record receives `PARENT` once), so `S_0` is the root record `rid` of `τ` (depth 0, `root_chain`). Each `PT` source is an `eext` by its pinned bytes, and the `res` rules give `N_{d+1} = res(child slot of N_d)`.
3. **Copy restriction.** Every `UPB` id is `NPOST(sN)` with `sN` one of the `S_δ`, at `depth = δ`. So every read is of a record on the `[0,15]` path of `τ`'s lockstep post-trie.
4. **Source bytes.** `UPB` balance plus `nodeV3`'s view give `rb = ser(P_sd)[spos]` and `plen = |ser P_sd|`.
   * The `nodeV3` view is `NodeV3.ser true`. The delta needs the `UPB` traffic to be added to `nodeTraffic3`.
   * `B_0`'s high nibble gives leaf vs extension and the parity; `P[1]` gives `hk`. These positions are valid because `P_D` provides `KEY`/`LEND` edges and is therefore a leaf or an extension.
5. **Each `Q_j` is a spec node.** From the part's field grammar and §3.2, `Q_j = ser(q_j)` byte for byte.
   * `q_j` is the node of the spec construction with those fields: copied ranges are fields of `P` by `NodeV3.ser`, and fresh fields are the formulas.
   * Windows are `DIGEST`s. The ids are `msgId 12 (512τ + j')`, and the lengths are bound by `MEMD.qlen` (`clen`), the constant 50 (`NLF` is always 50 bytes) or `L`. So SHA's prefix behaviour cannot substitute a shorter message.
   * `MEM = u64 R` with `R` from §5, which is exactly the spec's `Nat`.
6. **Root.** The plan composes the spec cases (§3.1).
   * In the descend parts, `q_root = upsert (prune_{[0,15]} P_0) [0,15] v`.
   * Off-path windows are copied hash bytes, which are equal to `hashOf` of the pruned `.hash` child.
   * By `upsert_hashOf_congr`, `post = hashOf (upsert T_mid [0,15] v)`, and `ROOT (τ+1, post)` is sent.
7. **Uniqueness of ids.** Per `τ` there is one segment (`root_chain`), and `j ≤ nQ ≤ 403 < 512` within it (`pdep = dep_D − (j − nT) ≥ 0` and `dep_D ≤ 399`). So `(τ, j)` ↦ `512τ + j` is injective, and each id's `BYTES` are sent exactly once per position.

**Owed to the assembly lane (id-range lemma).** Every `BYTES`/`DIGEST` id that `upsV3` uses is `msgId 12 (512τ + j)` with `j < 512` and `τ ≤ K`. So the `upsV3` ids are exactly kind 12 with `idx < 512(K+1)`. No other table may send kind 12.

**Completeness conditions** (render hypotheses):
* empty-key extensions on the path are covered (pass-through, §1.1); depth ≤ 399 is `nodeV3`'s;
* if `0x0f` is present, its value is revealed (the read needs it anyway);
* `1 ≤ L < 2^24`;
* the trace fits the height: `4 + L + Σ|Q_j|` rows per instance, `|Q_j| ≤ 591` (46 for `PT`), `maxLog 22`. With `≤ 33` instances and `Σ L ≤ 3·10^6` (A7) this is `≤ 3·10^6 + 33·(4 + 6·591 + 397·46) < 2^22`.

## 7. `nodeV3` delta (applied in M7c step 2)

`Tables/Node.lean` now carries the delta (`NodeUpb.lean` keeps `tableU := table` for the budget):

* **column** `mU := 185` (width 186): the **per-row** use count of the row's post byte. It cannot be node-constant: `upsV3` reads different bytes of a record different numbers of times (for example, an `RDB` reads only the first byte of its target window), and a chained provider must close each byte's chain with that byte's exact count.
* **interactions** (chained provider, as `EDGE`), on every active row:
  * `send UPB (c act) [mid K_NPOST (c nid), c pos, c pb, c len, c depth, c cid, 0]`
  * `recv UPB (c act) [mid K_NPOST (c nid), c pos, c pb, c len, c depth, c cid, c mU]`
* **constraints:** none. The budget is kernel-checked in `BudgetCheck.lean`: `nodeV3` has 186 columns, 20 interactions and `W_eq` 370 / 298. The five-table total is 855 / 783 (was 838 / 782).
* **view** (`Extract/NodeView.lean`, `node3_view`):
  * `NodeS3` gains `ucid` and `mU`, per-byte lists of the `cid` and `mU` cells.
  * `nodeSends3` / `nodeRecvs3 B_UPB` contain `upbOf n s (· ↦ 0)` / `upbOf n s (p ↦ mU[p])`, where `upbOf n s u = [NPOST(n), p, ser_post[p], |ser|, depth, ucid[p], u p]` for each byte `p`.
  * `NodeWf3` gains `upbLen` and `upbSmall` (lengths, canonical values) and `kidCid`: the first byte of every revealed child's window carries the child id (`NodeV3.kidCidOk`). The offset is `5 + |hp|` in an extension and `(1 | 37) + 2 + 32·#(present kids before j)` in a branch.
* **render** (`node_render_local`, `node_render_traffic`):
  * The generator writes `mU[p]` into column 185.
  * `NodeOk` gains `ucid`: `ucid[p] = cidAt vs n p`, the generator's `cid` column (the window's child on a revealed window, else 0). A builder sets `ucid` to that and `mU` to the `upsV3` read counts.

## 8. Plan for view, render and link

* **M7c, view (`UpsViewStmt`).** In the segment framework (`Near/Extract/Segments`), the view is one `UpsSeg` per `τ`:
  * `walk : List WStep3` (4), the case, `D`, `I`, `x`, `L`, `v`;
  * `parts : List UpsPart`, each with kind (incl. `PT`), `j`, `sd`, `sN`, `pdep`, `cN`, `rc`, `plen`, its field list with bytes, its read list `(spos, rb, cid)`, and its `MEM` limbs.

  `UpsWf` collects the row facts. The field grammar can be ported from `Extract/Node/Segs.lean`, since the states and the length/succession constraints are `nodeV3`'s on `q*` columns. The other facts are:
  * the provenance table of §3.2 as per-field equalities;
  * the read positions of §4;
  * **the chain lemma**: the 8-row carry chains give the exact `R = E + (A + B − C)` truncated, with `H` exact;
  * the plan (§3.3), including the upper chain: depths, the descend counter and the child ids.
* **M7d, render.** The generator is `test/upsv3_model.py`'s `gen` (§9) transcribed to Lean.
  * Its inputs are the lockstep records, the walk, `v` and `τ`.
  * The local constraints are proved per part kind. Traffic matches by construction: the `UPB` reads are counted into `nodeV3`'s per-byte `mU`, and `ucid = cidAt` (`NodeOk.ucid`).
* **M7e, link.** Per §6 and per case:
  * from the view, the `nodeV3` records of `τ` and the walk, show `q_root = upsert (prune P) [0,15] v`;
  * the per-case lemmas are `upsert_brSlot`, `upsert_brVal`, `upsert_leaf_ne` with `splitLeaf`'s three cases, `upsert_ext_np` with `splitExt`'s, and `upsert_branch_down` / `upsert_ext_down` for the `RD` levels and (key `[]`) the `PT` levels;
  * then `upsert_hashOf_congr`, plus `set_upsert_comm` / `trieOpsStmt` for the order relative to the lockstep sets.

### 8.1 M7c layer 2 (layout): status (lane/v3-trie-h)

Done (kernel-checked, axioms ⊆ {propext, Classical.choice, Quot.sound}; `Extract/Ups/`):

| module | content |
|---|---|
| `LayoutRows`, `Layout` | row lemmas `layoutRow`/`pconst`/`sconst`; `walkRows` (W0…W3), `valuePart` (rows `4 … 3+L`), `nodeParts` (consecutive parts to the segment end, `j = k+1`, `qpos`, `pf`/`pl`, part constants) |
| `FieldRows`, `LayoutFields` | `fieldRow` (one-hot states = `qb`, `idx` counter, field successions), `fieldEnd` (lengths), `fieldSucc`, `partHead`, `extLastw`; `segConstAll`; `partFields` (fields of a part) |
| `LayoutShape` | `partShape`: the fields' (state, length) list is `shapeU` of the part's type (leaf / ext / branch without / with value, `w` windows, `w = 0` iff `nochild`) |
| `MsgRows` | `msgsW`, `msgsV`, `msgsQ`: every row's messages by kind (ids `msgId 12 (512τ + j)` and `u + 1` mod `P`) |
| `ByteRows` | 49 generated row lemmas (`test/gen_ups_bytes.py`): copy flags per field, `b = rb` (+ bitmap add), fresh grammar bytes, header reads, read positions, `DIGEST` ids/lengths |
| `LayoutMain` | `UpsLayout s L ps fls ws` and `ups_layout : UpsWf v → ∀ s ∈ v, ∃ L ps fls ws, UpsLayout s L ps fls ws` |
| `Nev` | `nev C D e`: a pure constraint evaluated in `ℕ` modulo `P` (`uev_toNat`); `factN` (a vanishing constraint as an `omega`-ready fact); `nev_congr` (only the read columns matter) |
| `PlanDefs`, `PlanRows`, `Plan` | **part plan**: `UCase`/`UKind` (index order of the one-hot columns), `termPlan cs I` (terminal kinds bottom-up, `WEX` when a split has `I ≥ 1`), `nTof`; `planDec` (kind code / `up` / `termE` checked over all index combinations by `decide +kernel` on `nev`); row facts `segIx`, `partIx`, `planFact`, `partHeadPlan`, `joValueEnd`, `partEnd`, `rootEnd`, `rootPart`, `segNQ`; `UpsPlan s ps ci ti di si kd sdx` and `ups_plan : UpsWf v → s ∈ v → UpsLayout s L ps fls ws → ∃ ci ti di si kd sdx, UpsPlan …`: the number of parts is `nT + dep_D`; part `k < nT` has kind `termPlan[k]`, `up = 0`, `rc = D`, reads level `D` at depth `dep_D`; part `k ≥ nT` is `RDB`/`RDE`/`PT`, `up = 1`, `pdep = dep_D − (k+1−nT)`; `rc k` = number of descends from `k` up (`rdCount`), exactly `D` in all; a descend reads level `rc − 1`; non-`PT` parts read `sN = N_sd` at depth `dep_sd`; `cN (k+1) = sN k`; `rootP` exactly on the last part |
| `IxRow`, `WinRows`, `Windows` | **window roles**: `ixRow`/`IxOf` (a row's selectors as indices) and `ixVals` (derived selectors `s15E`, `twoE`, `spY1/2`, `xcp`, `vcp`, `ba0/1` = semantic functions `s15V`, `twoV`, … by `decide +kernel`); `partSelAll` (the derived part constants on every row of a part); `winStep`, `winRole`, `rdcOff`, `aftRow` (row facts); `WinsOK` and `ups_windows : … → ∀ k, WinsOK s ps[k].1 fls[k] ci si (kd k) (sdx k)`: every window field is 32 bytes, `fw` = the previous field is not a window, `lastw` = `MEM` follows, the window constants are those of its first row, where `WinRoleP` holds (`tgt` = last window iff slot 15 else first; `wfr` = `tgt` for `RDB`/`RBI`, 1 for `RDE`/`WEX`/`PT`, 0 for `RBR`/`RBV`/`MVE`; split branch: `wy` = `spY1`/`spY2` by `fw`, `wfr = 1 − (1−wy)·xcp`, window count `1 + two`; `wn = [RBI]·tgt + [SPB]·wy`; `rdc = fs·tgt·up` and `rdc → rcid = cN`); `aft` per field for `RBV`/`RBI` |
| `MemRows`, `MemChain`, `Mem` | **`memory_usage` chains** (§5): `memRow` (row facts `MemRowF`: `X1 ≡ A + B − C`, `Ein`, carry-ins, both chain equations, `rx`); `telescope` (the carry identity over `ℤ`); `memChain` / `ups_mem : … → ∀ k, ∃ r0, …`: on the part's `MEM` field (rows `r0 … r0+7`, `r0 + 8` = part end), if the limb inputs `inA = useA·rb`, `inB = bN·mBv + bL·LR0`, `inC = cO·mCv + cS·SR0 + fs·Cc`, `inE = fs·Kc + eL·LR0 + eS·SR0` are `< 2^12` and the emitted bytes are `< 256` (SHA, hypothesis), then `Σ 256^i rx_i = E + (A + B − C)` (ℕ, truncated; exact, including the high limb), `rx_i = b_i` for `i < 7`, and `Σ 256^i b_i = Σ 256^i rx_i mod 2^64` |
| `WalkRows`, `Walk` | **the walk** `W0 … W3`: `upsWalk s : WalkR` (`stepOf`: mode `0/1/2/3` from `mS/mK/mB`, symbols `START 0 15 END`, edge message, `BMAP` message, `u` as both use counts); `ups_walk : … → (s.row 3 mB = 1 → s.row 3 wbm < 2^16) → WalkWf3 [upsWalk s] ∧ symbols = [START, 0, 15, END] ∧ tau` (so `walk3_find` applies with key `[0, 15]`; the 16-bit bound of `W3`'s `BMAP` bitmap comes from `BMAP` balance in the link); `ups_walkTerm`: rows before `t* = si+1` are steps, at `t*` the mode is the case's (`mS = [LP,BR]`, `mB = [BV,BI]`, `mK` = splits; a step terminal is `W3`), `nI = I`, level `= D`, `LSa` ↔ `LEND` edge, other key splits `KEY` with `nib = tX`, `S0F` contents; `ups_walkLev`: `W1` at level 0, `enter` semantics and level advance, lookup record `nN = N_lv` |
| `WalkTraffic` | **walk traffic**: `ups_walkTrafficFp` (no hypothesis): a segment's `EDGE`/`BMAP` sends and receives, after `Msg.toFp`, are `walkSends3`/`walkRecvs3 [upsWalk s]` (the form `Link/Walk3Prov` consumes); `ups_walkTraffic`: the same over `ℕ` given `u + 1 < P` on `W0 … W3` (`u` is canonical; the bound comes from the chained-provider count in the link: one record's use counts are `0 … n−1`, `n` ≤ the consumer rows `< P`); value and node rows send nothing on these buses (`quietWalkBus`) |
| `FieldBytes` | **field byte lists** (start): `rowsB s r0 n`; `partBytes_fields` (a part's bytes = the concatenation of its fields' bytes); `freshWin` (a fresh window field's 32 bytes = the register of its first row, which receives `DIGEST (dI, dL, reg)`); `freshVlen` (a fresh `VLEN` field = `L0 L1 L2 0`); row facts `winRow`, `vlenRow`, `gramRow` (tag byte, `u32 qhk`) |
| `PartBytes`, `NlfBytes` | **part bytes by kind** (start): `FieldsAt`/`fieldsB`, `partFieldsAt` (a part's bytes are its fields' bytes, laid out as `shapeU`); `toNats_u32`, `u64_limbs` (eight limbs `< 256` of value `X mod 2^64` are `u64 X`); `tagField`, `hplField` (`u32 qhk`), `gDrow` (a fresh window's first row looks up `DIGEST`), `dI_nat`; **`ups_nlfBytes`**: an `NLF` part's 50 bytes are `nodeEnc (qNLF si val)`, given `|val| = L` (`SPLEN`), the `DIGEST` lookup `(msgId 12 (512τ), L)` returns `sha256 val`, and the part's bytes are `< 256` (`SHA`) |
| `KindHeads` (generated, `test/gen_ups_heads.py`), `PartK`, `Shapes`, `RlpBytes` | `head_K` (11 kinds, all but `SPB`): the part constants a kind fixes on its first row (`xcp`, `vcp`, node type, `memory_usage` formula `useA bN bL cO cS Cc eL eS Kc`); `PartK` (row facts of a part, `partK`), `rdCopy` (a copied byte is read), `bCopyN`, `copyRun` (copied rows with `spos = δ + d` emit `Pb[δ …]`), `vlenFresh`, `vhFresh`, `memSR`, `memRegs` (`fs`, `L` and old-length registers on `MEM` rows), `memIn` (the `MEM` inputs `E A B C` as numbers), `memBytesK` (the `MEM` bytes are `u64 (E + (A + B − C))`); `leafShape`/`extShape` (field offsets of leaf/extension parts, `HPF [KEY]` = `qhk` rows); `dirRow` (direct copies read at `spos = qpos`); **`ups_rlpBytes`**: an `RLP` part's bytes are `nodeEnc (qRLP k val)`, given the `UPB` reads return the source record's post bytes `Pb` and the source is `nodeEnc (.leaf k s m)` (`< 2^32` bytes) |
| `RdeBytes` | `chUp` (the window of `RDE`/`WEX`/`PT` is fresh, `wn = 0`), `rdMem` (`MEM` rows read the old memory), `jmRow` (`jm = j − 1`), `limbs_u64`; **`ups_rdeBytes`** / **`ups_ptBytes`**: an `RDE` / `PT` part's bytes are `nodeEnc (qRDE k m c' cm)` / `nodeEnc (qPT m c' cm)`, given the source `nodeEnc (.ext k c m)` (`|c.hashOf| = 32`, `m < 2^64`) through the `UPB` reads, the `DIGEST` of the part below at `clen` is `c'.hashOf`, and the `MEMD` limbs on the `MEM` rows (`< 2^12`) have values `c'.memD` / `cm` |
| `WexBytes` | `wexQhk`, `wexHpf`, `wexKeyB` (fresh `WEX` header bytes); **`ups_wexBytes`**: a `WEX` part's bytes are `nodeEnc (qWEX (wexKey si ti) b)` (`wexKey si ti = [0,15].drop (si − ti) |>.take ti`: `[0]`, `[15]` or `[0,15]`), given `1 ≤ ti ≤ si` (walk), the `DIGEST` of the part below at `clen` is `b.hashOf` and the `MEMD` limbs on the `MEM` rows (`< 2^12`) have value `b.memD` |
| `Shapes` (branch), `RbvBytes` | `fieldsAt_rep`, `branchVShape` / `branchNShape` (field offsets of branch parts with / without a value, `w` windows); `UpbReads s Pb` (every `UPB` read returns its record's post byte at its position and the record's length); `bCopyB`, `copyRunB` (copied bitmap bytes without an inserted bit), `rdcUp0`, `chCopy` (`RBR RBV MVE` windows are copied), `sposRBV`, `upZero` (kinds 2–10 are terminal parts); **`ups_rbvBytes`**: an `RBV` part's bytes are `nodeEnc (qRBV cs m val)`, given `UpbReads` with the source `nodeEnc (.branch none cs m)` (`m < 2^64`; the number of child hashes is fixed by the `MEM` read position and the record length) and the value as for `NLF` |
| `RbrBytes` | `srRot` (the old-length register rotates on `VLEN` rows), `srConst` (constant on the other rows of a part), `rdVlenRBR`; **`ups_rbrBytes`**: an `RBR` part's bytes are `nodeEnc (qRBR s cs m val)`, given `UpbReads` with the source `nodeEnc (.branch (some s) cs m)` (36-byte slot, `s.len < 2^32`, `m < 2^64`) and the value as for `NLF`; the old length reaches the `MEM` field through `SR` |
| `KidsBytes`, `BranchK`, `RdbBytes` | spec side: `kidAt`, `kidsLen`, `setKid_first`/`setKid_last` (replacing an occupied first / last slot replaces the first / last child hash), `bitmap_setKid`, `setKid_first_ins`/`setKid_last_ins` (inserting into an empty first / last slot prepends / appends the hash and adds the bit); `winFlags` (`fw = [e = 0]`, `lastw = [e = w − 1]` on window `e`); `BrLay`/`brLay` (uniform branch layout: prefix `TAG [VLEN VH] BM` of `c0 ∈ {3, 39}` rows, windows, `MEM`); `brPre`, `brEnc`; **`ups_rdbBytes`**: an `RDB` part's bytes are `nodeEnc (qRDB bv cs m (slotOf sd) c' cm)` (`slotOf 1 = 15`, else `0`), given `UpbReads` with the source `nodeEnc (.branch bv cs m)` (36-byte slot if any, `m < 2^64`, 16 slots, slot `n` holds a child with a 32-byte hash), the part below's `DIGEST` at `clen` and the `MEMD` limbs; every byte but the target window (`tgt`: first / last window) and `MEM` is copied at its own position |
| `RbiBytes` | spec side: `kidsBitmap_succ`, `kidsBitmap_lt` (`< 2^kidsLen`), `kidsBitmap_even` (slot 0 empty), `kidsBitmap_lastFree` (last slot empty: `< 2^15`); `brTag`, `brPre_eq`, `bCopyIns` (a copied bitmap byte with the insertion bit), `sposRBI`; **`ups_rbiBytes`**: an `RBI` part's bytes are `nodeEnc (qRBI bv cs m si val)`, given `si ≤ 1`, `UpbReads` with the source `nodeEnc (.branch bv cs m)` (`< 2^20` bytes, 36-byte slot if any, `m < 2^64`, 16 slots, slot `y` empty), the `DIGEST` of the part below at 50 is `(qNLF si val).hashOf`, `|val| = L` with `L`'s bytes `< 256`; the window count is `≥ 1` and the source's length are recovered from the `MEM` read (`spos + 32 aft = qpos`, `spos + 8 = plen + idx`) |
| `MoveKey`, `MvRows`, `MvlBytes` | spec side: `pack_drop2`, `pack_get`, `hp_eq`, `hp_len`, **`hp_drop`** (the hex prefix of `k.drop d` is `hp k` with `δ = n/2 − (n−d)/2` packed bytes dropped; its flag byte takes the low nibble of byte `δ` when `n − d` is odd); rows: `nibBits`, `mvTag` (`hi = 2·qtl + podd`), `mvHpf`, `mvPos` (`spos + qhk = qpos + phk`), `mvQhk` (`2·qhk + qodd + I + 1 = 2·phk + podd`), `rdMv`, `srChain` (the old length reaches `MEM` through `SR`); **`ups_mvlBytes`**: an `MVL` part's bytes are `nodeEnc (qMVL k s I)`, given `UpbReads` with the source `nodeEnc (.leaf k s m)` (`< 2^20` bytes, nibbles `< 16`, `I + 1 ≤ |k| < 400`, 36-byte slot, `s.len < 2^32`) |
| `MveBytes` | **`ups_mveBytes`**: an `MVE` part's bytes are `nodeEnc (qMVE k c m I)`, given `UpbReads` with the source `nodeEnc (.ext k c m)` (`< 2^20` bytes, nibbles `< 16`, `I + 1 ≤ |k| < 400`, 32-byte child hash, `m < 2^64`): as `MVL` for the tag, `hplen`, flag byte and key; the child window copied `δ = phk − qhk` bytes further on (`chCopy`, `mvPos`); `memory_usage = (50 + 2·qhk) + (m − (50 + 2·phk))` with `m` read from the source's last eight bytes (`pMEM`: `spos + 8 = plen + idx`) |
| `SpbSpec`, `SpbRows`, `SpbBytes` | spec side: **`qSPB ci src cx x si v`** (the split branch by case, `ci = 4 … 10` = `LSa LSb LSc ESl0 ESl1 ESn0 ESn1`: the branches of `splitLeaf`/`splitExt` before `wrapExt`), `kidsFrom0/1/2`, `kids1_bm`, `kids2_bm` (bitmap `2^x (+ 2^y)`, hashes in slot order); rows: `head_SPB` (part constants by case: branch type, `xcp = useA = [ESx1]`, `vcp = eS = [LSa]`, `bN = [LSb LSc ESl0 ESn0]` with `jm = 1`, `Cc = xcp·(50 + 2·phk)`, `Kc = 202/100/152`), `spbSeg` (`bmL`/`bmH` = the bytes of `spBm = [¬LSa]·2^x + [y-case]·2^y`, `x = tX < 16`; a split with a new leaf has `si ≤ 1`), `rdBMx`; **`ups_spbBytes`**: an `SPB` part's bytes are `nodeEnc (qSPB ci src cx (tX) si v)`, given `UpbReads` with the source `nodeEnc src` (`< 2^20` bytes; `LSa`: a leaf, 36-byte slot, `slen < 2^32`; `ESl1`/`ESn1`: an extension, 32-byte child hash, `m < 2^64`, `|k| < 400`), for `LSb LSc ESl0 ESn0` the `DIGEST` of part 1 at `clen` (`cx.hashOf`) and the `MEMD` limbs (`cx.memD`), with a new leaf the `DIGEST` of the part below at 50 (`(qNLF si v).hashOf`) and `x ≠ y` (two windows), the value digest, `|v| = L` (bytes `< 256`); windows: new leaf (`winY`), moved node (`winC`), old child copied from `P[len − 40 …]` (`winO`); the value slot fresh or (`LSa`) copied from `P[len − 44 …]` with `slen` through `SR`; `phk` read on the first bitmap row (`ESx1`). Also **`rbiSi`**: an `RBI` part implies `si ≤ 1` (its case is `BI` by the plan, and `sf·ts3·cBI = 0`), `termCase` |
| `UpsParts` | **the gather**: `qPart` (the `QNodes` constructor by kind, from the source node, the part below, part 0 and the child source's old usage), **`upsQ`** (the parts' nodes bottom-up: `upsQ k = qPart (kd k) (src k) (upsQ (k−1)) (upsQ 0) (src (k−1)).memD`), `SrcOk` (per kind: shape and well-formedness of the source node), `recvK`/`childK` (parts receiving `MEMD`, from the part below or part 0); **`UpsExt s ps ci ti si kd sdx Pb src v`** (the segment's external facts, stated once: `reads` (`UpbReads`), `srcEnc` (`Pb (sN of part k) = nodeEnc (src k)`), `srcOk`, `vlen`/`vbytes`/`digV` (the value), `dig` (the `DIGEST` of part `k'`, id `512τ + k' + 1`, at `|nodeEnc (upsQ k')|` is `(upsQ k').hashOf`), `clen`/`memB`/`memV` (what a receiving part gets on `MEMD`: the child node's length and exact usage, the child source's usage), `bytes` (`< 256`), `tiLe` (`I ≤ t* − 1`), `xy` (`x ≠ y` with two windows)); plan facts `termNLF`, `termWEX`, `termSPB`, `partPlan` (`decide`); `rbiBytes'` (`RBI` without `si ≤ 1`); **`ups_parts`**: `UpsExt … → ∀ k < |ps|, rowsB s ps[k] = (nodeEnc (upsQ … k)).map toNat` |
| `QNodes` | **target nodes** per part kind (spec side, as `PTrie.upsert` builds them): `qRLP`, `qRBR`, `qRBV`, `qRBI`, `qNLF` (`newLeaf ([0,15].drop (si+1)) v`), `qMVL`, `qMVE`, `qSPBleaf`/`qSPBext` (the branch of `splitLeaf`/`splitExt` before `wrapExt`), `qWEX`, `qRDB`, `qRDE`, `qPT`; `setKid`; `qNLF_enc` |
| `NlfRows` | `NLF` part constants (`nlfHead`: leaf, `hplen 1`, `R = 102 + L` formula), `memLR` (the `L` register on `MEM` rows), `nlfHpf` (flag byte `0x20 + 0x1f·ts1`) |

Done (layer 2): the byte statements `rowsB (part) = nodeEnc (node)` for all twelve kinds
(`NLF RLP RDE PT WEX RBV RBR RDB RBI MVL MVE SPB`; `RBI`'s `si ≤ 1` by `rbiSi`) and their gather **`ups_parts`**
over a segment, with the hypotheses collected in **`UpsExt`**.  **AIR fix** (§10.4): `SPB`'s node type is now
pinned (`pf·kSPB·(qtl + qte) = 0`); without it the cases `LSc ESn0 ESn1` were not provable.
**For M7e** (discharging `UpsExt`): `Pb n` = the post bytes of `nodeV3` record `n` and `src k` = its node
(`nodeV3` view, `NodeV3.ser`; `UPB` balance gives `reads`); `srcOk` from `NodeWf3` plus the case/walk link
(the source of each kind has the kind's shape: e.g. an `RDB` source is a branch with its target slot revealed,
`MVL`'s a leaf with `I + 1 ≤ |k|`); `dig` and `bytes` from SHA by induction on `k` (`ups_parts` for the parts
below gives their bytes, hence their digest at their length); `clen`/`memB`/`memV` from `MEMD` balance (the
child part sends `qlen`, its exact `rx` and its read old usage `rb`; the child's `qlen`/`rx` are pinned by
`ups_parts` for the child and `ups_mem`); `tiLe`, `xy` and `vlen` from the walk and `SPLEN`.
Method note: `omega` is incomplete with
the modulus `P ≈ 2^31` when several unknowns share a `% P` (it then reports spurious counterexamples or times out);
such facts go through `Fp` and `natv` (`wbmBits`, `sub_of_cast`), or through `decide +kernel` on index rows
(`planDec`, `ixVals`).  `omega` / `simp_all` can also time out in `whnf` when the context holds hypotheses with
large `if`/list terms (e.g. `winRole`'s); prove such side facts with explicit lemmas.
M7d (render) is not started.

### 8.2 M7e (link): status (lane/v3-trie-h)

Done (kernel-checked, axioms ⊆ {propext, Classical.choice, Quot.sound}; `Extract/Ups/`):

| module | content |
|---|---|
| `Shapes` + per-kind files | **exact `memory_usage`**: `memBytesK` also gives `limbs rx = E + (A + B − C)` (untruncated); every per-kind lemma (`RLP RDE PT WEX RBV RBR RDB RBI MVL MVE SPB`) now also concludes `limbs rx (MEM rows) = (node).memD` — what the part sends on `MEMD` |
| `UpsParts` | `UpsExt` split: **`UpsExt0`** (part-independent: `reads`, `srcEnc`, `srcOk`, value `vlen`/`vbytes`/`digV`, walk `tiLe`/`xy`) and **`UpsExtK k`** (`dig` for parts `< k`, `clen`/`memB`/`memV`, bytes of `k`); **`ups_part`**: part `k`'s bytes are `nodeEnc (upsQ k)` and (not `NLF`) its `rx` limbs are `(upsQ k).memD` |
| `UpsInd` | segment facts **`UpsShaSeg`** (a `DIGEST` lookup of part `k`'s id at its length returns `sha256` of its bytes, which are `< 256`), **`UpsMemdSeg`** (every `MEMD` receive of the segment is matched by a send of the segment: same `j, i, new, old, len`), `UpsLookSeg`; `memdMatch` (a receiving part's child is `childK`; its `mBv`/`mCv`/`clen` are the child's `rx`/`rb`/`qlen` on `MEM` row `i`), `memSrc` (`MEM`-row reads = the source's usage), `qlenPart` (`qlen` = part length), `memRowOf`, `memRows8`, `recvHead`, `rx_lt`; **`ups_partsI`**: strong induction on `k` discharges every `UpsExtK k` (`dig` from SHA + IH, `clen`/`memB`/`memV` from `memdMatch` + IH, bytes from SHA via the lookup) |
| `UpsLook`, look lemmas in `RdbBytes RbiBytes RdeBytes WexBytes SpbBytes` | **`ups_look`**: `UpsLookSeg` from `UpsExt0` + SHA + `MEMD` (downward from the root: `W3` looks the root up at `rlen = qlen`, `nQ = j`; the new leaf is looked up by `RBI` / split branch at 50 (`nlfLen`); every other part by the part receiving its `MEMD` at `clen` = its length); `parentOf` (`termPar`, `termLast` by `decide`); `rdbLook rbiLook extUpLook wexLook spbLookY spbLookC` (the per-kind proofs' prefixes up to the child-window digest); **`ups_partsS`**: the parts of a segment from `UpsExt0`, "sources are nodes with usage `< 2^64`", `UpsShaSeg`, `UpsMemdSeg` |
| `UpsBus` | **global SHA / `MEMD`**: **`sha_seg`** (`ShaFacts`, the `BYTES` balance `shaR B_BYTES = cnt (upsV3 sends ++ others)` with no other id of kind 12, every `upsV3` `DIGEST` receive provided, `UpsTauDistinct`, `UpsIdBound` (`τ < 2^17`, `< 512` parts) ⇒ `UpsShaSeg` for every segment, via `sha_core` with the part's bytes); **`memd_seg`** (the `MEMD` balance, `upsV3` only, + `UpsTauDistinct` ⇒ `UpsMemdSeg`); **`ups_partsG`**: every part of every segment emits `nodeEnc (upsQ k)` with exact `MEMD` limbs, from the per-segment `UpsExt0` and "sources are nodes with usage `< 2^64`" and the global facts above |
| `SpbSplit` | **step 2**: `commonPrefix_eq`; `split_LSa/LSb/LSc` (`splitLeaf k s key' v = wrapExt (k.take I) (qSPB ci (.leaf k s m) (qMVL k s I) k[I] si v)`), `split_ESl0/ESl1/ESn0/ESn1` (same for `splitExt`, moved node `qMVE k c m I` or the old child), given `k.take I = key'.take I` and `key'.drop I = [0,15].drop si`; `wexKey_eq` (the wrapping extension's key is the common prefix) |

Added (this round):

| module | content |
|---|---|
| `UpsReads` | **`UPB` reads**: `UpbBal` (nodeV3 + upsV3 on `UPB`), `upbMsgs` (only read rows use `UPB`; `rd ⇒ qb`), **`upb_read`** (`Walk3.chain_provided`: a read row's key is record `sN`'s key at `spos`: `sN < |vs|`, `rb` = post byte, `plen` = `|pre|`, `pdep` = depth, `rcid` = `ucid`), **`upb_reads`** (`UpsExt0.reads` with `Pb = postB vs`); `memRead` (every part but the new leaf reads on its first `MEM` row), **`ups_nparts`** (`|ps| ≤ 404`: the first upper part reads a record at depth `dep_D − 1 < 400`), **`ups_idBound`** (`UpsIdBound` from it and `τ < 2^17`) |
| `UpsSrc` | `post_node` (every record's post subtrie `fullTree R V' n`: `nodeEnc = toB (ser true)`, a node, usage `< 2^64`; `head_of` + `enc_fullTree_post`), `srcOf` (**`src k = fullTree R V' (sN of part k)`**), `part_sN` (every part's `sN` is a record; the new leaf shares its parent part's), **`ups_srcEnc`** (`UpsExt0.srcEnc`, and `ups_partsG`'s "sources are nodes with usage `< 2^64`") |
| `UpsVal` | **interface `SchedVal v sv`** (below); `ups_valRow` (value rows carry `sv τ`), **`ups_vlen`** (`|sv τ| = L0 + 256 L1 + 65536 L2` = number of value rows, given the limbs are bytes), **`ups_digV`** (`UpsExt0.digV`: `sha_core` with the value rows' `BYTES`), **`ups_xy`** (`UpsExt0.xy`: the terminal `KEY` nibble differs from the walk symbol) |
| `UpsWalk` | the `upsV3` walks in the walk link: `allWalks ws v = ws ++ v.map upsWalk`, `WalkBal` (the `EDGE`/`BMAP` balance of nodes, heads, `walkV3`, `upsV3`) ⇒ `Walk3.BusBal` over `allWalks` (`walkBal_all`); **`ups_bm`** (`W3`'s `BMAP` bitmap is a branch record's, `< 2^16`: discharges `ups_walk`'s hypothesis); `allWalks_wf`; **`ups_walkHyp`** (`Walk3.WalkHyp` of all walks: `walk3_pos`/`walk3_find` apply to `upsV3` walks); `edge_I`, **`ups_tiLe`** (`UpsExt0.tiLe`) |
| `UpsShape` | `SrcOk` split: **`NodeOk3`** (generic: encoding `< 2^22`, usage `< 2^64`, nibbles `< 16`, keys `< 510`, 36-byte slots of length `< 2^32`, 16 children, 32-byte child hashes) and **`SrcShape`** (constructor and slot / key conditions per kind); `srcOk_of`; **`post_nodeOk`** (`NodeOk3` of every record's post subtrie); **`ups_srcOk`** (`UpsExt0.srcOk` given the parts' `SrcShape`) |
| `UpsExt` | **`UpsEnv`** (the other tables' facts, collected); **`ups_ext0`** (`UpsExt0` of every segment given `SrcShape` and `vbytes`); **`ups_partsAll`** (every part emits `nodeEnc (upsQ k)` with exact `MEMD` limbs) |
| `UpsRec` | record facts (no table): `edge_branch` (a non-`END` edge of a branch is `DOWN` to a revealed child in the symbol's slot), `edge_key` (a `KEY` edge belongs to a leaf / extension, before its key's end), `edge_lend` (`LEND`: a leaf), `ser_tag` (byte 0 = `tagOf`: 0 leaf, 3 extension, 1 / 2 branch without / with value), `ser5_leaf`/`ser5_ext` (byte 5's high nibble `2·isLeaf + odd`), `ext_nil_of` (bytes 1, 5 = `1`, `0` ⇒ key `[]`), `kidAt_node`/`kidAt_none`, **`post_eq`** (a record's post subtrie is `nodeTree3` of its `Rec3`) |
| `UpsPath` | the walk's path records (with `ups_walkHyp`): **`ups_levels`** (`D ≤ t* − 1`; `D ≥ 1`: `W1` steps out of `N_0`; `D = 2`: `t* = W3`, `W2` steps out of `N_1`; `t*`'s record is `N_D`), `rowEdge`, `stepSym`, **`ups_downSlot`** (a branch at level `d < D` has a revealed child in `slotOf d`), **`ups_termEdge`** (an absent-by-key terminal's `LEND` / `KEY`-at-`I` edge is `N_D`'s), **`ups_termBmap`** (an absent-at-branch terminal's `BMAP` is `N_D`'s: `hasVal = 0` on `W3`, bit `y` clear on `W1`/`W2`) |
| `UpsTag` | the part's reads of its source's first bytes: **`tagCopy`** (`RDB RDE RLP RBR PT` copy byte 0 onto their `TAG` row, whose byte is the node type), `copyRow`, `firstTag`, **`ptHead`** (`PT` copies bytes 1, 5 = `qhk = 1`, flag `0`, `bHPFp`), **`tagNib5`** (`MVL MVE` and `ESx1`'s `SPB` read byte 5 on their `TAG` row, `spos = 5`, high nibble `2·qtl + podd`: `tagNib`, `rdTag`) |
| `UpsShapeK` | **`ups_shape`**: every part's source has its kind's `SrcShape` (constructor from the tag / the walk; `RDB`'s slot from `ups_downSlot` with `descLt` (`sdx < D` from the descend counter); `RBV` (`w3Si`: `t* = W3`) and `RBI` from `BMAP`; `LSa` from `LEND`; `MVL`/`MVE`/`ESx1` from the `KEY` edge (`I < |k|`) and byte 5); `kindCase`, `kindCaseK`, `tag_cases`; **`ups_ext0S`** / **`ups_partsAllS`**: `ups_ext0` / `ups_partsAll` without the shape hypothesis |
| `UpsVb` | **step 2, `vbytes` without an AIR change**: `valKind` (every case has a part with a fresh `VLEN` field: `RLP RBR RBV NLF`, or the `LSb ESl0 ESl1` split branch), **`vbPart`** (its rows `L0 L1 L2` are three of its emitted bytes), **`ups_vbytes`** (with the segment SHA facts and the lookups `ups_look0`, which do not use the limbs), **`ups_vbytesE`**; **`ups_ext0V`** / **`ups_partsAllV`**: `UpsExt0` and every part's bytes with exact `MEMD` limbs from `UpsEnv` alone.  `UpsLook`: `ups_look0` (lookups from reads, sources and walk facts); `rbiLook`/`spbLookY`/`spbLookC` dropped their unused `vlen`/`vbytes`/`digV` arguments |
| `UpsRoot` | **root binding** (AIR fix): `rootSrcRow` (the root part's `sN` is `rootRid`), **`ups_rootSrc`** (= the head's `rid`, via `RootChain.rid`) |
| `UpsUpsert` | step 3, spec side: `kids_upsert_some`/`kids_upsert_none`, **`upsert_rdb`**, **`upsert_rde`**, **`upsert_pt`** (a descend / pass-through is `qRDB`/`qRDE`/`qPT` of the child's upsert), terminal nodes `upsert_rlp`/`rbr`/`rbv`/`rbi`, `upsert_leafSplit`/`upsert_extSplit` |
| `UpsKey` | step 3, walk side: `stepEdge`, **`res_depth`** (a record's `res` is at least as deep, strictly unless itself), **`stepRow`** (a step without `enter` advances along its record's key; with `enter` it descends into a revealed child whose `res` is the next row's record), `lv23`/**`ups_lvl`** (rows' records `N_lvl`, `D` = number of entries), **`rowKey`** (`k.take p = (key.drop (i−1−p)).take p` at every row, branches at `p = 0`) |
| `UpsTerm` | **`mveLong`** (`MVE` keeps a non-empty key: `pf·kMVE·nokey·(1−qodd)` and the flag byte), **`esx1Len`** (`ESx1`: `|k| = I + 1` from `2·phk + podd = I + 3`, `phk` read on the first bitmap row) |
| `UpsTermT` | **`ups_term`**: `upsert (T N_D) ([0,15].drop (t* − 1 − I)) v = some (upsQ (nT − 1))` in all eleven cases (`LP`: `VAL` edge at the leaf key's end; `BR`/`BV`/`BI`; splits via `SpbSplit` with `rowKey`, the terminal `LEND`/`KEY` edge, `mveLong`, `esx1Len`, `ups_xy`; `wexTop`: the wrapping extension is `wrapExt (k.take I)`) |
| `UpsChain` | **step 4**: `upsE s = ⟨τ, reg(W0), reg(W3)⟩`; `ups_rootMsgs`/`ups_midMsgs`; **`ups_chain`** (`root_chain` for the real table: `RootChain hs (v.map upsE) K r0 rK`), **`ups_tauDistinct`**, `ups_tauBound` (`τ ≤ K`); **step 3, root half**: `rootLook3`, **`ups_rootDig`** (`(upsE s).post = sha256 (nodeEnc (upsQ (|ps| − 1)))`) |
| `UpsCid` | the child-id reads of the upper parts (no AIR change): **`extCid`** (`RDE`/`PT`: on the window's first row `rd = rdc = 1`, `spos = 5 + Pb[1]` (byte 1 = `|hp|`, copied on the `HPL` row), `rcid = cN`; `fw = 1` from the `HPF`/`KEY` row before, `tgt = fw`), **`rdbCid`** (`RDB`: `c0 ∈ {3, 39}`, the `MEM` read gives `plen = c0 + 32w + 8`; for `w > 0` the read is at `c0 + 32·e*`, `e* = w − 1` for slot 15 / `0`), `rdCH` (a window row with `cp = 0`, `rdc = 1` is read) |
| `UpsUpper` | **step 3, upper chain**: `Eoff` (key consumed above a level: `ℓ` below `D`, `t* − 1 − I` at `D`), **`ups_desc`** (each `d < D` is left on an `enter` row `i` with `d + 1 + nI = i`, landing on `N_{d+1}`, `Eoff (d+1) = i`; `Eoff 0 = 0`), `lvlOf`/**`lvl_succ`**/`lvl_top` (the level below an upper part is its `rc`; the root part's is `0`), **`ptDeep`** (below a pass-through the next non-`PT` part reads `N_rc`, strictly deeper), record facts (`serBr_len`, `filter_take15`, `extSer1`, `kidsBytes_len`), **`chStep`/`ups_ch`** (top-down from `ups_rootSrc` via `top_inv`: the head's `START` edge lands on `rres = res rid = N_0`; a `PT` record is not its own `res` (depth), so `.ext [] (.node c …)` (`resOk`) with `c = sN (k−1)` (`extCid` + `kidCidOk`), `res c = N_rc`; a descend at `N_d` takes the walk's revealed child (`stepRow` at the `enter` row, `rowKey` for an extension's key; `RDB` slot `slotOf d` = `wsym (d+1)`, window position matched to `kidCidOk` through `plen`), **`ups_up`** (bottom-up from `ups_term`: `upsert_pt` / `upsert_rdb` / `upsert_rde`), **`ups_upsert`**: `upsert (fullTree R V' (headAt τ).rid) [0,15] (sv τ) = some (upsQ (|ps| − 1))` |
| `UpsLink` | **step 2**: `ups_s0fMsgs` (one `S0F [τ, pres, vid]` by `W0`), **`ups_s0f`** / `upsV3_s0f` (`walk3_find_of` on the `upsV3` walk with the post values, `walkHyp_any`: `pres = 1` and `T'_τ.find [0,15] = some (some (valOf V' (vpos vid)))`, or `pres = vid = 0` and `find = some none`); **step 3**: `upsert_isNode`, `ups_post` (`(upsE s).post = hashOf Q` with `ups_rootDig`, `hashOf_eq_enc`), **`upsV3_link`** (every `τ ≤ K`: `upsert T'_τ [0,15] (sv τ) = some Q`, `ROOT` digest `= hashOf Q` byte for byte (`toB` form too), `= (headAt (τ+1)).pre` for `τ < K`, `= rK` for `τ = K`), **`upsV3_linkB`** (the same and `S0F` from views, balances, `ShaHyp` and the interfaces only) |

**AIR fix (M7e, lead-approved): the root part is bound to the instance's root record.**  `cid` is free on
unrevealed windows (`kidCidOk` constrains it only for `.node` kids), so above the walk's first record `N_0` the
pass-through chain had no fixed top: the root part's source was any depth-0 record, and a pass-through could use
an empty-key extension with a `.hash` child from another instance (§6.2's argument assumed the record was on
`τ`'s path).  Fix: `headV3` sends `MIDROOT (τ, rid, post)`; `upsV3` receives it into the segment constant
`rootRid` (column 186) and pins `qb·rootP·(sN − rootRid) = 0`.  `Chain3.UpsE` gets `rid`, `RootChain.rid`
(`(upsAt τ).rid = (headAt τ).rid`); **`ups_rootSrc`** (`UpsRoot`): the root part's source is the head's `rid`.
Budget (`BudgetUps`, kernel-checked): `upsV3` 187 columns, `W_eq` 330 → 331 (g=1), 290 → 291 (g=3); lane total
1201 → 1202 / 1081 → 1082; interactions and degree unchanged; `headV3` unchanged (161 / 161).  Model check
(`upsv3_model.py`, `rootRid = chain[0]`): seeds 1 (100) and 4 (200, `chain_prob = 0.4`), 0 failures.

Changes to existing statements (all rebuilt): `SrcOk` and the `RBI`/`MVL`/`MVE`/`SPB` lemmas take encodings `< 2^22`
(was `2^20`) and keys `< 510` nibbles (was `400`), the bounds the records give; `WalkWf3.nrows` is `≤ 2^23` (was `2^21`)
so that the `upsV3` walks fit (`wrows_lt` unchanged); `Chain3.UpsWf` → `UpsEWf` (name clash).

**Interface hypotheses (new):**
* `SchedVal v sv` (scheduler ↔ `upsV3`, V3-D0-DESIGN §12): `sv τ` is the new value of instance `τ`; every `SPLEN`
  receive is a scheduler send `[τ, |sv τ|]`, every `SPOST` receive a send `[τ, d, (sv τ)[d]]` with `d < |sv τ|`
  (as `Fp` images), `|sv τ| < 2^24`.  Discharged in the assembly by v3-sched's `codec_schedVal`
  (`Sched/Link/CodecSV.lean`, lane/v3-air; `sv τ` = the codec post-byte column); its ownership conditions
  (`CodecValOwn`, `SparOwn`) and the `SPAR` `PubIdx` are assembly obligations.
* (discharged) `walkV3`'s height `≤ 2^21` (`hWr` of `allWalks_wf` / `ups_walkHyp`): now exported by
  `WalkV3ViewStmt` next to `WalkWf3` (whose `nrows` stays `≤ 2^23` for `walkV3` and `upsV3` walks together).
* `UpsEnv` collects the balances (`UPB`, `MEMD`, `BYTES` with others' ids not of kind 12, `DIGEST` provided) and
  `τ < 2^17` (from `ups_tauBound` with `K < 2^17`).

**M7e: done** (b0ed3cf4, 08fc3d85; axioms of `ups_upsert`, `ups_s0f`, `upsV3_link`, `upsV3_s0f`, `upsV3_linkB`:
propext, Classical.choice, Quot.sound):
* (done) **`SrcShape`** of every part: `ups_shape`.
* (done) **`vbytes`**: `ups_vbytesE`.
* (done) **step 3**: spec lemmas (`UpsUpsert`), walk key facts (`UpsKey`), terminal half `ups_term` (`UpsTermT`), upper
  chain **`ups_upsert`** (`UpsCid` 252 lines, `UpsUpper` 599 lines): the `RDB` target window (first / last) is matched
  to `kidCidOk`'s position `(1|37) + 2 + 32·#present(kids.take j)` through the source length (`plen` on the `MEM`
  read, `serBr_len`: `c0 ≡ 3, 7 mod 32` pins `c0` and `w`) and `filter_take15` for slot 15.  `T' = fullTree R V' rid`
  directly (no `prune`, no `upsert_hashOf_congr` needed).
* (done) **step 2**: `S0F` = `T'_τ.find [0,15]` (`ups_s0f`, `UpsLink` 246 lines).
* (done) **`upsV3_link`** / **`upsV3_linkB`** (per `τ ≤ K` with `ups_chain`).

**Hypotheses of `upsV3_linkB`** (views, balances, SHA and interfaces only):
* views: `NodeWf3 vs`, `HeadWf hds`, `ValWf es`, `UpsWf v`, `WalkWf3 ws`, `(ws.flatMap (·.steps)).length ≤ 2^21`
  (`WalkV3ViewStmt`'s height conjunct);
* balances: `Link3.ParentBal`, `Link3.VParentBal`, `UpbBal vs v`, `WalkBal … B_EDGE`, `WalkBal … B_BMAP`,
  `Link3.KeynibOk ws prov`, `BYTES` (`shaR B_BYTES m = cnt (upsV3 sends ++ othersU) m`, `othersU` ids `< P`, not of
  kind `K_VUPS`), `DIGEST` provided (`0 < shaS B_DIGEST m`), the `MEMD` permutation, `ROOT` / `MIDROOT`
  permutations with `K + 1 < P`, `K < 2^17`, `r0` / `rK` canonical, `|hds| < P`;
* SHA: `Link3.ShaHyp vs hds es others shaS shaR`;
* interfaces: `SchedVal v sv`, `Link3.VPostOk others pv`, `vpostLen` (`(pv i).length ≤ l` on every written value slot).
Derived inside: `RootChain` (`ups_chain`), `UpsTauDistinct` (`ups_tauDistinct`), `τ < 2^17` (`ups_tauBound`), the walk
hypotheses of all walks (`ups_walkHyp`, bytes from `Link3.rec_bytes`); `UpsEnv` assembled.

**Unconstrained cells read by the link (STATUS §6 register):**
* (closed) `W0`'s value-length limbs `L0 L1 L2` (`vbytes`): not range-checked on `W0`; discharged by `ups_vbytesE`
  (each limb is a byte the value-carrying part emits on `BYTES`; SHA's contract bounds it once that part's digest
  is looked up, `ups_look0`).
* (closed) `W3`'s `BMAP` bitmap `wbm`: now discharged by `ups_bm`.
The other cells the links read (`rx`, `rb`, `mBv`, `mCv`, `clen`, `qlen`, `dI`, `dL`, `reg`, `j`, `jm`, `idx`, `gD`,
`gMs`, `gMr`, `sN`, `spos`, `plen`, `pdep`, `rcid`, `u`, `nI`, `nI2`, `nib`, `tX`) are pinned by the table or by a
balance.

## 9. Model check (tested)

`zk-formal/test/upsv3_model.py` checks the design against the spec. Run it as:

```
lake env lean --run test/UpsExport.lean > ups_air.txt
python3 test/upsv3_model.py ups_air.txt [seed] [instances] [chain_prob] [long_chain]
```

`chain_prob` is the probability that a node on the path sits below a chain of empty-key extensions (length 1–3: 50%, 4–15: 30%, 16–50: 20%); `long_chain > 0` adds one chain of that length above the root.

For each instance the script:
1. builds a random well-formed partial trie revealed along `[0, 15]` (non-canonical shapes included, and chains of empty-key extensions on the path), with stored `memory_usage` small, near `2^64` or random, so that truncation and `≥ 2^64` exact values both occur;
2. builds the `nodeV3` record view of that trie (ids, depths, post bytes, window child ids, edges, `BMAP`; empty-key extensions provide no edges and pass their child's `res` up);
3. runs the walk and generates the `upsV3` segment by the design rules;
4. checks:
   * every exported constraint vanishes on every row;
   * the emitted `Q_j` bytes equal `ser` of the spec `PTrie.upsert` result's new path nodes, and the post root equals `hashOf (upsert …)`;
   * every `UPB` read is of a record on the path, with that record's (byte, len, depth), and its `cid` is the record's window child id on window bytes;
   * the `MEMD` sends equal the receives;
   * every `DIGEST` lookup equals sha256 of that id's emitted bytes at that length.

**Results (M7c).** 3,740 instances, 0 failures:
* seeds 1–3, 400 each, no chains (the M7b regime);
* seeds 4–7 and 11, 500 each, `chain_prob = 0.4`: 1,123 instances had no pass-through part, 548 had 1–3, 460 had 4–15 and 369 had ≥ 16; the largest `nQ` was 104;
* seed 13, 40 instances, one chain of 397 above the root: `nQ` up to 401 (`j < 512`).

Coverage:
* all 26 reachable (case, `D`) pairs;
* truncation (`neg = 1`) in `RDB`, `RDE`, `PT`, `MVE`, `RBR` and `SPB`;
* `R ≥ 2^64` in `RDB`, `RDE`, `PT`, `RBI`, `RBV`, `SPB` and `WEX`.

The M7b script had a bug in `rmem` (the near-`2^64` branch was unreachable); it is fixed. The constraints are now compiled to one Python function for speed.

This checks **completeness and agreement with the spec** of the design. It does not check soundness, which is §6 and M7c–M7e.

## 10. Open points for the lead

1. **Resolved (lead):** the `UPB` format `(NPOST n, pos, pb, len, depth, cid, u)`; `MEMD` (23) with `(τ, j, i, new, old, qlen)`; empty-key extensions on the path are handled by pass-through parts (§1.1); ids `512τ + j`.
2. **`cid` is free on unrevealed windows** of `nodeV3`. Soundness of the chain (§6.2) therefore uses the walk: a `PT` source with an unrevealed child would be its own `res` and would have ended the walk. An alternative that avoids this argument is to send `rv·cid` (or `cid` only on `gP` rows) on `UPB`. That changes the binding message, so it is not done.
3. **Width is not optimised.** The 186 columns favour a simple view. The 11 case columns, the 4 `jo` columns and the 10 part-constant arithmetic selectors could be merged into fewer encoded columns, at the cost of higher-degree selector algebra in the view.
4. **Fixed (M7c layer 2, lane/v3-trie-h): the node type of a split branch without a value was free.** `cPlan`
   pinned `qtb2 = spValE` for `SPB` but nothing excluded `qtl`/`qte` when `spValE = 0` (`LSc`, `ESn0`, `ESn1`), so
   an `SPB` part could take the leaf or extension grammar, whose `HPF`/`KEY` bytes no rule constrains for `SPB`
   (a free key in `Q_SPB`).  Added `pf·kSPB·(qtl + qte) = 0` (degree 3; budget unchanged: width, interactions and
   the maximal degree are the same).  Re-checked with the model (`test/upsv3_model.py`, seeds 1 (400) and 4 (500,
   `chain_prob = 0.4`): 0 failures).
