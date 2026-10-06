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
| `upsV3` | 186 | 15 | 15 | 4 | **330** | 6 | 8 | **290** | 22 |
| `nodeV3` + `UPB` delta | 186 (+1) | 20 (+2) | 20 | 4 | 370 (+17) | 7 | 8 | 298 (+1) | 22 |
| lane total (6 tables) | | | | | **1185** (838 → 1185) | | | **1073** (782 → 1073) | |

M7b had `upsV3` at 176 columns, `W_eq` 320 / 280. The pass-through mode adds 10 columns
(`dep0‥2`, `kPT`, `up`, `rc`, `pdep`, `cN`, `rcid`, `rdc`) and no interaction. The `nodeV3` delta
is unchanged in size: `cid` is an existing column.

The theorems are `ups_g1`, `ups_g3`, `nodeU_g1`, `nodeU_g3`, `weqTrieU_g1` and `weqTrieU_g3`.
* `upsV3` has 581 constraints, all of degree ≤ 4. Every interaction gate is a column, and every message has degree 1.
* Of the 186 columns, 14 walk-row columns are aliases of part-constant columns. The 32-byte register `reg` is reused by row kind (§2.4).

## 1. Interface

| bus | message | `upsV3` side | gate |
|---|---|---|---|
| `MIDROOT` 24 | `(τ, mid[32])` | recv | `W0` |
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
| `QNodes` | **target nodes** per part kind (spec side, as `PTrie.upsert` builds them): `qRLP`, `qRBR`, `qRBV`, `qRBI`, `qNLF` (`newLeaf ([0,15].drop (si+1)) v`), `qMVL`, `qMVE`, `qSPBleaf`/`qSPBext` (the branch of `splitLeaf`/`splitExt` before `wrapExt`), `qWEX`, `qRDB`, `qRDE`, `qPT`; `setKid`; `qNLF_enc` |
| `NlfRows` | `NLF` part constants (`nlfHead`: leaf, `hplen 1`, `R = 102 + L` formula), `memLR` (the `L` register on `MEM` rows), `nlfHpf` (flag byte `0x20 + 0x1f·ts1`) |

Not yet done (layer 2; estimate ≈ 2.5–3.5 k lines): the remaining field-level byte lemmas (copied fields with `spos` offsets, moved-key `HPF`, split-branch bitmap) and the
per-kind assembly `rowsB (part) = nodeEnc (node)` with the node defined from (case, source bytes, child digests, `MEMD`
values) as in `PTrie.upsert` — the target nodes are defined (`QNodes`); `NLF RLP RDE PT WEX RBV RBR RDB` are done (`NlfBytes`, `RlpBytes`, `RdeBytes`, `WexBytes`, `RbvBytes`, `RbrBytes`, `RdbBytes`); `RBI MVL MVE SPB` remain.  Method note: `omega` is incomplete with the modulus
`P ≈ 2^31` when several unknowns share a `% P` (it then reports spurious counterexamples or times out); such
facts go through `Fp` and `natv` (`wbmBits`), or through `decide +kernel` on index rows (`planDec`, `ixVals`).
M7d (render) and M7e (link) are not started.

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
