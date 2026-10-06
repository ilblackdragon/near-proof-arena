# `upsV3`: the `0x0f` upsert table (M7b design, for review)

Status: **M7b done, for lead review**, 2026-10-06. Branch `lane/v3-trie-h`, built on `lane/v3-trie` at c121be68.
Inputs: STATUS-V3-TRIE §2.3, §2.3.1 and §2.3.2; `spec/lean/NearSpec/TrieUpsert.lean`; `Spec/Absent.lean`; and `Link/Chain3.lean`, where `UpsE (τ, mid, post)` is the abstraction that this table refines.

Labels used below:
* **proved**: kernel-checked in Lean.
* **tested**: model-checked by the script in §9.
* **argued**: the soundness sketch, which is the job of M7c–M7e.

| deliverable | file | state |
|---|---|---|
| table `UpsV3.table` | `zk-formal/ZkFormal/NearV3/Tables/Ups.lean` | builds; degree 4 |
| bus ids | `zk-formal/ZkFormal/NearV3/IdsUps.lean` | `UPB 25`, `MEMD 23`; `S0F 59`, `SPOST 60`, `SPLEN 61` as agreed with v3-sched; `K_VUPS 12` |
| `nodeV3` delta, not applied | `zk-formal/ZkFormal/NearV3/Tables/NodeUpb.lean` (`NodeV3.tableU`) | builds; §7 |
| budget | `zk-formal/ZkFormal/NearV3/BudgetUps.lean` | **proved** (`decide +kernel`; axioms `propext`) |
| model check | `zk-formal/test/UpsExport.lean`, `zk-formal/test/upsv3_model.py` | **tested**: 2,650 random instances, 0 failures (§9) |

## 0. Budget (proved, `BudgetUps.lean`)

| table | width | interactions | aux g=1 | degree g=1 | `W_eq` g=1 | aux g=3 | degree g=3 | `W_eq` g=3 | maxLog |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `upsV3` | 176 | 15 | 15 | 4 | **320** | 6 | 8 | **280** | 22 |
| `nodeV3` + `UPB` delta | 186 (+1) | 20 (+2) | 20 | 4 | 370 (+17) | 7 | 8 | 298 (+1) | 22 |
| lane total (6 tables) | | | | | **1175** (838 → 1175) | | | **1063** (782 → 1063) | |

The theorems are `ups_g1`, `ups_g3`, `nodeU_g1`, `nodeU_g3`, `weqTrieU_g1` and `weqTrieU_g3`.
* `upsV3` has 549 constraints, all of degree ≤ 4. Every interaction gate is a column, and every message has degree 1.
* Of the 176 columns, 14 walk-row columns are aliases of part-constant columns. The 32-byte register `reg` is reused by row kind (§2.4).

## 1. Interface

| bus | message | `upsV3` side | gate |
|---|---|---|---|
| `MIDROOT` 24 | `(τ, mid[32])` | recv | `W0` |
| `ROOT` 10 | `(τ+1, post[32])` | send | `W3` |
| `S0F` 59 | `(τ, present, vid)` | send | `W0` |
| `SPLEN` 61 | `(τ, L)` | recv | `W0` |
| `SPOST` 60 | `(τ, pos, b)` | recv | value rows |
| `BYTES` 0 | `(msgId 12 (8τ + j), pos, b)` | send | value and node rows |
| `DIGEST` 1 | `(id, len, d[32])` | recv | fresh windows, `W3` |
| `EDGE` 4 | `(N, I, sym, N2, I2, ek, u)` | chained consumer (recv `u`, send `u+1`) | `mS + mK` |
| `BMAP` 11 | `(N, bm, hasVal, u)` | chained consumer | `mB` |
| `UPB` **25** | `(NPOST(n), pos, pb, len, depth, u)` | chained consumer | `rd` |
| `MEMD` 23 | `(τ, j, i, new_i, old_i, qlen)` | send (child) / recv (parent) | `gMs` / `gMr` |

* The `EDGE` and `BMAP` messages are `walkV3`'s (`Extract/WalkView.lean`).
* `S0F`, `SPOST` and `SPLEN` use v3-sched's numbers and formats (`Sched/Ids.lean`, `Codec.lean`).
* SHA ids: `K_VUPS = 12`, `idx = 8τ + j`. `j = 0` is the new value. `j = 1 … nQ` are the new path nodes `Q_j`, with `nQ ≤ 4` (§3.3), so `j ≤ 4 < 8`.

**Deviation from the binding UPB format.** The lead specified `UPB (NPOST(n), pos, pb, u)`. The message also carries the source record's `len` and `depth`. Both are existing node-constant columns of `nodeV3`, so the delta still costs 1 column and 2 interactions. Both fields are needed for soundness:

* **`depth` rejects empty-key extensions on the path.** `nodeV3` admits empty-key extensions (`eext`), and walks skip them: an `eext`'s `res` is its child's `res`. A walk edge `N_d → (N_{d+1}, 0)` can therefore jump over one or more `eext` records. `PTrie.upsert` would rewrite those records (`.ext [] c m`), and `upsV3` would silently drop them.
  * `upsV3` requires `depth(N_d) = d` for every record it reads. `N_0` comes from the head's `START` edge. Depth 0 means `N_0` is the root record `rid` and not a descendant of an `eext` root. Then `N_{d+1}` is a direct child of `N_d`.
  * Any `eext` on the path makes the trace fail. This only costs completeness, and only on tries that nearcore never produces. Note that the path can be arbitrarily long through `eext`s, so they cannot be supported with bounded rows.
* **`len` locates the `MEM` field of a branch and pins its window count.** Without it, a rewritten branch could claim fewer windows and read `memory_usage` from window bytes. The alternative is to read the bitmap and count bits, which costs 16 bit columns and a popcount.

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
* `W3` receives `DIGEST (msgId 12 (8τ + nQ), rlen, reg)` and sends `ROOT (τ + 1, reg)`.

### 2.2 Value rows (`vb`, part `j = 0`)

* Row `pos` receives `SPOST (τ, pos, b)` and sends `BYTES (msgId 12 (8τ), pos, b)`.
* The last row has `pos + 1 = L`, with `L = L0 + 256·L1 + 65536·L2`.
* The `L` bytes are emitted as fresh `VLEN` bytes in every case, so SHA range-checks them. The top byte is 0, so `L` is exact (`< 2^24 < P`).

### 2.3 Node parts (`qb`, `j = 1 … nQ`, bottom-up)

Part `j` emits `Q_j`. Row `qpos` sends `BYTES (msgId 12 (8τ + j), qpos, b)`, and the last row is the `MEM` field end with `qpos + 1 = qlen`.

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

### 2.4 Column map (176)

| range | content |
|---|---|
| 0–9 | `act wk vb qb sf wt1 wt2 wt3 pf pl` |
| 10–48 | segment constants: `tau`, `N0..N2`, `L0..L2`, the case one-hot (11), `dd` (3), `ts` (3), `ti` (3), `tX`, `xb` (4), `px`, `bmL`, `bmH`, `pres`, `vid`, `nQ`, `rlen` |
| 49–99 | part constants: `j`, kinds (11), `jo1..4`, `sd0..2`, `sN`, `plen`, `qtl qte qtb1 qtb2 qhk qodd nokey nochild qlen rootP jm clen`, the arithmetic selectors `Kc eL eS useA bN bL cO cS Cc neg`, `phk podd vcp xcp ba0 ba1 spY1 spY2`. On walk rows, 49–62 are `nN nI nib nN2 nI2 ek inv hv wbm enter lv0 lv1 lv2 trm`. |
| 100–128 | `qpos b rd rb spos u`, the 9 states, `fs fe idx fw lastw wfr tgt wy wn gD dI dL cp aft` |
| 129–160 | `reg[32]`, which holds a digest on fresh-window rows, `W0` and `W3`. On `MEM` rows it holds the chain temporaries: `tb[8] cb[3] cc[3] ci ci2 X1 Ein`. On `TAG`/`HPF` reads it holds nibble bits, and on `W1`/`W2` bitmap bits. |
| 161–167 | `LR[3]` (new length bytes), `SR[4]` (old value length bytes) |
| 168–175 | `gMs gMr rx mBv mCv mS mK mB` |

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
| `SPB` (split branch) | `N_D` | `TAG` = 2 (value) / 1; value slot: `LSa` = `P[len−44 … len−8)` (`s`'s ValueRef), `LSb`/`ESl` = `u32 L ‖ H(v)`; `BM` = `2^x` (unless `LSa`) + `2^y` (`LSa`, `LSc`, `ESn`); windows in slot order (`y = 0` first, else `x` first): `x`-slot = `DIGEST(Q_1 = MVL/MVE, clen)` or, for `ESl1`/`ESn1`, `P[len−40 … len−8)` (the old child hash `c`); `y`-slot = `DIGEST(Q_{j−1} = NLF, 50)`; `MEM` fresh | `MEM`; for `ESx1` also `P[5]` (extension, odd), `P[1]` (`hk`) |

Notes on the moved key (`MVL`/`MVE`):
* The hex prefix right-aligns the key nibbles, so `hp(k.drop t)` is `hp(k)`'s last `hk' − 1` bytes with a new flag byte. No nibble shift is needed.
* `hk' = 1 + ⌊|xs|/2⌋` and `e = hk − hk'`. The flag byte takes the low nibble of `P[5+e]` when `|xs|` is odd.
* The constraint is `2(qhk−1) + qodd = 2(phk−1) + podd − I − 1`.

### 3.3 Part plan (bottom-up, `j = 1 …`) and `nQ ≤ 4`

| case | terminal parts | then |
|---|---|---|
| `LP` / `BR` / `BV` | `RLP` / `RBR` / `RBV` | `RD × D` |
| `BI` | `NLF, RBI` | `RD × D` |
| `LSa` | `NLF, SPB` | `[WEX if I ≥ 1]`, `RD × D` |
| `LSb` | `MVL, SPB` | the same |
| `LSc` | `MVL, NLF, SPB` | the same |
| `ESl0` / `ESl1` | `MVE, SPB` / `SPB` | the same |
| `ESn0` / `ESn1` | `MVE, NLF, SPB` / `NLF, SPB` | the same |

**`RD` parts.** `RD` is `RDB` or `RDE`, chosen by the copied tag. The `RD` part at `j` reads level `nQ − j`. All terminal parts and `WEX` read level `D`.

**Bound `nQ ≤ 4`.** Each level `d < D` consumes ≥ 1 nibble, and a split consumes `I` more, so `D + I ≤ 2`. Hence `nQ = n_case + [I ≥ 1 ∧ split] + D ≤ 4`:
* `LSc`/`ESn0` with `c = 0`, `I = 1`: 3 + 1;
* `c = 1`, `I = 0`: 3 + 1 RD.

**Enforcement.** The plan is enforced on each part's first row: `Σ_k code_k·kind_k = Σ_i jo_i·plan_i(case, I)`, with code 0 for `RD`. The last part has `rootP`, `j = nQ`. A part beyond the plan would need source level `nQ − j < 0`, which is impossible.

**Child links.**
* A part's `DIGEST` child is `j−1`, or `jm = 1` for the moved node under `SPB`.
* `MEMD` runs from every part except the root and `NLF` to its parent:
  * `RD` and `WEX` receive from `j−1`;
  * `SPB` receives from `j = 1` in `LSb`, `LSc`, `ESl0` and `ESn0`;
  * the remaining parts fold the new leaf's usage `102 + L` into a constant.

## 4. Read positions (`spos`, every `rd` row)

| rows | `spos` |
|---|---|
| `MEM`, every reading part | `plen − 8 + idx` (the anchor: pins a branch's window count) |
| `RDB RDE RLP RBR` | `qpos` |
| `RBV` / `RBI` | `qpos − 36·aft` / `qpos − 32·aft` (`aft`: after the inserted value slot / window) |
| `MVL MVE` | `TAG`: 5; `HPL` row 0: 1; `HPF … CH`: `qpos + phk − qhk` |
| `SPB` | `TAG`: 5; `BM` row 0: 1; `VLEN`/`VH`: `qpos + plen − 45`; `CH`: `plen − 40 + idx` |

Which rows read is a function of kind, field and window flags: `rd = cp + extra` (`cBytes`). A prover cannot read at other positions, and the `UPB` message pins `(record, pos, byte, len, depth)`.

## 5. `memory_usage` arithmetic

Every `Q_j` has `R = E + max(0, A + B − C)`, matching the spec's `Nat` arithmetic:

| kind / case | `E` | `A` | `B` | `C` |
|---|---|---|---|---|
| `RDB`, `RDE` | 0 | `m` | `N_{child}` (`MEMD.new`, exact) | `old_{child}` (`MEMD.old` = child source's `m`) |
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
2. **No skipped records.** Every read checks `depth(N_d) = d`. With `kid_depth` and "`res c ≠ c` ⇒ `depth(res c) > depth c`" (from `nodeV3`'s `eext`/`xres` rules), each `N_{d+1}` is the record in `N_d`'s child slot. Moreover `N_0 = rid`.
3. **Copy restriction.** Every `UPB` id is `NPOST(sN)` with `sN = N_sd`, `sd ≤ D` and `depth = sd`, so it is a record on the `[0,15]` path of `τ`'s lockstep post-trie. The source is a part constant, set by the plan from the walk's segment constants.
4. **Source bytes.** `UPB` balance plus `nodeV3`'s view give `rb = ser(P_sd)[spos]` and `plen = |ser P_sd|`.
   * The `nodeV3` view is `NodeV3.ser true`. The delta needs the `UPB` traffic to be added to `nodeTraffic3`.
   * `B_0`'s high nibble gives leaf vs extension and the parity; `P[1]` gives `hk`. These positions are valid because `P_D` provides `KEY`/`LEND` edges and is therefore a leaf or an extension.
5. **Each `Q_j` is a spec node.** From the part's field grammar and §3.2, `Q_j = ser(q_j)` byte for byte.
   * `q_j` is the node of the spec construction with those fields: copied ranges are fields of `P` by `NodeV3.ser`, and fresh fields are the formulas.
   * Windows are `DIGEST`s. The ids are `msgId 12 (8τ + j')`, and the lengths are bound by `MEMD.qlen` (`clen`), the constant 50 (`NLF` is always 50 bytes) or `L`. So SHA's prefix behaviour cannot substitute a shorter message.
   * `MEM = u64 R` with `R` from §5, which is exactly the spec's `Nat`.
6. **Root.** The plan composes the spec cases (§3.1).
   * In the descend parts, `q_root = upsert (prune_{[0,15]} P_0) [0,15] v`.
   * Off-path windows are copied hash bytes, which are equal to `hashOf` of the pruned `.hash` child.
   * By `upsert_hashOf_congr`, `post = hashOf (upsert T_mid [0,15] v)`, and `ROOT (τ+1, post)` is sent.
7. **Uniqueness of ids.** Per `τ` there is one segment (`root_chain`), and `j ≤ 4` within it. So `(τ, j)` ↦ id is injective, and each id's `BYTES` are sent exactly once per position.

**Owed to the assembly lane (id-range lemma).** Every `BYTES`/`DIGEST` id that `upsV3` uses is `msgId 12 (8τ + j)` with `j ≤ 4` and `τ ≤ K`. So the `upsV3` ids are exactly kind 12 with `idx < 8(K+1)`. No other table may send kind 12.

**Completeness conditions** (render hypotheses):
* no empty-key extension on the `[0,15]` path of the lockstep post-trie;
* if `0x0f` is present, its value is revealed (the read needs it anyway);
* `1 ≤ L < 2^24`;
* the trace fits the height: `4 + L + Σ|Q_j|` rows per instance, `|Q_j| ≤ 559`, `maxLog 22`.

## 7. `nodeV3` delta (for the lead to apply)

Defined in `Tables/NodeUpb.lean` as `NodeV3.tableU`, for the budget only:

* **column** `mU := 185` (width 186): the per-row use count;
* **interactions** (chained provider, as `EDGE`):
  * `send UPB (c act) [mid K_NPOST (c nid), c pos, c pb, c len, c depth, 0]`
  * `recv UPB (c act) [mid K_NPOST (c nid), c pos, c pb, c len, c depth, c mU]`
* **constraints:** none.
* **view:** `nodeTraffic3` gains, per record and byte, `send [NPOST(nid), pos, pb, len, depth, 0]` and `recv […, mU]`, with `mU` canonical. The view proof is a port of the `EDGE` provider's.
* **render:** `mU` = the number of `upsV3` reads of that byte.

## 8. Plan for view, render and link

* **M7c, view (`UpsViewStmt`).** In the segment framework (`Near/Extract/Segments`), the view is one `UpsSeg` per `τ`:
  * `walk : List WStep3` (4), the case, `D`, `I`, `x`, `L`, `v`;
  * `parts : List UpsPart`, each with kind, `j`, `sd`, `plen`, its field list with bytes, its read list `(spos, rb)`, and its `MEM` limbs.

  `UpsWf` collects the row facts. The field grammar can be ported from `Extract/Node/Segs.lean`, since the states and the length/succession constraints are `nodeV3`'s on `q*` columns. The other facts are:
  * the provenance table of §3.2 as per-field equalities;
  * the read positions of §4;
  * **the chain lemma**: the 8-row carry chains give the exact `R = E + (A + B − C)` truncated, with `H` exact;
  * the plan (§3.3).
* **M7d, render.** The generator is `test/upsv3_model.py`'s `gen` (§9) transcribed to Lean.
  * Its inputs are the lockstep records, the walk, `v` and `τ`.
  * The local constraints are proved per part kind. Traffic matches by construction: the `UPB` reads are counted into `nodeV3`'s `mU`.
* **M7e, link.** Per §6 and per case:
  * from the view, the `nodeV3` records of `τ` and the walk, show `q_root = upsert (prune P) [0,15] v`;
  * the per-case lemmas are `upsert_brSlot`, `upsert_brVal`, `upsert_leaf_ne` with `splitLeaf`'s three cases, `upsert_ext_np` with `splitExt`'s, and `upsert_branch_down` / `upsert_ext_down` for the `RD` levels;
  * then `upsert_hashOf_congr`, plus `set_upsert_comm` / `trieOpsStmt` for the order relative to the lockstep sets.

## 9. Model check (tested)

`zk-formal/test/upsv3_model.py` checks the design against the spec. Run it as:

```
lake env lean --run test/UpsExport.lean > ups_air.txt
python3 test/upsv3_model.py ups_air.txt [seed] [instances]
```

For each instance the script:
1. builds a random well-formed partial trie revealed along `[0, 15]` (non-canonical shapes included), with stored `memory_usage` small, near `2^64` or random, so that truncation and `≥ 2^64` exact values both occur;
2. builds the `nodeV3` record view of that trie (ids, depths, post bytes, edges, `BMAP`);
3. runs the walk and generates the `upsV3` segment by the design rules;
4. checks:
   * every exported constraint vanishes on every row;
   * the emitted `Q_j` bytes equal `ser` of the spec `PTrie.upsert` result's new path nodes, and the post root equals `hashOf (upsert …)`;
   * every `UPB` read is a path record's (byte, len, depth);
   * the `MEMD` sends equal the receives;
   * every `DIGEST` lookup equals sha256 of that id's emitted bytes at that length.

**Results.** 2,650 instances over seeds 1–4, 7 and 11 gave 0 failures.
* All 26 reachable (case, `D`) pairs were covered.
* Truncation (`neg = 1`) was hit in `RDB`, `RDE`, `MVE`, `RBR` and `SPB`.
* `R ≥ 2^64` was hit in `RDB`, `RDE`, `RBI`, `SPB` and `WEX`.

This checks **completeness and agreement with the spec** of the design. It does not check soundness, which is §6 and M7c–M7e.

## 10. Open points for the lead

1. **Accept the `UPB` format with `len` and `depth`** (§1). Alternatives:
   * drop `len` and count the bitmap: +18 columns in `upsV3`;
   * drop `depth`: unsound with empty-key extensions unless `nodeV3` forbids them, which is itself a `nodeV3` constraint change.
2. **`MEMD` (23) is used** with the message `(τ, j, i, new, old, qlen)`.
3. **Empty-key extensions on the `[0,15]` path are rejected.** This costs completeness only; nearcore never builds them.
4. **Width is not optimised.** The 176 columns favour a simple M7c view. The 11 case columns, the 4 `jo` columns and the 10 part-constant arithmetic selectors could be merged into fewer encoded columns, at the cost of higher-degree selector algebra in the view.
