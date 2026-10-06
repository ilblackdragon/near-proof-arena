# STATUS — lane `v3-rcpt` (receipt side of the v3 D0 AIR)

Branch `lane/v3-rcpt` (off `lane/v3-air` `5622eb84`). Design: `V3-D0-DESIGN.md` §1, §3.4–3.7,
§10–§13. Interfaces: `STATUS-V3-TRIE.md` (`KeynibOk`, walk `FINAL`, `VBYTES`/`valV3`, `hpl`,
`hperm`, `ShaHyp`), `STATUS-V3-BUS.md` (`AirP`/`HoldsP`/`PubSeg`), `STATUS-V3-SPEC.md` (`Prep`,
`Hint = {n, body}`, duplicate chunk hashes). Lean: `zk-formal/ZkFormal/NearV3/Rcpt/`. No v1
table, proof or definition and no spec file is modified.

Rules: no `sorry` / `axiom` / `native_decide`; axioms ⊆ {propext, Classical.choice, Quot.sound}.

## Plan and milestones

| # | milestone | state |
|---|---|---|
| M0 | design: tables, buses, message formats, public data, walk ids, cuts (§1–§3) | **done** |
| M1 | table definitions `rcptV3`, `acctV3`, `akeyV3`, `bndV3`, `srcpV3`, `sizeV3`; kernel-checked budget | **done** (§4) |
| M2 | views of the small tables (`…ViewStmt` proved): `acctV3`, `akeyV3`, `bndV3`, `sizeV3` **done** (helper, §5); `srcpV3` in progress | partly done |
| M3 | renders of the small tables: `acctV3`, `akeyV3`, `bndV3`, `sizeV3` **done**; `srcpV3` in progress | partly done |
| M4 | `qvV3` (fixed-key value parsers `[7] [10] [13] [16]‖s`), `mrkV3` / `sortV3` (`n ≤ 4481`, `n = 0`) | open |
| M5 | `rcptV3` view (`RcptV3ViewStmt`, adapting v1's 7.3 k-line `Extract/Rcpt*`) | statement done; proof ≈ 35 % (§6) |
| M6 | `rcptV3` render | open |
| M7 | links: body binding (`stream_eq_of_count`), lists ⇒ `verifyReceiptProof`, routing ⇒ A2, run ⇒ `applyReceipts` (incl. `applySystemReceipt`), `KeynibOk` for the sends, `hpl`/`hperm` for account writes | open |
| M8 | heights under A1 / B0 | open |

## 1. Tables (V3-D0-DESIGN §3.4–3.6 as built)

### 1.1 `rcptV3` (`Rcpt/Tables/Rcpt*.lean`)

v1 `rcpt` with **columns `0 … 227` at v1's indices** (so v1's view / render proofs transfer by
adaptation) and new columns `228 … 262`.

* **Lists.** Per applied source list `j` (consecutive from 0 = applied order): 12 header rows
  (`sCL`, v1's claim-row state) emitting `u64 own ‖ u32 n_j` into `RC(j)` (`K_RC + 16 j`), then
  the list's receipts. `j`, `nj` list constants; `cj` (v1 `rcnt`) counts the list's receipts and
  equals `nj` on the list's last row `le`; `RCL (j, |RC(j)|)` is sent there (to `srcpV3`). `r`
  is global; `o` restarts at 12 per list; the body position `o2` is global from 8.
* **Removed**: claim rows' prefix / gas-limit / `gas_burnt` / `nref` checks and the `RC`/`RF`
  digest lookups (all native now, or replaced by `srcpV3` and the public body).
* **System receipts** (`sys`, v1 `lo8`): `sys ⇔ predecessor = "system"` (both directions);
  `sys ⇒` no refund; burn price `pc = (1 − sys)·p`, so `burnt = 0`, tokens unchanged, outcome
  `tokens_burnt = 0`, `gas_burnt = G` (v1 rows unchanged); the refund-flag rule uses
  `gq = ge·(1 − sys)`.
* **Signer = receiver** (`ee`, v1 `lo4`; `ee ⇒ sys`): `ee ⇒ Ls = Lv` and every signer row
  receives `SREC (r, i, v_i)` from the receiver row `i` (so `s = v`); `sys ∧ ¬ee ⇒` `Ls ≠ Lv`
  (`invL`) or exactly one signer row `i` with `s_i ≠ v_i` (`dd`, `scnt`, `invD`).
* **Access-key walk** (`ee`): `KEYNIB (W_AK + r, t, sym, last)` for
  `nibbles([2] ‖ signer ‖ [2] ‖ kt ‖ pk) ++ [END]`: `T0` row (t 0, 1), first `SL` row
  (t `2+2Ls`, `3+2Ls`), `S` rows, `KT` row, `PK` rows (nibbles in `xb 0 … 7`), `END` on the first
  `GP` row (t `70 + 2Ls + 64 kt`). Key slots A and B are generalised (walk id
  `r + W_AK·[T0 ∨ SL ∨ S ∨ KT ∨ PK ∨ GP]`). `FINAL (W_AK + r, 0, fkF, kF)` on the `T0` row:
  absent, or `VAL` with `AKC (kF, u) → (kF, u+1)` through `akeyV3`.
* **Routing (A2)**: interval `q` (receipt constant); on `V` rows and on the first `RID` row
  (position `Lv`, byte `0` = end marker) while undecided (`eqL ∨ eqH`):
  `BND (65 q + i, lo_i, hi_i, hn, u) → (…, u+1)`; `v − lo + 255`, `hi − v + 255` as 9 bits
  (`xb 20 … 37`), equality indicators `eL`, `eH`; equal-so-far ⇒ `lo_i ≤ v_i ≤ hi_i`; at the end
  `v < hi` strictly. (`0` is never an account-id byte; boundaries are valid account ids,
  `decodeLayout`.)
* **Body**: v1's `RF` emissions `(K_RF, o2 + …, byte)` are the refund body `B[8 …]`, received by
  the public bus; `lastR ⇒ o2End = |B|`.
* **End**: `lastR ⇒ r + [receipt row] = n`, `tok = H.prev_balance_burnt`.

### 1.2 Small tables

| table | rows | content |
|---|---|---|
| `acctV3` | 16 / written account | v1 `acct` constraints verbatim; pre bytes on `VBYTES (vid, pos, b)`, post bytes `BYTES (VPOST(vid), …)`, `MEM`, `VSLOT (vid)` |
| `akeyV3` | 9 / present access key | `VBYTES (vid, pos, b)`, last byte `1`; chained provider `AKC (vid, 0) / (vid, U)` |
| `bndV3` | 1 / public routing record | `BNDP (x, lo, hi, hn)` from public; chained provider `BND (…, 0) / (…, U)` |
| `srcpV3` | per list: root row, 32-row leaf segment, 64-row path segments | `RCL`, public `SRC (j, dup, root)`, `DIGEST (RC(j), L)`, rehash, path, `root_j`; `dup ⇒ L = 12`; `SIZE (2, Σ L + 33·#items)` |
| `sizeV3` | 3 rows | `SIZE (t, x_t)`, `t < 3`; `x_0 + x_1 ≤ 3,000,000`, `Σ x_t + OVH ≤ 8,388,608` (24 bits) |

## 2. Interfaces

### 2.1 Buses and ids (`Rcpt/Ids.lean`)

New buses `14 SRC`, `15 BND`, `16 SREC`, `26 RCL`, `27 AKC`, `28 BNDP`, `29 QSH` (reserved for
`qvV3`); reused `0 BYTES`, `1 DIGEST`, `3 VSLOT`, `5 KEYNIB`, `6 FINAL`, `7 MEM`, `8 RIDS`,
`9 MPOS`, `18 SIZE`, `21 VBYTES`. SHA kinds: 1 `RC(j)`, 2 body (not hashed), 3–6 v1, 10
`VPOST(vid)`, 13 `SRC(q)`. **`K_VAK = 14` is not needed** (access-key values are `valV3`
records hashed as `VPRE(vid)`).

Walk ids: account `r`, access key `W_AK + r` (`W_AK = 8192 > 4481`), fixed keys
`W_QV + τ + 64·slot` (`W_QV = 16384`).

### 2.2 Requests to other lanes (blocking for the links, not for the tables)

* **R1 (bus lane / assembly): indexed public segments.** Public elements are bytes
  (`pubOf = cb'` bytes), so positions and record indices cannot be record fields. Needed:
  `PubSeg` with a constant prefix and an index field, message `pre ++ [off + j] ++ record_j`:
  `SRC`: `[j] ++ [dup] ++ root`; `BNDP`: `[x] ++ [lo, hi, hn]`; body: `[K_RF] ++ [8 + j] ++ [B[8+j]]`
  on `BYTES`. The assembly's other lanes (scheduler records) likely need the same.
* **R2 (spec / assembly): prepared statement.** Header fields at static offsets: `n` (30),
  `own` (34), `height` (50), gas price (58), outcome root (146), balance burnt (178) as in
  `Prep.encode`; **new**: `u32 |B|` (`PH_BLEN`) and `u32` witness overhead (`PH_WOVH`).
  Records: per applied list `(dup, root)` with `dup` = "an earlier used slot has the same
  chunk hash"; natively: duplicate keys must have equal roots (else reject: the relation's
  single entry cannot verify two roots). Routing records: per own interval `q`, positions
  `i ≤ 64`: `lo_i` / `hi_i` (`0` past the end; `lo` missing = empty), `hn` (`hi` missing).
* **R3 (lane v3-trie): `hperm`.** Nothing in the current `nodeV3` forces a lockstep-written
  window (`tw = 1`) for an account value that `acctV3` rewrites (and `tw = 0` makes the post root
  ignore the write). Proposal: `nodeV3` receives `VSLOT (vid)` (bus 3, v1's) on `valStart·tw`;
  `acctV3` sends it once per segment (done). Then account writes ↔ `tw` windows is a bijection.
  (Alternative: a `wr` field on `VPARENT`/`VBYTES`.)
* **R4 (assembly): `ShaHyp` with a public body.** Body messages (kind 2) are received by the
  public bus, not by SHA; `others` must exclude them. With `o2End = |B|` the balance gives
  `shaR (kind 2) = 0` (lemma planned in M7).
* **R5 (spec):** `inIntervals (ownIntervals L own) a ↔ L.shardOf a = own` is tested, not
  proved; the routing link (A2) needs it.
* **R6:** `n = 0` is possible in D0 (all lists empty): `mrkV3` and `sortV3` must allow empty
  tables (v1 requires a first segment); `outcomeRoot [] ` is then checked natively.

## 3. Findings

* **Public data are bytes.** See R1: `stream_eq_of_count`'s `(i, B i)` messages need the index
  supplied by the verifier.
* **`hperm` gap** (R3): written accounts were not bound to `tw` windows.
* **Duplicate keys**: in D0 a duplicate used slot's list is empty (otherwise the applied ids
  repeat, `e.distinct_ids`), so `srcpV3` requires `L = 12` for `dup`; the extracted witness has
  one entry per distinct key plus the spec's filler entries (encoder).
* **Size accounting**: `SIZE` carries byte totals only; the constructed witness also has
  per-entry length prefixes. Either the senders count entries too (`SIZE (t, bytes + 4·count)`)
  or the overhead is bounded natively; to be fixed with the encoder (`ZkFormal.V3.EncodeWitness`).

## 4. Budget (kernel-checked: `Rcpt/BudgetCheck.lean`, `report_g1`, `report_g3`, `weqRcpt_g1/g3`)

| table | width | interactions | `W_eq` g=1 | `W_eq` g=3 | maxLog |
|---|---:|---:|---:|---:|---:|
| `rcptV3` | 263 | 18 | 431 | 367 | 22 |
| `acctV3` | 16 | 13 | 144 | 112 | 17 |
| `akeyV3` | 7 | 3 | 55 | 63 | 16 |
| `bndV3` | 6 | 3 | 54 | 62 | 13 |
| `srcpV3` | 56 | 5 | 120 | 128 | 20 |
| `sizeV3` | 31 | 1 | 63 | 63 | 2 |
| **total** | | | **867** | **795** | |

Not yet counted: `mrkV3` (v1 `mrk`: 122), `sortV3` (v1 `sort`: 81), `qvV3` (≈ 80–120).
Design estimate (§13): receipt extension ≈ 480 + small tables ≈ 700.

### 4.1 Cut candidates (not applied)

| cut | saving (g=1) | cost |
|---|---:|---|
| merge `akeyV3`, `bndV3`, `sizeV3` into one row-kind table (one quotient overhead instead of three) | ≈ 60–80 | three small views become one |
| `akeyV3` as a mode of `acctV3` (its lane-0 `VBYTES` send) | ≈ 40 | acct view + 2 interactions there |
| `SREC` via the key walk: none found (both directions are needed) | — | — |
| `sizeV3` as a bit-serial table (one bit column) | ≈ 20 | longer view |
| keep `g = 1` for the small tables (degree 6–8 at `g = 3`) | 8–16 / table | per-table `g` (L3) |

## 5. Small-table views and renders (helper, branch `lane/v3-rcpt-h`)

All in `NearV3/Rcpt/Extract/*Proof.lean` and `NearV3/Rcpt/Render/*Render.lean`; axioms ⊆ {propext,
Classical.choice, Quot.sound}; each checked with `#print axioms`.

| table | view | render (local, traffic) |
|---|---|---|
| `bndV3` | `bnd_view : BndViewStmt` | `bnd_render_local`, `bnd_render_traffic` |
| `sizeV3` | `size_view : SizeViewStmt` (`SizeWf`: `base_le`, `tot_le` as Nat bounds under no-wrap) | `size_render_local` (`SizeOk`), `size_render_traffic` |
| `akeyV3` | `akey_view : AkeyViewStmt` (9 bytes, last byte 1) | `akey_render_local` (`AkeyOk`), `akey_render_traffic` |
| `acctV3` | `acctV3_view : AcctV3ViewStmt` (v1 `AcctWf` + height) | `acctV3_render_local`, `acctV3_render_traffic` (`AcctV3Ok`) |

## 6. `rcptV3` view: port state (`NearV3/Rcpt/Extract/RcptView.lean`, `Extract/V/*.lean`)

* **Statement** `RcptV3ViewStmt` (built): view `RcptV3Vs` = lists `ListV3 {n0, n1, rs}` of `RcptE`
  (v1 `RcptV` + `sys ee gv gs sx akf akk aku q rlk`), traffic `rcptTraffic3`, facts `RcptE.Wf`
  (v1 facts with `sysIff`, system arithmetic, `ee` / `neq`, `RouteOk`) and `RcptV3Wf`.
* **Model check** (`test/rcptv3_model.py`, `test/RcptExport.lean`): honest traces of random
  D0 batches satisfy all 881 constraints with 0/1 multiplicities and exactly the expected
  traffic on every bus (≈ 500 instances over 6 seeds, 0 failures).
* **Ported and building** (v1 module → v3): `RcptFacts → V/Facts` (v3 list/receipt boundaries,
  header facts, `brkStep`, `leFacts`, `lconst`), `RcptSegs → V/Segs`, `RcptLayout → V/Layout`
  (unchanged receipt layout), `RcptTable → V/Table` (**new**: `rcpts_from` per list, block end
  = padding or next header), `RcptRegs → V/Regs`, `RcptRowT → V/RowT` (18 interactions),
  `RcptOf → V/Of` (`rcptOf` incl. v3 data), `RcptChunks → V/Chunks`, `RcptFB1/FB2 → V/FB1/FB2`
  (`RC(j)` ids via the list index), `RcptBytes → V/Bytes`, `RcptGates → V/Gates` (+ `lay_const`),
  `RcptBus → V/Bus` (+ `gF_row`), `RcptChars → V/Chars`.
* **Remaining** (in dependency order): `Key` (+ access-key walk symbols on T0/SL/S/KT/PK/GP),
  `Dig`, block decomposition of the whole table (`blocks_from`, j-constancy inside a block from
  `le = 0` off the block end), `Shape`/`Traffic` over lists (+ `RCL`, `FINAL` two rows, `SREC`,
  `AKC`, `BND` traffic), `WfEasy`, `Count`, `Gas1–3` (`pc`, `gq`), `Dep`, `Arith`, `Toks`
  (claim arithmetic dropped), `StrField`/`Strings`/`CharClass`/`Names` (`sysIff`), new `Sys`
  (`ee`/`neq` from `SREC` rows) and `Route` (`RouteOk` by induction over the lookup rows),
  `WfIds`, `Proof`. `test/port_rcpt_v3.py` does the mechanical part of each port.

## Modules

| module | content |
|---|---|
| `NearV3/Rcpt/Ids.lean` | buses, kinds, walk ids, public offsets |
| `NearV3/Rcpt/Tables/Rcpt/{Layout,Fields,Arith}.lean`, `Tables/Rcpt.lean` | `rcptV3` |
| `NearV3/Rcpt/Tables/{Acct,Akey,Bnd,Srcp,Size}.lean` | small tables |
| `NearV3/Rcpt/Budget.lean`, `BudgetCheck.lean` | budget |

Build: `lake build ZkFormal.NearV3.Rcpt.BudgetCheck` (17 s, kernel `decide`).

## Commits

(see `git log lane/v3-rcpt`)
