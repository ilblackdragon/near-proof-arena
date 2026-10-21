# pq-receipt-air: the promise/receipt bookkeeping AIR, the wire, and the `ActionR` verdict

Lane `lane/pq-receipt-air`, branched from `origin/main` `f51c8563c`, 2026-10-21.

DESIGN.md (`pq-host-promise`) priced the 23 D3α `promise_*` host functions as ≈ 7–12 lane-weeks,
split into bookkeeping (2–3 wk), the borsh `ActionR` encoder + `HOSTB` byte binding (4–6 wk, "the
dominant cost") and `RIDS`/`SRC`/`RCL` + the `newReceipts` fold (3–4 wk).  This lane delivers the
bookkeeping table, the wire link, and a **measured, kernel-checked verdict on the encoder**.  The
verdict is the headline: the encoder is *not* avoidable by coding cleverness, but the plan's
division of cost is wrong in one important way — see §3.

Everything below is on this branch; commit in §6.

---

## 1. The bookkeeping table `PBC` — built, `Holds`-ready, row-proved

`zk-formal/ZkFormal/PQ/Receipt/{Ids,Table,Rows,Bookkeeping,Wire,Statement,Cost}.lean`.

### 1.1 Shape

One row per `promise_*` host call, in `HOSTQ` (`ts`) order.

| item | value |
|---|---|
| columns | **49** (`Table.width`) |
| constraints | **51**, all degree ≤ **4** (`Table.pbc_degree`) |
| interactions | **29** (1 `PBK` + 25 `PBR` + 2 `HOSTQ`/`HOSTR` + 1 `BYTE`) |
| `maxLog` | 16 |
| `Table.wf` at `maxDeg = 8` | **passes** (`pbc_wf`, `decide`-checked) |

DESIGN.md estimated "~15–25 columns, ~10 degree-≤2 constraints".  The real table is **49 columns
and 51 constraints**, because the `HOSTQ` request's argument window (9 args × 2 limbs = 18
columns) lives on the row.  That is not padding: without it the row could answer a request it
never saw.  Of the 51, **11 are the degree-4 counter/gate group** and the rest are degree ≤ 2
(bit constraints, policy links, bounds).  So: **columns ≈ 2×, constraints ≈ 5×** the estimate, but
still a *small* table — the estimate's order of magnitude was right.

### 1.2 The division that makes it small

The class of a call — `(np, ar, knd, addR, addP, addA, hasTgt, hasDep, retKind, rtag, dadd,
hasBytes, nres)` — is a row of a **cached** table `PBK`, consumed on bus 211.  `PBC` copies it
into its own columns so constraints can read it, but the copy is *pinned by the receive*: a
prover cannot invent a class.  This is the `HOSTT`/`CODE`/`TAPE` pattern, not a new idea, and it
is what keeps `PBC` at 51 constraints instead of ~23 × 6.

`Ids.promiseClasses` is the transcription of `Host.lean`, arm by arm (each line cites its
`Host.lean` line).  The kernel checks the transcription, not just the shape:

| lemma | what it checks | axioms |
|---|---|---|
| `promiseClasses_ids` | ids are exactly `8 … 30` | none |
| `promiseClasses_shape` | every `np ≤ 9`, `ar ≤ 1` (the widened HOST chip) | none |
| `promiseClasses_policy` | `addR`/`addP`/`addA`/`hasTgt`/`hasDep`/`dadd`/`rtag` **agree with the spec's arm list** (`specAddR`, …) | none |
| `promiseClasses_nres` | `nres = 1 ↔ retKind ≠ 0` (`pushRet`) | none |
| `promiseClasses_kind` | every `knd ∈ 0..10` or is the "no action" marker 15 | none |

That last pair is the interesting content: **`decide` compares the table against a second,
independently written list** of which arms create receipts, push promises, append actions, name a
promise index, read deps, consume a data id, and return `i32`.  A transcription slip in either
list breaks the build.

### 1.3 What is proved about a row (`Rows.lean`, all theorems)

| lemma | statement |
|---|---|
| `rcpt_row` | `rcpt = prevR + addR` on an active row |
| `prm_row` | `prm = prevP + addP` |
| `rcpt_chain` | `next.prevR = rcpt` (consecutive active rows) |
| `prm_chain` | `next.prevP = prm` |
| `start_zero` | the first row's `prevR = prevP = 0` |
| `pad_pad` | padding follows padding |
| `tgt_gt` | `tgt + gTgt + 1 = rcpt` (field form) |
| `tgt_lt` | **`tgt < rcpt`** as a `Nat`, given the `PBR` 16-bit bound |
| `dep_sum` / `dep_le` | **`dep ≤ 128`** (`maxInputDataDependencies`) |
| `tgt_off` / `dep_off` | the index/gap is `0` when the flag is off |
| `data_of` / `data_on` | `addD = dadd` (static) or `addD = dep` (the `then` family) |
| `act_bit` / `st_bit` | the two state-side bits |

Axioms of every one: `⊆ {propext, Classical.choice, Quot.sound}`.  No `sorry`, no `native_decay`,
no `implemented_by` anywhere in the lane (checked by grep).

### 1.4 The theorem that *means* something (`Statement.lean`)

`prevR_counter_is_count`:

```
HoldsP/TableLocal at PBC, n active rows  ⇒
  prevR(row n) = #{k < n | addR(row k) = 1}
```

i.e. **the receipt counter is the number of receipt-creating calls so far** — a count of `PBK`
bits, not a witnessed integer.  Composed with `Rows.rcpt_row` (`rcpt n = prevR n + addR n`) this
is what makes "the returned index is `< #receipts`" a statement about a count.  The same induction
gives the promise counter (`prm`).  This is the entire "counter" obligation of DESIGN.md §3.1.

The composition is `Bookkeeping.counts_additive` + `counts_additive_card` (pure list algebra) fed
by `Rows`' three counter lemmas.  Axioms: `{propext, Classical.choice, Quot.sound}`.

### 1.5 What is **stated, not proved** (named `Prop`s, not lemmas that look proved)

| `Prop` | where | what it says | why it is not proved here |
|---|---|---|---|
| `HostCallTrace` | `Bookkeeping.lean` | the `PBC` rows, in `ts` order, are `RunHost`'s `promise_*` calls with `promiseReceiptH`'s `tgt` and `thenDataIdsH`'s `addD` | the induction's state (`St.promises`, `St.actions`, `St.dataCount`) belongs to the Wasm proof; the step is a `RunHost` lemma |
| `TgtIsReceipt` | `Bookkeeping.lean` | `tgt < #receipts at that point` | the `PBC` half is `tgt_lt`; the "at that point" is the counter, hence the `HostCallTrace` order |
| `ActionBytesAreHostBytes` | `Wire.lean` | `PBB`'s request bytes are the Wasm side's memory bytes for the call | the `HOSTB → MEMIO` binding `HostChip.lean` leaves open for **every** host family |
| `ActionEncodingIsBorsh` | `Wire.lean` | `PBB`'s response bytes are `ActionR.encode` at the action's offset | this is the receipt-*contents* claim, which §3 prices and this lane does not make |

These are the honest residue.  Note what is *not* in the list: everything about counters, indices,
kinds, dependency bounds and data-id counts is a theorem.

---

## 2. The `promise_*` → `HOSTQ`/`HOSTR`/`HOSTB` link (`Wire.lean`)

Reuses the existing wire.  No second wire, no new bus for the traffic.

* `qRecv` — `PBC` **receives** `[ts, hid, S, np] ‖ (aLo j, aHi j)_{j<9}` on `HOSTQ` (208): 22
  fields, `qRecv_msg_len` (`rfl`).  The argument window is the row's columns, so the request is a
  function of the row.
* `rSend` — `PBC` **sends** `[ts, st, rLo, rHi, gLo, gHi, ar, 0]` on `HOSTR` (209): 8 fields,
  `rSend_msg_len` (`rfl`).  `ar` is the class's, the rest the row's.
* `tableW = PBC ++ [qRecv, rSend]` — same rows, same 51 constraints, two more interactions.
  `tableW_constraints : tableW.constraints = constraints` (`rfl`) proves adding the wire cannot
  change the bookkeeping.
* `wire_buses_distinct` — `PBK`(211)/`PBR`(212) are disjoint from `HOSTQ`(208)/`HOSTR`(209), so
  adding the wire cannot mask a class/range error.
* `PBB` — the state side of `HOSTB`: the `HostB` table's columns and group discipline, with the
  **direction roles swapped** (request bytes received, response bytes sent).  9 columns, 11
  constraints, 4 interactions (`HOSTB` twice, the `BYTE` value lookup, the `PBR` gap).

### 2.1 A real interface bug this found

`PQ/Join/Statement.lean`'s `hostQ`/`hostB` were written before the HOST chip was widened
(`pq-host-promise` DESIGN §1.3).  They are **stale**:

| message | `Statement.lean` | HOST chip | wide |
|---|---|---|---|
| `HOSTQ` | 8 fields (`hostQ`) | 22 (`Host.qMsg`) | `hostQ22`, 22 |
| `HOSTB` | 4 fields (`hostB`) | 5 (`HostB.msg`) | `hostB5`, 5 |
| `HOSTR` | 8 (`hostR`) | 8 | `hostR8`, 8 |

`hostQ_no_bridge`/`hostB_no_bridge` prove an old-width message can **never** equal a new-width
one (different lengths).  So a joined proof that kept the old shapes would *fail to balance*
rather than silently merge two wires — the failure is loud, which is the right failure.

**Fixed 2026-10-21 (lane `pq-actionr`).**  `PQ/Join/Statement.lean` is now migrated to the widened
wire: `hostQ` is 22 fields, `hostR` 8 (with `ar` in field 6), `hostB` 5 (with `hid`).  The old
shapes survive as `Join.hostQOld`/`Join.hostBOld` **only** so `hostQ_no_bridge`/`hostB_no_bridge`
keep their content; they now compare the old shapes against the current ones and are proved by the
same length argument (`hostQ_old_not_current`, `hostB_old_not_current`, unchanged axioms).
`Ids.hostQ22`/`hostB5`/`hostR8` are now *equal* to the join's definitions
(`hostQ22_eq_join`/`hostB5_eq_join`, both `rfl`), so the two spellings can never fork again.

---

## 3. The `ActionR` encoder verdict — **the dominant cost is real, but the plan's number is wrong**

`Cost.lean`.  All numbers are theorems, not estimates.

### 3.1 The exact byte length (theorem)

`receipt_len` (for a `CR()` receipt with one `FunctionCall` action, no outputs/inputs):

```
65 + |signer| + |pk| + |method| + |args|
```

`receipt_len_ed25519` specialises to `98 + |signer| + |method| + |args|`; `receipt_len_secp256k1`
to `130 + …`.  Axioms `{propext, Quot.sound}` — only `leN_length` and list lengths.  DESIGN.md
never pinned this; now a change to `ActionR.encode` that moved the length breaks the build.

### 3.2 The per-byte cost (kernel arithmetic)

At the D3α limits (`|method| ≤ 256 = Lim.maxMethodName`, `|args| ≤ 4 MiB = Lim.maxArgs`,
`|signer| = 64`, ED25519): `Lmax = 4,194,722` bytes.

| mechanism | rows | cells |
|---|---|---|
| byte-exact encoder rows at 64 columns (`w_a = 64`) | 4,194,722 | 268,462,208 |
| `sha_t` of those bytes (`1 + 17·⌈(L+9)/64⌉` rows × 544) | **1,114,232** | 606,142,208 |
| **total** | | **874,604,416** |
| `HOSTB` byte link only (10 columns, for comparison) | 4,194,722 | 41,947,220 |

So byte-exactness costs **≈ 21× the byte-link alone**, and **69 % of it is the hash**, not the
encoder.  `sha_rows_max = 1,114,232` and `sha_cells_max` are `decide +kernel` facts;
`two_max_receipts_over_cap` shows **two** 4 MiB-argument receipts exceed a `2^21`-row SHA table
(`2 · 1,114,232 = 2,228,464`): the per-byte path does not compose past a couple of maximum-size
receipts, which is exactly the DESIGN.md "2–3 lane-weeks of segmentation" line, now measured.

For a realistic call (8-byte method, 64-byte args, 64-byte signer): `Ltyp = 234`, 69 SHA rows,
**52,512 cells** — 22× the byte link, 71 % of it the hash.

### 3.3 Can the encoder be avoided by a cached commitment?

**Partly — and this is the finding that changes the plan.**  (*The cell counts below are
theorems; the argument about which mechanisms survive a cached-bytes design is architectural
reasoning about `rcptV3`/`srcpV3`, labelled as such.*)

The stack already has the pattern the question points at: `CODE`, `DATA` and `TAPE` are *cached*
traces whose content V_d recomputes from public data, so the AIR never renders the bytes, only
consumes them.  If receipts are treated the same way — the receipt bytes are a cached
`ACTIONBYTES` table bound by a commitment, and the proof consumes `(ts, pos, byte)` from it —
then:

* the **encoder disappears** (no `RECTYPE`, no per-byte pinning): the saved cost is the
  `268,462,208` cells of the encoder row at the limit (**31 %** of the total);
* the **hash does not disappear**.  `receiptIdFrom = sha256(parent ‖ h ‖ k)` and
  `encodeReceipts`' `RC(j)` are hashed *in-AIR* by `rcptV3`/`srcpV3` today; a cached table does
  not remove the SHA-256 instance, because `RIDS`/`SRC` verify the **hash**, not the bytes.  So
  the 606M SHA cells stay.

**Reasoning (not a theorem):** the SHA instance cannot move out of the AIR by caching, because
`rid = sha256(parent ‖ h ‖ k)` and `RC(j)`'s digest are what `RIDS`/`SRC` verify; a cached table
supplies *inputs* to the hash, not the hash.  So the correction to DESIGN.md is: the encoder is
**31 %**, the SHA is **69 %**, of the byte-exact cost.  DESIGN.md called the encoder "the dominant cost" and priced it 4–6 weeks with
`RIDS`/`SRC`/`RCL` separately at 3–4; in fact **the two are inseparable**: the receipt-id set is
only sound against the *hashed bytes*, so a cached-bytes design still needs the SHA instance and
the `RIDS` multiset.  The realistic split is:

* cached `ACTIONBYTES` + `RIDS`/`RCL` (no encoder): still **the SHA cost**, ~3–4 weeks;
* a real encoder (`RECTYPE`): **+** the 31 % above, ~2–3 more weeks, and it is what lets the
  proof *check* the bytes rather than trust a commitment.

So the encoder is real but it is **not** the dominant cost — the SHA instance is, and the SHA
instance is **unavoidable for any design that binds `rid` to the receipt**, cached bytes or not.
That is a firmer statement than DESIGN.md's, and it is what should drive the sequencing: build
`RIDS`/`RCL` + the cached-bytes link first (it carries the SHA and the multiset, ~70 % of the
cost), then decide whether the extra 31 % for a real encoder is worth it.

**The one thing the cached design must not lose:** `SIZE` and the congestion accounting read
`r.encode.length` (`Fees.receiptSize`).  A cached table must therefore still commit the exact
length — which `Cost.receipt_len` now gives as a *formula*, so the cached design can pin `L`
from the same arithmetic rather than from a witness.  That is a genuine saving the design did not
have before this lane.

---

## 4. Corrected prices

| block | DESIGN.md | **measured / corrected** | basis |
|---|---|---|---|
| HOST chip widening | done | done | — |
| bookkeeping table | 1.5–2.5 k lines, 2–3 wk | **~1.5 k lines built, column/constraint count 2×/5× the estimate; 1 wk** | 49 cols/51 cons/29 inters, `pbc_wf` |
| counter + index + bound lemmas | (inside the above) | **done; `prevR_counter_is_count` + 12 row lemmas, `{propext, choice, quot}`** | `Rows`, `Statement` |
| `HOSTQ`/`HOSTR` wire | (inside the above) | **done, reuse only; +2 interactions** | `Wire`, `tableW` |
| `HOSTB` byte link | (inside the above) | **table built (`PBB`); byte provenance stated** | `Wire`, `PBB` |
| borsh `ActionR` encoder | 4–6 wk, **"the dominant cost"** | **31 % of the byte-exact cost (268 M of 875 M cells at the limit); 69 % is SHA** | `Cost.cells_max`, `sha_cells_max` |
| `RIDS`/`SRC`/`RCL` + SHA of receipts | 3–4 wk | **the real dominant cost, and unavoidable even with cached bytes** | §3.3 |
| i32 result tag (`Host.rtag`) | 0.5 wk | unchanged (designed, not built) | — |
| **total to a receipt the state layer executes** | **7–12 wk** | **≈ 6–10 wk**, with a different split: SHA/RIDS first (3–4), encoder optional (+2–3) | §3 |

The two substantive corrections:

1. **the encoder is not the dominant cost** (31 %, not ~50 %+), and
2. **it is separable** from the SHA/`RIDS` work, so the plan can de-risk by shipping the cached
   design (which carries 69 % of the cost) before committing to the encoder.

Both were unreachable without the exact length, which is now a theorem.

---

## 5. The borsh `ActionR` encoder (lane `pq-actionr`, 2026-10-21)

`zk-formal/ZkFormal/PQ/Receipt/Encoder.lean`.  The encoder is now **built for the borsh shape**, not
just priced.  It starts at `promise_batch_action_transfer` (np=2: `[3] ‖ u128 amount`) and
generalises to `promise_batch_action_delete_account` (np=3: one `borshBytes`) and
`promise_batch_action_function_call` (np=7: two `borshBytes` + `u64` + `u128`).

**The reference encodings, checked against the spec's *decoder*.**  `trRaw`/`daRaw`/`caRaw`/`fcRaw`
are the spec's own byte construction; `decodesAs` runs `D2.pBaseAct` on them.  Kernel `decide`
facts (`decodes_transfer_{zero,one,fee,near,u64}`, `decodes_delete_{bob,dotted}`, `decodes_create`,
`decodes_fcall`, `decodes_fcall_empty`) show the bytes decode back to exactly that action, with the
raw bytes round-tripping; `decodes_discriminates` shows the check has teeth.  Axioms `[propext]`.

**The rows' bytes equal the reference bytes.**  `encAction` is the AIR-shaped byte list (a tag, then
a list of typed fields `str`/`u64`/`u128`); `encAction_transfer`/`_delete`/`_create`/`_fcall` prove
it equals the reference list position for position.  `encAction_transfer_body` gives the
position-indexed form a generator fills rows from.

**The framing lemmas — the point of the exercise.**

| lemma | statement |
|---|---|
| `encAction_length` | `|action| = 1 + Σ field lengths`, with `4+\|str\|` / `8` / `16` per field |
| `prefixBytes_value` | `leNat (u32 n) = n` — the prefix *is* the count (spec's own `leNat`) |
| `prefixBytes_getD` | byte `k` of the prefix is `n / 256^k % 256` |
| `tr_frame_len` / `da_frame_len` / `fc_frame_len` | `1 + 4·nStr + strLen + tail` = the reference length, per shape |
| `receipt_tr_len{,_ed25519,_secp256k1}`, `receipt_da_len` | the receipt-level length, per shape |

**The AIR (`PBE`).**  15 columns, 23 constraints (all degree ≤ 3), 4 interactions, `maxLog = 22`;
`pbe_wf` kernel-checks admissibility, `pbe_degree` / `pbe_degree_le` the degree bound.  One row per
emitted byte; body bytes come from a committed array on bus 214 (the §3.3 cached-source design) and
`u32` prefix bytes from a 4-row table on bus 213.  The row lemmas:

| lemma | statement |
|---|---|
| `pbe_len_framing_general` | `len = 1 + 4·nStr + strLen + tail` (the framing identity, field form) |
| `pbe_len_framing_tr` | the `TR` instance: `len = 17` |
| `pbe_len_framing_da` | the `DA` instance: `len = strLen + 5` |
| `pbe_group_len_is_row_count` | **the declared `len` is the number of emitting rows** — the direction a prover cannot fake |
| `pbe_tag` / `pbe_tag_pos` | the tag byte is the action's `knd`, and it is at position `0` |
| `pbe_phase` / `pbe_body_pos` | every active row is tag or body, and a body row is at `5 + d` |
| `pbe_pos_offset` / `pbe_len_const` | `pos` is the offset in the group; `len` is group-constant |
| `pbe_msg_len` / `pbe_buses` | the `HOSTB` message is 5 fields and the table uses only the existing buses |

Axioms of every one: `⊆ {propext, Classical.choice, Quot.sound}`; no `sorry`, no `native_decide`,
no `implemented_by`.

**Wire.**  `PBE` sends each byte on the existing `HOSTB` (210), `dir = 1`, 5-field message — the
same shape `Wire.PBB` and `HostB.msg` use.  No second byte wire.

**Cost, corrected.**  At the D3α maximum receipt the encoder is 268 M cells (31 %), so a single-row-
per-byte encoder at 64 columns stays the right shape; the extra 15-column framing table is `15 ·
L` cells, i.e. **~23 % of the 64-column encoder's rows** — negligible next to the SHA (69 %).  The
`TR`/`DA`/`FC` lengths are now theorems (`receipt_tr_len` accounts for `49 + |signer| + |pk|`
before `pk_encode_len`), so a change to `ActionR.encode` that moved a length breaks the build.

**What remains on the encoder.**  The `FC` shape's *body* rows are the same mechanism as `TR`/`DA`
(committed source), but the two prefixes need two `PBPREFIX` groups per call, so a fully general
`PBE` needs a per-`(call, field)` prefix group key — the table has one `(ts, hid, strLen, pos)`
tuple and would need the field index added.  `promise_create`'s nested `Vec<Action>` is the same
`u32 |actions|` prefix with `nStr = 0, tail = Σ action lengths`; the constraint form is already
general (`eFrameCons` takes `tail` as a class constant), so it is a class-table addition, not a new
table.  Pinning a source byte to linear memory stays `ActionBytesAreHostBytes` (`Wire.lean`).

---

## 6. What is not done (and why that is the honest boundary)

* **The `FC`/`promise_create` encoder instances** — §5 states exactly what is missing (the
  per-field prefix group key and the nested-`Vec` class row); the `TR`/`DA`/`create` shapes and the
  framing lemmas that generalise are built.
* **`RIDS`/`SRC`/`RCL` + `newReceipts` fold** — not attempted; §3.3 now says this is where the
  cost is, and it is the next lane.
* **The `RunHost` call-log induction** (`HostCallTrace`) — stated, not proved; it is a Wasm-side
  theorem about `pushPromiseH`/`pushAction`/`thenDataIdsH`.
* ~~**`Statement.lean`'s stale HOSTQ/HOSTB**~~ — **fixed** (§2.1): the join speaks the wide wire.
* **`Holds` for the full joined AIR** — `pbc_wf` is the table's own admissibility; there is no
  `nearAirV3`-level assembly for `PBC` because the promise family has no state-side instance yet.

---

## 7. Reproduce

```
# Lean (the whole library, including this lane)
HEAVY_MEM=24G taskset -c 14-15,28-29 /data/illia/nearproof-deps/bin/heavy sh -c \
  'cd zk-formal && lake build'
# → Build completed successfully (3057 jobs).

# the lane's own modules
HEAVY_MEM=24G taskset -c 14-15,28-29 /data/illia/nearproof-deps/bin/heavy sh -c \
  'cd zk-formal && lake build ZkFormal.PQ.Receipt.Statement ZkFormal.PQ.Receipt.Cost'

# the pinned-oracle check (must pass)
make pin-check
```

Key output (from `/tmp/opencode/Final.lean`):

```
(table.width, constraints, interactions, maxLog, maxDegree) = (49, 51, 29, 16, 4)
(Lmax, shaRows Lmax, receiptCells 64 Lmax)                  = (4194722, 1114232, 874604416)
(Ltyp, shaRows Ltyp, receiptCells 64 Ltyp)                  = (234, 69, 52512)
pbc_wf          : axioms [propext]
rcpt_row        : axioms [propext, Classical.choice, Quot.sound]
prevR_counter_is_count : axioms [propext, Classical.choice, Quot.sound]
promiseClasses_policy  : no axioms
receipt_len_ed25519    : axioms [propext, Quot.sound]
```

Commit: see `git log -1` on this branch.
