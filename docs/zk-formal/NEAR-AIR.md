# NEAR AIR (`nearAir`): table layout, width and height accounting

Lane L6, DESIGN.md §5.2–5.3. Status: layout frozen at v1 (this document);
Lean definitions under `zk-formal/ZkFormal/Near/`. The Lean value is
normative where it differs from this text; `ZkFormal.Near.Budget` computes
the width accounting below from the Lean value and checks it by kernel
evaluation.

## 0. Summary

| | Plonky3 example (`examples/stark-plonky3`) | `nearAir` v1 |
|---|---|---|
| tables | 9 (one row per item, LogUp) | 7 (byte-serial streams, grand product) |
| main columns | 10,817 | 1,070 (incl. L5's 544-column SHA table) |
| interactions | 3,619 per row-set | 66 |
| `W_eq` (main + 8·aux + 8·quot, §5) | ≈ 14,600 | **1,766 (budget 3,000), kernel-checked** (`Budget.weq_le`) |
| largest table | `node`, 2^12 rows × 1,381 cols | `node`/`sha`, ≤ 2^22 rows × ≤ 544 cols |

The re-layout rests on one decision: **every table that emits message bytes
is a byte-serial stream** — one byte position per row, with a small state
machine selecting which field the byte belongs to — instead of one wide row
per item. Each byte costs one interaction *per table* instead of one per
byte per row, so the interaction count (which dominates the aux width under a
grand-product argument) drops from thousands to about 60. Multi-byte values
that a row must see at once (a 32-byte digest for a lookup) live in a
**shift register** (32 columns) that is loaded by one lookup at the start of
a window and shifted one byte per row. Arithmetic on little-endian u128
values is done byte-serially (LSB first) with carries carried to the next row.

## 1. Conventions

* Field `Fp` = BabyBear (`p = 15·2^27 + 1`, L1). All bytes the AIR emits on
  the bytes bus are range-checked by the SHA table (it reads them from bit
  columns); every other byte or small integer the soundness argument needs
  as a natural is range-checked by explicit bit columns. **No lookup tables
  with free multiplicities are used** (a `k`-bit multiplicity costs `2(k−1)`
  extension columns, L4 `Table.auxCount`), and every multiplicity is a single
  bit.
* **Shared lookups by chaining.** Where several consumers need the same fact
  (a trie edge used by several account walks), the provider sends `(e, 0)` and
  receives `(e, m)`; each consumer receives `(e, u)` and sends `(e, u + 1)`.
  Soundness needs no counting: if no provider offers `e`, the `e`-messages of
  the consumers balance only if `Σ (u+1) = Σ u`, i.e. `#consumers ≡ 0 (mod p)`,
  impossible for `0 < #consumers < p` (`Near.Bus.chain_sound`).
* **Message ids.** A SHA message is identified by one field element
  `Id = kind + 16·idx` (`idx < 2^22`, so ids are distinct field elements):

  | kind | message | idx | length |
  |---|---|---|---|
  | 1 `RC` | `u64 shard ‖ u32 n ‖ Σ Receipt.encode` | 0 | `12 + Σ size_r` |
  | 2 `RF` | `u32 nref ‖ Σ Receipt.encode refund` | 0 | `4 + Σ size'_r` |
  | 3 `PEO` | `PartialExecutionOutcome` of receipt `r` | `r` | `46 + 32·hr + L_v` |
  | 4 `LEAF` | `u32 2 ‖ id ‖ H(PEO_r)` | `r` | 68 |
  | 5 `RID` | `id ‖ u64 height ‖ u64 0` (refund id preimage) | `r` | 48 |
  | 6 `MRK` | outcome-merkle inner node `left ‖ right` | merkle row | 64 |
  | 7 `NPRE` / 8 `NPOST` | trie node `N`, pre/post serialization | `N` | node length |
  | 9 `VPRE` / 10 `VPOST` | AccountV1 value of touched slot `k`, pre/post | `k` | 72 |

* **Every digest consumer pins the length.** L5's contract
  (`Sha.sha_digest_contract`) gives, for a provided `(Id, len, d)`, a message
  `m` with `|m| = len`, `d = sha256 m`, and every `(Id, i, m[i])` received.
  Since the NEAR side emits for `Id` exactly the positions `0 … |enc|−1` of
  its intended encoding `enc`, bus balance gives `m[i] = enc[i]` for
  `i < |m|`; the consumer's `len` must equal `|enc|` to conclude `m = enc`
  (otherwise e.g. `(Id, 0, sha256 [])` could be offered). Lengths are therefore
  always columns tied to the producer (node length via the `PARENT` bus;
  constants 72, 68, 64, 48; running offsets for `RC`, `RF`, `PEO`).
* **Public inputs** `publicOf c = c.encode` as field elements (309 entries for
  `chainId = "mainnet"`). The AIR reads them only at static indices
  (`ZkFormal.Near.Pub`): format/statement prefix 0–65, `u32 7 ‖ "mainnet"`
  66–76, `shard` 77, `height` 85, `bgp` 93, `gasLimit` 109, `pre` 117, `n`
  149, `rc` 153, `post` 185, `out` 217, `nref` 249, `rfc` 253, `gas` 285,
  `tok` 293. Values needed on many rows (`bgp`, `height`, header bytes) are
  loaded into rotating registers on the first row of the table that uses
  them.

## 2. Buses

| # | bus | message | producer(s) → consumer(s) | kind |
|---|---|---|---|---|
| 0 | `BYTES` | `(Id, pos, byte)` | node, rcpt, acct, mrk → sha | perm |
| 1 | `DIGEST` | `(Id, len, d[32])` | sha → node, rcpt, mrk | perm (each digest consumed once, `Dmult` one bit) |
| 2 | `PARENT` | `(N, depth, len)` | node child window → node first row | perm |
| 3 | `VSLOT` | `(k)` | acct → node (touched value window) | perm |
| 4 | `EDGE` | `(N, i, sym, N', i', u)` | node (chained provider) ↔ walk | chain |
| 5 | `KEYNIB` | `(r, t, sym, last)` | rcpt → walk | perm |
| 6 | `FINAL` | `(r, k)` | walk → rcpt | perm |
| 7 | `MEM` | `(k, t, i, amt_i, locked_i, stor_i)` | acct/rcpt ↔ rcpt/acct | perm (offline memory) |
| 8 | `RIDS` | `(r, i, id_i)` | rcpt → sort | perm |
| 9 | `MPOS` | `(level, index, Id, len)` | rcpt, mrk → mrk | perm |

`sym < 16` is a key nibble, `16 = END` (key exhausted, value slot), `18 = START`
(the walk's first step, root → its walk target). Walk targets `res` skip
empty-key extensions (an empty-key extension forwards its child's target; the
last nibble of an extension's key and a branch's child edge go directly to the
child's target), so AIR walks take no epsilon steps: at most `1 + 2 + 128 + 1`
rows per receipt even for pathological witnesses with long chains of empty
extensions. `17 = EPS` exists only in the spec-level `Walk` (`Spec/Trie.lean`).

## 3. Tables

Width = main columns; `I` = interactions (sends + receives); `maxLog` =
`log₂` height cap; `deg` = constraint degree (selectors count 1).

### 3.0 `sha` — owned by L5 (`ZkFormal.Sha.Table`)

544 columns, 16 receives on `BYTES` + 1 send on `DIGEST`, deg 4, maxLog 22.
One start row per message plus 17 rows per block.

### 3.1 `node` — trie node byte stream (L6a)

One row per byte of the serialization of a revealed trie node (pre and post
state simultaneously); nodes are contiguous row segments; node 0 is the root.
A final `SUM` row checks the witness-size bound.

| group | columns | notes |
|---|---|---|
| control | `act, nf (node first), nid, pos, len, depth` (6) | `pos` 0…len−1; `len`, `depth`, `nid` node-constant |
| bytes | `b` (pre), `pb` (post) (2) | `pb = b` outside revealed windows |
| node type | `tl, tb1, tb2, te` (4) | one-hot, node-constant |
| field state | `TAG, HPL, HPF, KEY, VLEN, VH, BM, CH, MEM` (9) | one-hot; `idx` (1) counts within the field |
| key | `hplen, odd, s, hi, lo, hiBits[4], loBits[4]` (13) | `b = 16·hi + lo` on `KEY` rows; `s` = key nibble count |
| bitmap | `bm[16]`, child slot one-hot `j[16]` (32) | node-constant bitmap; `j` window-constant, strictly increasing over windows, only set bits |
| windows | `reg[32]`, `preg[32]` (64) | shift registers; loaded at window start by the `DIGEST` lookups; `b = reg[0]`, `pb = preg[0]` on revealed windows |
| refs | `rv, cid, clen, tv` (4) | revealed child id/length; touched value |
| edges | `m_a, m_b` (2) | chained-provider use counts |
| size | `S` (1); `SUM` row reuses `reg` as 22 slack bits | running revealed-byte count |

≈ 140 columns. Interactions (11): `BYTES` pre/post (sends, gate `act`);
`DIGEST` pre/post (receives, at window start: revealed child
`(NPRE/NPOST(cid), clen, reg/preg)`, touched value `(VPRE/VPOST(nid), 72, …)`,
root `nf ∧ nid = 0`: `(NPRE/NPOST(0), len, pub pre/post root)`); `PARENT` send
(child window start: `(cid, depth+1, clen)`) and receive (`nf ∧ nid ≠ 0`:
`(nid, depth, len)`); `VSLOT` receive (`tv`); `EDGE` provider A and B
(send `(e,0)`, receive `(e,m)`): key-byte rows provide the two nibble edges
`(N,i) –hi→ (N,i+1) –lo→ (N,i+2)`, the `HPF` row of an odd key provides
`x0`, branch child windows provide `(N,0) –j→ (cid,0)`, extension child
windows provide `(N,s) –EPS→ (cid,0)`, touched value windows provide
`(N, s or 0) –END→ (N, 0)`. deg ≤ 4, maxLog 22.

Soundness content (`Near.Node.extract`): the node segments are a list of
`NodeRec` (§4) whose pre/post messages are `ser` of the record with the
looked-up windows; `PARENT` balance + `depth` (a cycle would need
`L ≡ 0 mod p`) make the revealed nodes a tree rooted at node 0 in which every
node has exactly one parent slot; `VSLOT` makes touched slots and accounts
one-to-one.

### 3.2 `walk` — account-key walks (L6a)

One row per walk step of receipt `r`: a nibble step (receives
`KEYNIB (r,t,sym,last)`, uses edge `(N,i) –sym→ (N',i')`) or an `EPS` step.
Walks start at `(0,0)`; the step consuming `END` (`last = 1`) sends
`FINAL (r, N')`. Columns ≈ 16 (`act, ws, r, t, sym, last, eps, N, i, N', i', u`
+ flags); interactions 4 (`KEYNIB` recv, `EDGE` recv `(e,u)` + send
`(e,u+1)`, `FINAL` send); deg 3; maxLog 16 (≤ 256 walks × (2·65+3 + #EPS)
rows; EPS steps are bounded by the revealed extensions on the path).

### 3.3 `rcpt` — receipt stream (L6b)

One segment per receipt, in batch order, preceded by `CLAIM` rows (claim-level
checks) and followed by nothing; one row per emitted byte. A row has a
one-hot field state, an index within the field, the byte, and up to four
**emission slots** `(Id_e, pos_e, g_e)` (`Id_e`, `pos_e` are columns
constrained by the state; `g_e` gates). Field states and their emissions:

| state | rows | byte | emits into |
|---|---|---|---|
| `PL, P` | 4, `L_p` | borsh predecessor | RC |
| `VL, V` | 4, `L_v` | borsh receiver | RC, PEO; `KEYNIB` (two nibbles per char, `0,0` on `VL`) |
| `RID` | 32 | receipt id | RC, LEAF, RID (if refund), `RIDS` |
| `T0` | 1 | `0` (ReceiptEnum::Action) | RC, RF (if refund; refund-receipt tag) |
| `SL, S` | 4, `L_s` | borsh signer | RC, RF ×2 (if refund) |
| `KT, PK` | 1, 32/64 | key | RC, RF (if refund) |
| `GP` | 16 | gas price, LSB first | RC; PEO (`burnt_i`), RF (`ramt_i`) |
| `TAIL` | 13 | `u32 0 ‖ u32 0 ‖ u32 1 ‖ 3` | RC, RF |
| `DEP` | 16 | deposit, LSB first | RC |
| `XPEO` | 4+32·hr+8+5 | PEO header/refund id/`u64 G`/status | PEO; refund id also RF |
| `XLEAF` | 4+32 | `u32 2`, `H(PEO)` | LEAF |
| `XRID` | 16 | `u64 height ‖ u64 0` | RID |
| `XRF` | 10+16 | `u32 6 ‖ "system"`, zero gas price | RF |

Arithmetic lanes (columns shared between states):
* `GP` rows: `bg_i` (rotating `bgp` register), borrow chain for
  `gp − bgp`, the guessed comparison flag `ge` (checked by the final borrow),
  `p_i = ge·bg_i + (1−ge)·gp_i`, `sur_i = ge·D_i`, delay lines of `p` and
  `sur` (4 each), convolutions `burnt = G·p`, `ramt = G·sur` with 11-bit
  carries, no overflow past byte 15; running `tok` (rotating register, write
  back) with byte bits; `hr = [sur ≠ 0]` by an inverse.
* `DEP` rows: `MEM` read `(k, tprev, i, bef_i, l_i, s_i)` and write
  `(k, r+1, i, aft_i, l_i, s_i)`; `aft = bef + dep` (bits), `aft ≠ 2^128−1`
  (running all-ones flag + inverse), `tot = aft + l < 2^128`, `q = 10^19·s`
  (delay line of 7 storage bytes, carries), `tot ≥ q` or `s ≤ 770`;
  `r − tprev < 2^9` (bits).
* account-id states: character class from the nibble split (`hi`, `lo`, 8
  bits), `lastSep`, length, and the whole-string predicates
  (`≠ "system"`, named: not 64-hex / `0x`+40-hex / `0s`+40-hex) via running
  accumulators and inverses.
* registers: digest window `reg[32]` (refund id, `H(PEO)`), `bgp[16]`,
  `tok[16]`, `height[8]`, header `[12]`; scratch bits `x[48]` shared by
  states.
* running across receipts: `r`, RC offset `o`, RF offset `o2`, refund count.

≈ 250 columns. Interactions (14): 4 `BYTES` sends; `DIGEST` receives:
refund id `(RID(r), 48, reg)`, `H(PEO)` `(PEO(r), len, reg)`, first row
`(RC, len_RC, pub rc)` and `(RF, len_RF, pub rfc)`; `KEYNIB` ×2; `FINAL`
recv; `MEM` recv/send; `RIDS` send; `MPOS` send `(0, r, LEAF(r), 68)`.
deg ≤ 4, maxLog 18 (≤ 256 × ~500 rows + claim rows).

### 3.4 `acct` — touched value slots (L6a)

16 rows per touched slot `k` (lane `i = 0…15`): `amt_pre_i, amt_post_i,
locked_i, stor_i (i<8), ch_{2i}, ch_{2i+1}`; emits `VPRE(k)` bytes at
`i, 16+i, 32+2i, 33+2i, 64+i (i<8)` and `VPOST(k)` likewise with the post
amount; `MEM` write `(k,0,i,…)`, read `(k,tlast,i,…)`; `VSLOT` send on the
first row; AccountV1 check `amt_pre ≠ u128::MAX`. ≈ 20 columns, 13
interactions, deg 3, maxLog 12.

### 3.5 `mrk` — outcome merkle tree (L6b)

First row: the root check (receives `MPOS (J, 0, Id, len)`, looks up
`(Id, len, pub out)`). Then, level by level from the leaves, one 64-row
segment per hashed inner node (`left ‖ right`, windows loaded by `DIGEST`
lookups, positions from `MPOS` receives; provides `MPOS (j, i, MRK(row), 64)`)
or one `PROMOTE` row per odd last node (forwards the `MPOS` entry). Level
sizes from `n` (public) as in nearcore `merklize`. ≈ 50 columns, 5
interactions, deg 3, maxLog 15.

### 3.6 `sort` — distinct receipt ids (L6b)

32 rows per id (LSB first), ids received on `RIDS (r, i, b)`; a delay line of
32 holds the previous id; `id_t = id_{t−1} + diff + 1` byte-serially (`diff`
bytes as bits, carry bit, no final carry) ⇒ strictly increasing ⇒ distinct.
≈ 45 columns, 1 interaction, deg 3, maxLog 13.

## 4. The relational intermediate spec

`ZkFormal.Near.Spec` (no field elements; `Nat`/`Bytes` only):

* `NodeRec` — one revealed node: `leaf key v mem | ext key kid mem |
  branch v kids mem` with value slots `ref len h | touched` and child slots
  `none | hash h | node cid`.
* `treeOf ns vals n : PTrie` — the partial trie of node `n`, where `vals k` is
  the current value of touched slot `k` (the arena view of reexec-npai,
  `Trie/Arena.lean`, specialized to records).
* `WalkTo ns key k` — the edge walk from `(0,0)` along `key ++ [END]` ends at
  touched slot `k`.
* `Good c e` — the relational spec of a claim: the trie records form a tree
  hashing to `preStateRoot`; every receipt walks to its slot; the memory
  chain per slot; per-receipt arithmetic facts; the outcome / refund /
  receipt encodings and digests; the claim-level facts.

Lemmas (proof lanes): `good_sound : Good c e → NearRelation c (witnessOf e)`
(L6a/L6b: tree hashing, `get`/`set` along walks = slot reads/writes, the
memory chain = sequential `set`s, arithmetic = `applyReceipt`);
`good_complete : NearRelation c w → Good c (extOf c w)` (pruning the witness
trie to the touched paths keeps the hash and does not increase
`revealedBytes`).

## 5. Width accounting (checked by `ZkFormal.Near.Budget`)

Per table, with L4's protocol layout (`Stark/Protocol.lean`,
`FORMATS.md` §3) and `g = auxGroup`:

```
aux_t   = Σ_{i, k_i ≥ 2} 2(k_i − 1) + ⌈sends_t / g⌉ + ⌈recvs_t / g⌉     (K columns)
quot_t  = Table.degree t g − 1                                          (K columns)
W_eq    = Σ_t (width_t + 8·aux_t + 8·quot_t)
```

Proof bytes per query ≈ `4·W_eq` + Merkle paths, so `W_eq` is the quantity
DESIGN.md §8 budgets (`≤ 3000`). Estimates (v1 layout; exact numbers are
`#eval ZkFormal.Near.Budget.report`):

Exact numbers of the v1 Lean AIR (`#eval Budget.report 1`; table degree 4
everywhere, so 3 quotient chunks per table):

| table | width | interactions | aux (K) | `W_eq` (g=1) | maxLog |
|---|---:|---:|---:|---:|---:|
| sha (L5) | 544 | 17 | 17 | 704 | 22 |
| node | 163 | 13 | 13 | 291 | 22 |
| walk | 12 | 4 | 4 | 68 | 16 |
| rcpt | 228 | 13 | 13 | 356 | 18 |
| acct | 16 | 13 | 13 | 144 | 12 |
| mrk | 58 | 5 | 5 | 122 | 15 |
| sort | 49 | 1 | 1 | 81 | 13 |
| **total** | 1,070 | 66 | | **1,766** | |

`ZkFormal.Near.Budget.weq_le : weq nearAir 1 ≤ 3000` and
`nearAir_wf : Air.wf nearAir 16 = true` are checked by `decide +kernel`
(13 s, leaf module `Near/BudgetCheck.lean`). No protocol change is required. (`g = 2` saves ≈ 170; L4 may pick
it later — the AIR is valid for any `g` with degree ≤ 16.)

L4 `Air.wf` side conditions: all multiplicities are one bit, so
`multBound = Σ_t 2^maxLog_t · I_t ≈ 2^27.4` and
`fpBound ≈ 2^27.4 · 35 ≈ 2^32.5`, both `≤ busBudget = 2^36`.

## 6. Height accounting (the `honestTrace_fits` argument)

From `NearRelation c w`: `n ≤ 256`, `revealedBytes ≤ 3,000,000`, account ids
≤ 64 bytes. The honest trace prunes the witness trie to the nodes on the
touched paths (hash unchanged, `revealedBytes` not increased).

| table | rows (worst case) | cap |
|---|---|---|
| node | `Σ ser_len(node) + 1 ≤ 3,000,000 − 72·#touched + 1` | 2^22 = 4,194,304 |
| sha | `Σ_msgs (1 + 17·⌈(len+9)/64⌉)`: node pre+post ≤ 1.25 rows/byte ⇒ ≤ 3.75 M; receipts/outcomes/values ≤ 0.06 M | 2^22 |
| rcpt | `≤ 16 + 256 · 512` | 2^18 |
| walk | `≤ 256 · (133 + #ext on path)`; `#ext ≤ 3 M/46` crude, ≤ 2^16 using the per-path bound | 2^16 |
| acct | `16 · #touched ≤ 4096` | 2^12 |
| mrk | `1 + 64 · 255 + 8` | 2^15 |
| sort | `32 · 256` | 2^13 |

The binding case is `sha`: a node of serialized length 56 needs two blocks
for 56 bytes in each of the pre and post messages (`2·(1 + 34)/56 = 1.25`
rows per byte); `3 M · 1.25 + 0.06 M < 2^22` with a 10 % margin.
(Walk rows: a path has at most 133 nibble/END steps; EPS steps are bounded by
the number of extensions on the path, each ≥ 46 revealed bytes, so
`≤ 256·133 + 3,000,000/46 < 2^17`; maxLog 17 if the per-path bound is not
proved.)

## 7. Lean module map

| module | content | lane |
|---|---|---|
| `Near/Ids.lean` | kinds, buses, public offsets | L6 |
| `Near/Spec/*.lean` | `NodeRec`, `treeOf`, `WalkTo`, `Good`, `witnessOf`, `extOf` | L6 |
| `Near/Tables/{Node,Walk,Rcpt,Acct,Mrk,Sort}.lean` | `Air.Table` values | L6a/L6b |
| `Near/Air.lean` | `nearAir`, `publicOf` | L6 |
| `Near/Budget.lean` | width/height report, `weq_le` (kernel) | L6 |
| `Near/Statements.lean` | sublemma statements | L6 |
| `Near/Compose.lean` | `nearAir_sound`, `nearAir_complete`, `honestTrace_fits` from the statements | L6 |
