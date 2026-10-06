# STATUS — lane `v3-trie` (v3 trie tables: `nodeV3`, `walkV3`, `uniqV3`)

Branch `lane/v3-trie` (off `lane/v3-air`). Design: `V3-D0-DESIGN.md` §3.1–3.3, §3.7, §6,
§10, §11 (lead round 2: A6 rejected, **weak `uniq`**, **tree-shaped records**). Spec-side
predecessor: `STATUS-V3-STORE.md`. Lean: `zk-formal/ZkFormal/NearV3/`. No v1 table, proof
or definition is modified.

Rules: no `sorry` / `axiom` / `native_decide`; axioms ⊆ {propext, Classical.choice,
Quot.sound} (checked with `#print axioms` for every theorem named here).

## Milestones

| # | milestone | state |
|---|---|---|
| M1 | store spec for tree records + weak uniq (no A6) | **done** (§1) |
| M2 | `uniqV3`: table, view, link (weak uniq ⇒ hash-functional), render | **done** |
| M3 | `walkV3`: table, view, render | **done**; link (walks ⇒ `find`/absent) open |
| M4 | node side split into `nodeV3` / `headV3` / `valV3`: tables, kernel-checked budget; `headV3` view + render; `valV3` view + render; `nodeV3` view **statement** | **done** except as noted |
| M5a | `nodeV3` view proof (v1's `Extract/Node*` adapted: `Extract/Node/*.lean`, 21 modules) | **done**: `node3_view : NodeV3ViewStmt` |
| M5b | `nodeV3` render | **done**: `node_render_local`, `node_render_traffic` (`Render/Node/Local.lean`, `Traffic.lean`; 5df77df2) |
| M6 | `upsV3` (`0x0f` upsert incl. insertion, `memory_usage`), link layer (trie of τ hashes to root, finds/absents, post-root) | **open** |

## 1. M1 — store obligation under the lead's decision (spec side, proved)

### 1.1 Soundness from weak uniqueness (`Spec/Rank.lean`)

* **`RootedDagR ns vs τ root rk`**: `RootedDag` with the id order replaced by any rank
  (`rk n < rk c` for every revealed child `c` of a `τ` record `n`). Tree-shaped AIR records
  give the rank `depth`. `rootedDag_R` embeds the id-order case.
* The unfolding (fuel `ns.length`) is fuel-stable under any rank via the measure
  `mu n = #{τ records ranked above n}` (`mu_child`, `mu_lt_length`); `treeOf3_fuelR`,
  `fullTree_unfoldR`, `dag_inductionR`, `fullTree_wfR`, `fullTree_storedR`.
* **`storeBuildR`** — `storeBuild` for ranked records: from `HashFunctional (storeOf ns vs τ)`
  (= "equal digest ⇒ equal bytes", exactly what `buildFor` needs), `RootedDagR` and
  `PathsRevealed`, NearSpecV3's `partialTrie (storeOf …) (digest root) keys` refines the
  unfolded records, has the root digest, and answers every read key like them.
* **`fdepth_le_rank`, `pathsRevealed_of_rank`** — if every `τ` record has rank `< 400`
  (`trieFuel`), every lookup visits `≤ 400` revealed nodes. So the AIR's per-record
  `depth ≤ 399` check (9 bits on the node's first row) replaces the store lane's proposed
  walk depth counter: walks need no `Δ` on `EDGE` and no counter.
* **Weak uniqueness**: `WeakUniq key bytes l` (consecutive entries: `key` strictly
  increases, or is equal with equal bytes). `weakUniq_functional`: any two entries with
  equal keys have equal bytes (the step relation is transitive). **`hashFunctional_of_weakUniq`**:
  a store whose entries are the byte column of a weakly unique list keyed by (a function of)
  the digest is `HashFunctional`.

### 1.2 Completeness without A6 (`Spec/TreeRecs.lean`)

**`treeRecs_spec`** (no hypothesis beyond the relation's own: root 32 bytes, keys nonempty,
every read key determined). For `T = partialTrie ws root keys`, the pre-order occurrence
records `recsT τ 0 0 T`, value records `valsT τ T`, depths `depsT 0 T`:
* form a `RootedDag` (pre-order ids: children have larger ids) whose unfolding **is** `T`;
* their root digest is `root`;
* every store entry is what `storeGet (mkStore ws)` returns for its own digest
  (`EntriesFound`), hence `HashFunctional`, hence weakly unique in any digest order — so the
  honest `uniq` trace exists whatever identical subtrees, SHA cycles in `ws` or node/value
  byte coincidences the witness has;
* `PathsRevealed` for the read keys;
* child depth = parent depth + 1, root depth 0, every depth `< 400` (from `buildFor`'s
  fuel: `exists_fdepth`, `theight_le_of_fdepth`);
* `storeBytes = unfoldedBytes T` (every node and value *occurrence*).

### 1.3 Finding: unfolded-size cap (needed for `FitsV3Stmt` with *any* record layout)

`unfoldedBytes T` can exceed `|base_state|` (≤ 3,000,000): a witness may share one subtree
digest under many branch slots, and `buildFor` reveals one occurrence per path. Example
(collision-free, acyclic, valid under `RelD0`): ~130 "universal" branches whose 16 slots
all hold the next one's digest, then a distinguishing subtree for the read keys; the
store is < 1 MB, but each of the ~9 k read keys has its own occurrence of every universal
branch (≈ 9 k × 130 × 523 B ≈ 600 MB unfolded).

This is **not an artifact of tree-shaped records**: the post-state root after the account
writes requires hashing every changed node *occurrence* on the write paths, and in the
example these are pairwise distinct (each carries a different child hash). So any AIR that
proves the post-root needs ≈ the unfolded size of the write paths in SHA rows. Hence a
D0 cap is required for completeness of heights, e.g.

> **A7 `w.unfolded`** (additive, `RelD0a`): for every partial trie `checkD0` builds,
> `unfoldedBytes T ≤ 3,000,000` (Σ over revealed node occurrences of `|nodeEnc|` plus
> revealed value occurrences).

On real chains `unfoldedBytes T = |base_state|` up to rare identical leaves (no impact).
Decidable from `(c, w)` in a few lines over `occs`/`valsOf` (`Spec/Occs.lean`). With A7,
tree-shaped records cost at most 2 × A7 node rows (pre and post bytes in lockstep, as v1).
**Raised to the lead** (spec request for lane spec-v3 / V0).

### 1.4 `UnfoldBound e` and the best bound without any amendment

**Decision (lead): no A7 yet.** Every completeness / height statement of this lane takes
an explicit hypothesis

```lean
def UnfoldBound (e : Nat) (ws : List Bytes) (root : Bytes) (keys : List (List Nat)) : Prop :=
  unfoldedBytes (partialTrie ws root keys) ≤ e
```

(`Spec/TreeRecs.lean`; `treeRecs_bytes_le`: under `UnfoldBound e` the tree-shaped records
hold `≤ e` bytes, since `storeBytes = unfoldedBytes` by `treeRecs_spec`).  The node table
has one row per record byte (+ `SUM` row + padding), so its height obligation is
`e + 1 ≤ 2^22`; value records likewise.

**Best bound provable from `RelD0` alone.**  Notation: `B = |base_state|` (≤ 3,000,000),
`K` = number of read keys (with multiplicity, as passed to `partialTrie`), `D = trieFuel = 400`,
`N` = largest node entry of the store, `V` = largest value entry (`N, V ≤ B`; on NEAR
`N ≤ 559 + |hex-prefix key|`).

> `unfoldedBytes (partialTrie ws root keys) ≤ K·D·N + K·V`,
> and more finely `≤ N · Σ_{d<D} min(K, 16^d) + K·V`.

Proof (by induction on the fuel of `buildFor`): a subtree is revealed only if a non-empty
key list reaches it; a branch routes each key to at most one child (by its first nibble)
and keeps a key that ends there for its value slot; an extension passes only the keys with
its prefix; a leaf has no children.  So at each depth the revealed occurrences receive
pairwise disjoint, non-empty sub-multisets of the keys (≤ `K` of them, and ≤ `16^d`), there
are at most `D` depths (the fuel), and each revealed value consumes a distinct key.  Each
node occurrence is a store entry (`EntriesFound`), so its encoding has `≤ N` bytes.  Nothing
better holds without an amendment: the example of §1.3 (one ≈ 560-byte "universal" branch
repeated under every slot) attains `≈ K · depth · 560` while `B < 1 MB`.

Numbers: with `K = 9,000`, `N = 559`, `D = 400`: `N · Σ_{d<400} min(K,16^d) ≈ 559 ·
(4,369 + 396·9,000) ≈ 2.0·10^9` bytes — far beyond one `2^22`-row table.  So without A7 the
tables are complete only for witnesses with `UnfoldBound (2^22 − 1)` (and the value-record
analogue); on real chains `unfoldedBytes = |base_state|` up to rare identical leaves.
(Paper proof; the Lean statement is the hypothesis above.)

### 1.5 A7 accepted: what is counted, and row costs per unfolded byte

The lead accepted A7 as a decidable conjunct of `InD0` (`RelD0a B … := … ∧ unfoldBytes ≤ B`,
spec lane, `NearSpecV3/ChunkValidationV0a.lean`).  This lane keeps **every completeness and
height theorem parametric in the bound** (`UnfoldBound e`, §1.4).  **Soundness never
mentions it.**

**Definition to mirror (tree records).**  For each transition `τ = 0..K`:

* `T_τ` is the partial trie the relation builds for `τ`:
  `partialTrie ws root_τ keys_τ`, where `keys_τ` is every key `τ` reads or writes
  (reads, account `set`s, `[0,15]`).
* `nodeB_τ = Σ_{o ∈ occs T_τ} |nodeEnc o|` counts node occurrences, each **per read-path
  copy**.  A digest shared by several paths is counted once per occurrence.
* `valB_τ = Σ_{v ∈ valsOf T_τ} |v|` counts revealed value occurrences.
* **Post-write path copies cost no extra records.**  Account `set`s are lockstep: the post
  bytes sit in the same rows as the pre bytes, so `nodeB_τ` already counts them.
* `upsB_τ` counts the `0x0f` upsert's new nodes, under `upsV3` option A (§2.3):
  `upsB_τ = Σ_{o ∈ occs Q_τ} |nodeEnc o|` (value occurrence of `Q_τ` counted in `valB`).
  * `Q_τ = upsert (prune_{[0,15]} T_τ') [0,15] v_τ`.
  * `T_τ'` is the lockstep post-trie.
  * `prune_k t` replaces every child that is off the path of `k` with `.hash (hashOf child)`.
  * `Q_τ` has at most 6 revealed nodes.
  * Under option C (A4), `upsB_τ = 0`.

So `unfoldBytes = Σ_τ (nodeB_τ + valB_τ + upsB_τ)`.  Bounding the parts separately is also
fine.  Some tables need occurrence counts:

* `nOcc = Σ_τ (|occs T_τ| + |occs Q_τ|)`
* `vOcc = Σ_τ |valsOf T_τ|`

**Rows (all instances share one table each):**

| table | rows | per unfolded byte (node occurrence of `L ≥ 46` bytes) |
|---|---|---|
| `nodeV3` | `Σ_τ (nodeB_τ + upsB_τ) + 1` (SUM) | **1** |
| `valV3` | `Σ_τ valB_τ + #empty values + 1` | 1 (value bytes) |
| `sha_t` | per node occurrence: **2** messages (`NPRE` and `NPOST`, every record), each `1 + 17·⌈(L+9)/64⌉` rows; per value occurrence: 1 message | `≤ 0.531 + 40.25/L` per node byte (`≤ 1.41` at `L = 46`, ≈ 0.61 at `L ≈ 500`); ≈ 0.27 + 18/L per value byte; plus the other tables' hashing |
| `uniqV3` | `32 · (nOcc + vOcc)` | `32/L` (`≤ 0.70`); binding cap `nOcc + vOcc ≤ 131,071` |
| `headV3` | 32 per instance | 0 |
| `walkV3` | `Σ_walks (|key nibbles| + 2)` | 0 (does not scale with unfolding) |

Widths and `W_eq` are in §4.  From these, `B0` must satisfy, against `2^22` rows:

* `nodeB + upsB ≤ 2^22 − 1`
* `0.531·nodeB + 40.25·nOcc + (other SHA) ≤ 2^22`
* `nOcc + vOcc ≤ 2^17 − 1`

The 8 MiB check uses the widths in §4.

### 1.6 Alternative: one record per distinct digest (graph) plus post copies on write paths

| | tree (current) | graph |
|---|---|---|
| pre-state node rows | `Σ` occurrences (unfolded) | distinct digests `≤ |base_state|` (does not scale with sharing) |
| post-state | lockstep, same rows, free | separate **post-copy records** for every write-path occurrence. Their bytes are copied from the pre record (an `ENT`-style copy with window exceptions). They still scale with unfolding of the write paths, so an A7-type cap on write-path bytes is still needed. |
| SHA | 2 messages per occurrence | 1 per distinct record + 1 per post copy |
| uniq | 32 rows per occurrence | 32 rows per distinct record |
| depth ≤ 400 / fuel | 9 bits per record (`depthBound`); occurrence = record | one record sits at many depths, so walks need a depth counter again. Soundness must go through "fuel-unfolding of the graph refines `partialTrie`" (`find_refinedBy`, `hashOf_refinedBy`, `upsert_refinedBy`; a `set_refinedBy` is missing). Cycles (SHA cycles) must be handled by fuel, not rank. |
| `PARENT` | exact (one per record) | chained with use counts |
| proof state | M1 spec done, `node3_view` done, render ≈ 2/3 | spec redone (≈ 1.5–2 k lines), `nodeV3` with a post-copy mode and copy bus (view re-port ≈ 3 k changed lines, render redone), walk depth counter: **≈ +5–7 k lines**, M1/M5 restart |

* **Honest witnesses** (`unfolded ≈ |base_state|`, rare shared leaves): node rows are the
  same or **higher** with the graph (pre records plus post copies vs lockstep), SHA rows
  ≈ halve, uniq is the same.
* The graph raises `B` only for adversarial, heavily shared witnesses, which A7 excludes
  anyway, and it still needs a cap on write-path copies.

**Recommendation: keep tree records.** (**Lead: accepted**; adopt the `wr` flag if `sha_t` rows bind `B0`, which the spec lane picks from §1.5.)  If SHA rows bind `B0`, the cheap fix within the
tree approach is to send `NPOST` bytes only for records on write paths (a node-constant
`wr` flag; `post = pre` otherwise, with the post digest taken from the pre digest).  That
halves SHA for read-only records with a small `nodeV3` delta.

## 2. Design decisions (this lane)

### 2.1 Writes through shared records

Records are tree-shaped (one record per parent slot, `PARENT` is a permutation, v1). Every
record is a single occurrence of the unfolded pre-trie, so **v1's per-record pre/post
bytes in lockstep suffice** for `set` (accounts, 72 → 72): a write changes exactly the
records on its path, each once. The store-lane finding (shared record on two written
paths) cannot arise: two paths never share a record unless they share the whole prefix
in the trie. Option (a) of STATUS-V3-STORE §2.2 is not needed.

### 2.2 Node side split in three tables

`nodeV3` keeps v1 `node`'s column layout (`0 … 162`) and row structure, so v1's 22-module
extraction and render proofs transfer by adaptation; instance heads and value records,
which have different row shapes, are separate small tables:

* **`headV3`** (32 rows per instance τ): root digest window; `ROOT (τ, pre)` in,
  `MIDROOT (τ, lockstep post)` out; `PARENT (rid, τ, 0, …)` to the root record (so v1's
  root special cases disappear); the walks' `START` edge `(0, τ) –START→ (root target, 0)`;
  `DIGS` of the root entry.
* **`valV3`**: one record per revealed value occurrence (tree-shaped), bytes hashed as
  `VPRE(vid)`, the same bytes received from the value's parser on `VBYTES` (`acct` /
  `akey` / `sched` / `qvals` / public), `VPARENT (vid, len)` from the unique value window,
  `DUP`/`ENT` like node records, `SIZE`.
* **`nodeV3`** deltas: `τ`; `PARENT` carries τ; depth ≤ 399 (9 bits on the first row);
  value windows onto `valV3` records with variable `vlen` (LE accumulator over `VLEN`, top
  byte 0), `tw` = written in lockstep (post digest `VPOST(vid)` of the same length) else
  `preg = reg`; `DIGS` from every digest window; `DUP`/`ENT`; edge kinds; `LEND` marker per
  leaf; dead target `(nid, s)` for an extension's last nibble when the child is unrevealed;
  `BMAP` per branch; `SIZE` instead of v1's in-table 3,000,000 check.

### 2.3 `0x0f` upsert: separate table `upsV3` (**decided: option A**; not started)

Lockstep pre/post records express only same-length `set`s (accounts).  The `0x0f` upsert
changes `memory_usage` along its path with truncated Nat arithmetic (`m + new − old`), may
change the value length, and when the key is absent changes node shapes (`splitLeaf`,
`splitExt`, new branch child/value).  It is applied **after** the lockstep writes
(`set_upsert_comm`, account keys `[0,0,…] ≠ [0,15]`): the head sends the lockstep post-root on
`MIDROOT (τ, ·)`, and the chain is `ROOT τ → head → MIDROOT τ → upsV3 → ROOT τ+1`.

**Reduction (spec side, available):** by `upsert_hashOf_congr` the post-root only depends on
the path trie `P` (the lockstep post-trie pruned to the path of `[0,15]`: ≤ 3 revealed nodes,
every off-path child `.hash`).  The obligation is `Q = upsert P [0,15] v` for the new path
trie `Q` (≤ 6 revealed nodes: ≤ 3 rewritten path nodes, `wrapExt` extension, split branch,
moved leaf / shortened extension, new leaf).  Case table for a 2-nibble key: per level
(root / after one nibble / after two) the node is a leaf (replace or `splitLeaf`), an
extension (descend or `splitExt`) or a branch (descend into slot, new child leaf, or set
the branch value) — 3 levels × 3 shapes × ≤ 3 outcomes.

**The cost driver is cross-record byte access, not the case logic.**  `Q`'s nodes copy
bytes from `P`'s post encodings: 15 sibling windows (shifted by 32 when a child is
inserted before them), the moved leaf's slot, the moved/shortened key (re-hex-prefixed: a
nibble shift by 1–3), and new `MEM` / `VLEN` values.  Options:

* **(A) `Q` as `nodeV3` records** of a pseudo-instance (their bytes, fields and hashes are
  then covered by `node3_view` unchanged) + a generalised `ENT` copy (`ENT (src, len, pos−off,
  b)` per row, with an offset column) for windows and slots + a key-nibble copy over the
  chained `EDGE` provider + a small field-level `upsV3` table (case selector, `u64` `MEM`
  arithmetic with truncation, value length).  Changes `nodeV3` (≈ 4 columns, 2 interactions:
  view port ≈ +500 lines); `upsV3` + link ≈ 3 k lines.
* **(B) bespoke byte-level `upsV3`** with its own field parser for `P` and `Q` (duplicates
  much of `nodeV3`'s 6 k-line view; ≈ 5–6 k lines) and a multiplicity column on `nodeV3`'s
  post-byte stream so that `upsV3` can copy `P`'s bytes (no collision assumption).
* **(C) A4** (`0x0f` present; design doc §4): removes insertion; with present `0x0f` the
  upsert is a `set` plus `MEM`/`VLEN` updates along ≤ 3 path nodes, i.e. lockstep records
  with `MEM`/`VLEN` excluded from "post = pre" and a per-path-node `u64` delta — ≈ 1 k lines.

Recommendation: (A) if insertion must stay in D0 (no amendment); (C) if A4 is acceptable.
**Lead decision: A** (A4 rejected; B costs more for no gain).

### 2.4 Walks

* No depth counter (node depth ≤ 399 bounds `fdepth`, `pathsRevealed_of_rank`).
* `START` edges only from heads, keyed by `(0, τ)`; a walk's first row has `I = τ`.
* Terminal kinds follow `AbsentWitness`: `VAL` (edge kind `VAL`, target the value record),
  `ABS_KEY` (a `KEY`/`LEND` edge with a different symbol: `extNib`, `leafNib`, `extLen`,
  `leafLen`), `ABS_BR` / `ABS_VAL` (`BMAP`: bit `sym` of the bitmap is 0, or no value at
  `END`).  After an absent terminal the walk drains the remaining `KEYNIB` symbols.
  `FINAL (w, τ, kind, k)`.

### 2.5 Weak uniqueness (`uniqV3`)

Key `(τ, digest)`; `τ` is segment-constant and steps by a bit between segments (so an
instance's entries are contiguous); within an instance the digest is strictly larger
(`eq = 0`) or equal (`eq = 1`, then `DUP (eid, eid_prev)`); `nodeV3`/`valV3` answer `DUP` by
copying the entry's bytes from its predecessor over `ENT (eid, len, pos, byte)`.  Node/value
role clashes are covered because value records live in the same `ENT` space.

## 3. Statements and theorems (all kernel-checked; axioms ⊆ {propext, Classical.choice, Quot.sound})

| table | view statement / theorem | render | link |
|---|---|---|---|
| `uniqV3` | `UniqViewStmt` / **`uniq_view`** (`Extract/UniqProof.lean`) | **`uniq_render_local`, `uniq_render_traffic`, `uniqEntries_wf`** (`Render/Uniq*.lean`) | **`uniq_weak`, `uniq_functional`, `storeOf_hashFunctional`** (`Link/Uniq.lean`) |
| `walkV3` | `WalkV3ViewStmt` / **`walk3_view`** (`Extract/WalkProof*.lean`) | **`walk_render_local`, `walk_render_traffic`** (`Render/Walk*.lean`) | open |
| `headV3` | `HeadViewStmt` / **`head_view`** (`Extract/HeadProof.lean`) | **`head_render_local`, `head_render_traffic`** (`Render/HeadRender.lean`) | open (ROOT chain) |
| `valV3` | `ValViewStmt` / **`val_view`** (`Extract/ValProof.lean`) | **`val_render_local`, `val_render_traffic`** (`Render/Val*.lean`) | open |
| `nodeV3` | `NodeV3ViewStmt` / **`node3_view`** (`Extract/Node/Proof.lean`; per-node lemmas `leafEdges`, `extEdges`, `brEdges`, `nodeDigs`, `nodeEnt`, `nodeDPVB`, `nodeAll`; global `nodeTrafficOf` incl. the `SUM` row's `SIZE` total, `nodeWfOf` incl. `depthBound`) | **`node_render_local`, `node_render_traffic`** (`Render/Node/*.lean`; hypotheses `NodeOk vs`, honest height `logOf (Σ |ser false| + 1)`) | open |
| spec | **`UnfoldBound`, `treeRecs_bytes_le`** (`Spec/TreeRecs.lean`) | | |
| spec | **`storeBuildR`, `pathsRevealed_of_rank`, `hashFunctional_of_weakUniq`, `treeRecs_spec`** | | |

Render theorems are stated for any trace whose table `t` has the generator's cells
(`hcell` for rows below the height and columns below the width, `hlog` the honest height).

## 4. Budget (kernel-checked: `NearV3/BudgetCheck.lean`, `report_g1`, `report_g3`, `weqTrie_g1`, `weqTrie_g3`)

| table | width | interactions | aux g=1 | degree g=1 | `W_eq` g=1 | `W_eq` g=3 | maxLog |
|---|---:|---:|---:|---:|---:|---:|---:|
| `nodeV3` | 185 | 18 | 18 | 4 | 353 | 297 | 22 |
| `headV3` | 73 | 8 | 8 | 4 | 161 | 161 | 11 |
| `valV3` | 15 | 7 | 7 | 4 | 95 | 95 | 22 |
| `walkV3` | 56 | 6 | 6 | 4 | 128 | 128 | 21 |
| `uniqV3` | 53 | 2 | 2 | 5 | 101 | 101 | 22 |
| **total** | 382 | 41 | | | **838** | **782** | |

Design estimate (§3.1) for node + walk + uniq was 345 + 104 + 81 = 530; this lane's five
tables are 838 (+308: heads 161, value records 95, wider walk/uniq).  `uniqV3` has degree 5
(gate `sf·eq` on `DUP`); a gate column would save 8 (left as is: proofs done).  `upsV3` not
counted.

## 5. Reuse

* `uniqV3` view: ≈ 70 % of v1 `SortProof` (structure, segment, delay-line, carry chain
  copied; new segment constants, equal case, `DUP`).
* `walkV3` view: ≈ 60 % of v1 `WalkProof`; render (helper) built on v1's `Render/Walk*`
  pattern.
* `headV3`, `valV3`: new, written in the same segment framework (`Extract/Segments.lean`).
* `nodeV3`: v1 layout kept for columns `0 … 162` so the v1 node view (5.8 k lines) can be
  adapted; estimated 60–70 % reusable (row/field structure, bytes, windows unchanged; edges,
  root handling, value windows, sizes change).

## 6. Open items

1. ~~`nodeV3` render~~ done (`NodeOk` adds: depth < 400, key length < 510, value length bytes < 256, rows Σ+1 ≤ 2^22 — the last is where `UnfoldBound` enters).
2. **Link layer**: ROOT/MIDROOT chain; trie of instance τ = records (tree via `PARENT` +
   depth ⇒ `RootedDagR` with rank = depth); entries ⇒ `storeOf` covered by `uniq` entries
   (`storeOf_hashFunctional`) ⇒ `storeBuildR`; walks ⇒ `find`/`AbsentWitness`
   (`absent_iff`); lockstep post-root = `set`s.
3. **`upsV3`** (§2.3): option A decided. Order: node render → link layer → `upsV3`.
4. **A7** accepted (spec lane `RelD0a`); counting definition and row costs in §1.5; completeness/height parametric, soundness bound-free.
5. `size` lane consumes `SIZE (0, ·)` (node) and `SIZE (1, ·)` (values).
6. Producers must switch value pre-bytes from `BYTES (VPRE)` to `VBYTES (vid, …)` (`acct`
   v3 variant, `akey`, `sched`, `qvals`), and send `FINAL`/`KEYNIB` in the v3 formats.

## Modules

| module | content |
|---|---|
| `NearV3/Spec/Rank.lean` | `RootedDagR`, `storeBuildR`, `fdepth_le_rank`, `pathsRevealed_of_rank`, `WeakUniq`, `weakUniq_functional`, `hashFunctional_of_weakUniq` |
| `NearV3/Spec/TreeRecs.lean` | `recsT`/`valsT`/`depsT`, segments, `treeRecs_spec`, `unfoldedBytes` |

Build: `lake build ZkFormal.NearV3.Spec.TreeRecs` (Rank 0.5 s, TreeRecs 1.7 s).

## Commits

(see `git log lane/v3-trie`)
