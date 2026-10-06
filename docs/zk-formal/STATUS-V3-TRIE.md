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
| M5 | `nodeV3` view proof (adapt v1's 22 `Extract/Node*` modules), `nodeV3` render, link layer (trie of τ hashes to root, finds/absents, post-root), `upsV3` (`0x0f` upsert incl. insertion) | **open** |

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

### 2.3 `0x0f` upsert: separate table `upsV3` (open)

Lockstep pre/post records express only same-length `set`s (accounts).  The `0x0f` upsert
changes `memory_usage` along its path with truncated Nat arithmetic (`m + new − old`), may
change the value length, and when the key is absent changes node shapes (`splitLeaf`,
`splitExt`, new branch child/value).  It is applied **after** the lockstep writes
(`set_upsert_comm`, account keys `[0,0,…] ≠ [0,15]`): the head sends the lockstep post-root on
`MIDROOT (τ, ·)` and `upsV3` (to be designed) re-reveals the upsert path of the lockstep
post-trie (bytes copied from the lockstep records' post streams, so no collision assumption),
computes the post-upsert path (incl. insertion modes) and sends `ROOT (τ+1, ·)`.  Every
instance has exactly one `0x0f` upsert (scheduler step), so the chain is
`ROOT τ → head → MIDROOT τ → upsV3 → ROOT τ+1`.

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
| `nodeV3` | `NodeV3ViewStmt` (`Extract/NodeView.lean`, statement only) | open | open |
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

1. **`nodeV3` view proof** (adapt `Extract/Node*`), **`nodeV3` render**.
2. **Link layer**: ROOT/MIDROOT chain; trie of instance τ = records (tree via `PARENT` +
   depth ⇒ `RootedDagR` with rank = depth); entries ⇒ `storeOf` covered by `uniq` entries
   (`storeOf_hashFunctional`) ⇒ `storeBuildR`; walks ⇒ `find`/`AbsentWitness`
   (`absent_iff`); lockstep post-root = `set`s.
3. **`upsV3`** (§2.3).
4. **A7** (unfolded-size cap, §1.3) — spec request.
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
