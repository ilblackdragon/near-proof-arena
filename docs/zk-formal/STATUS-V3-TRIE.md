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
| M2 | `uniqV3` table, view, link, render | in progress |
| M3 | `walkV3` table, view, link, render | open |
| M4 | `nodeV3` table + budget | open |
| M5 | `nodeV3` view, link (trie of τ hashes to root, finds/absents, post-root) | open |

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

(Design of `nodeV3`/`walkV3`/`uniqV3` continues in §3 as tables land.)

## Modules

| module | content |
|---|---|
| `NearV3/Spec/Rank.lean` | `RootedDagR`, `storeBuildR`, `fdepth_le_rank`, `pathsRevealed_of_rank`, `WeakUniq`, `weakUniq_functional`, `hashFunctional_of_weakUniq` |
| `NearV3/Spec/TreeRecs.lean` | `recsT`/`valsT`/`depsT`, segments, `treeRecs_spec`, `unfoldedBytes` |

Build: `lake build ZkFormal.NearV3.Spec.TreeRecs` (Rank 0.5 s, TreeRecs 1.7 s).

## Commits

(see `git log lane/v3-trie`)
