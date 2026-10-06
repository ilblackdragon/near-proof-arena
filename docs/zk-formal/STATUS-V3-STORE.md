# STATUS — lane `v3-store` (v3 trie: hash-indexed stores, spec side)

Branch `lane/v3-store` (off `lane/v3-air`). Design: `V3-D0-DESIGN.md` §3.2, §3.3,
§6.2, §10.3. Lean: `zk-formal/ZkFormal/NearV3/Spec/`. No v1 table, proof or
definition is modified. `zk-formal/lakefile.toml` gains a path `require` of
`NearSpecV3` (`../spec/lean/v3`). That package is resolved by name and reuses the
same `NearSpec`/`ArenaCore` checkouts, so the v1 import closure is unchanged.

All theorems below are kernel-checked. None uses `sorry` or `native_decide`.
Axioms ⊆ {propext, Classical.choice, Quot.sound}.

## 1. What is proved

### 1.1 `StoreBuildStmt` (soundness direction): **proved**

`ZkFormal.NearV3.storeBuildStmt : StoreBuildStmt` (`Spec/StoreSound.lean`), via
`storeBuild`:

```lean
theorem storeBuild (ns : List NodeRec3) (vs : List ValRec3) (τ root : Nat) (keys : List (List Nat))
    (hf : HashFunctional (storeOf ns vs τ)) (hd : RootedDag ns vs τ root)
    (hp : PathsRevealed ns vs root keys) :
    (partialTrie (storeOf ns vs τ) (digest ns vs root) keys).refinedBy (fullTree ns vs root) ∧
    (partialTrie (storeOf ns vs τ) (digest ns vs root) keys).hashOf = digest ns vs root ∧
    ∀ k ∈ keys, (partialTrie (storeOf ns vs τ) (digest ns vs root) keys).find k =
      (fullTree ns vs root).find k
```

The model (`Spec/Records.lean`):

* **`NodeRec3 = { tau, node : Rec3 }`.** `Rec3` is v1's `NodeRec` with two changes:
  * a revealed value slot is `VSlot3.val vid`, a reference to a **value record** `ValRec3 = { tau, bytes }` of any length;
  * a child is `Kid3.node cid`, `Kid3.hash h` or `Kid3.none`.

  Records may be shared, so the records form a DAG.
* **`fullTree ns vs n`** unfolds the DAG with fuel `ns.length`. **`digest n`** is the hash of that tree.
* **`storeOf ns vs τ`** is the witness store of instance `τ`: `nodeEnc (fullTree n)` for every `τ` record, in id order, followed by the bytes of every `τ` value.
* **`HashFunctional l`**: entries with equal SHA-256 digests are equal. `hashFunctional_of_nodup` derives it from **`DigestsDistinct l`** (pairwise-distinct digests), which is what the AIR proves.
* **`RootedDag ns vs τ root`** has four conditions:
  * the root is a `τ` record;
  * a child `c` of a `τ` record `n` is a `τ` record with **`n < c`**;
  * a referenced value is a `τ` value;
  * every `τ` record is well formed (`Rec3.wf`, which mirrors `PTrie.wf`).
* **`PathsRevealed ns vs root keys`**: for each read key, `find` on `fullTree root` is determined (`≠ none`), and the lookup visits at most `trieFuel = 400` revealed nodes (`fdepth`).

The proof has two layers.

The PTrie layer is `buildFor_spec` in `Spec/StoreBuild.lean`. Take any store `s` and a trie `t` that is
`Stored` in it, meaning every revealed node preimage and every revealed value is what `storeGet`
returns for its own digest. Suppose `t.find k ≠ none` for every `k ∈ keys`. Then for every fuel `f`:
* `buildFor s f t.hashOf keys` refines `t`;
* it answers `find k` exactly as `t` does whenever `fdepth t k ≤ f`.

The byte-level decoding inside `buildFor` is inverted by `nodeEnc`. The per-node lemmas are
`buildFor_leaf`, `buildFor_ext`, `buildFor_branch` and `buildFor_branchV`. They rest on
`hpDecode_hexPrefix`, `kidHashes_hashes` and `leNat_u16/u32/u64`.

The record layer is in `Spec/StoreSound.lean`:
* `treeOf3_fuel` and `fullTree_unfold`: under `RootedDag`, the unfolding of a record does not depend on fuel;
* `dag_induction`: induction over the records, children first;
* `fullTree_wf`;
* `fullTree_stored`: `HashFunctional` gives `Stored` through `found_of_mem`.

### 1.2 Completeness direction: **proved, under hypothesis A6** (see §3)

These theorems are in `Spec/StoreBuilt.lean` and `Spec/StoreComplete.lean`.

* **`built_spec` (no hypothesis).** Take any store `ws`, fuel, key set, and a 32-byte digest `h`. The trie `buildFor (mkStore ws) f h keys`:
  * has root hash `h`;
  * is `PTrie.wf`;
  * is `Stored` in `mkStore ws`;
  * satisfies `fdepth ≤ f` on every key.

  Decode followed by re-encode is the identity on every node the builder accepts. A corollary is `partialTrie_hashOf`: the relation's check `tMain.hashOf == prev_state_root` holds by construction whenever the root is 32 bytes.
* **`storeComplete`.** Take a witness store `ws`, a 32-byte `root`, nonempty `keys` whose relation lookups are all determined, and suppose `StoreDag (partialTrie ws root keys) rk` (A6) holds. Then the **hash-consed records** `nsOf`/`vsOf` have the following properties:
  * the records are built from one record per *distinct* revealed node digest, which merges what all occurrences of a digest reveal, and one value record per distinct revealed value;
  * ids are the digests sorted by rank, so `cid > N`;
  * they form a `RootedDag`;
  * their store is `DigestsDistinct`, and hence `HashFunctional`;
  * `digest = root`;
  * they are `PathsRevealed` for `keys`;
  * they look up every read key exactly as `partialTrie ws root keys` does;
  * `storeBytes ≤ Σ |ws|`. The record store is a duplicate-free sub-multiset of `ws`, which is what `w.size` needs.
* **`storeComplete_rebuild`** combines this with `storeBuild`: `partialTrie (storeOf ns vs τ) root keys` has hash `root` and agrees with `partialTrie ws root keys` on every read key.

### 1.3 `TrieOpsStmt`: **proved** (`Spec/TrieOps.lean`, `trieOpsStmt`)

* `PTrie.find_set_self` and **`PTrie.find_set_ne`**: `set` is a map update on revealed keys. This needs no `wf`.
* **`find_upsert_ne`**: NearSpec's `PTrie.find_upsert_other`, restated.
* `set_mem` / `set_memD`: `set` keeps every stored `memory_usage`.
* **`PTrie.set_upsert_comm`** (with `Kids.set_upsert_comm`): let `k₁ ≠ k₂`, `t.wf`, and let the old value at `k₁` have the new value's length. If `t.set k₁ v₁ = some t₁` and `t.upsert k₂ v₂ = some t₂`, then `∃ t₁₂, t₁.upsert k₂ v₂ = some t₁₂ ∧ t₂.set k₁ v₁ = some t₁₂`. This is *equality* of the two tries, so the post-roots are equal too.
  * The length hypothesis is necessary. When the upsert splits `k₁`'s leaf, the moved leaf's `memory_usage` is computed from the value length *at that moment* (`splitLeaf`). Account writes in D0 are 72 → 72 bytes.
  * Supporting lemmas: `set_splitLeaf`, `set_splitExt`, `kidsFrom_set`, `set_kids1/2`, `set_wrapExt`.

### 1.4 Non-membership: **proved** (`Spec/Absent.lean`)

`AbsentWitness t key` has these constructors:

| constructor | AIR terminal (§3.2.4) | condition |
|---|---|---|
| `brSlot` | `ABS_BR` | branch slot `n` empty (`Kids.slot cs n = none`) |
| `brVal` | `ABS_VAL` | key ends at a branch with no value |
| `extNib`, `leafNib` | `ABS_KEY` (`nib ≠ sym`) | `k[i] = a`, `key[i] = b`, `a ≠ b` |
| `extLen` | `ABS_KEY` (key ended) | `key.length < k.length` |
| `leafLen` | `ABS_KEY` (lengths differ) | `k.length ≠ key.length` |
| `brDown`, `extDown` | (walk steps) | descend through a revealed branch child or extension |

The facts proved about it:
* soundness: `absent_find`;
* completeness: `absent_of_find` / `kids_absent`, together `absent_iff : AbsentWitness t key ↔ t.find key = some none`;
* insertion: `upsert_absent`. Along a witness, `upsert` always succeeds, `find key = some (some v)`, and every other key is unchanged.

The local rewrites the AIR's insertion mode has to implement are:
* `upsert_brSlot`: a new leaf goes into the empty slot, and the branch gains `leafMem rest |v|`;
* `upsert_brVal`;
* `upsert_leaf_ne` (`splitLeaf`);
* `upsert_ext_np` (`splitExt`);
* `upsert_branch_down` and `upsert_ext_down`: a frame on the path replaces its child, and its `memory_usage` moves by the child's change.

`keyBwState_nibbles : keyBwState = [0, 15]`.

## 2. The AIR this enables (next phase: `uniq`/`DIGS`, node/walk deltas)

### 2.1 `uniq`: a second instance of v1 `sort` over `(τ, digest)`

The obligation is that the extracted records satisfy `DigestsDistinct (storeOf ns vs τ)` for each `τ`.
`hashFunctional_of_nodup` then gives `HashFunctional`, which feeds `storeBuild`.

* **Bus `DIGS` (#17)** carries the message `(i, b)`. Here `i` ranges over `0..33`, LSB-first over the
  34-byte key `K = digest[31] … digest[0] ‖ τ_hi ‖ τ_lo`, so that `τ` is the most significant part.
  This is the same shape as v1 `RIDS (r, i, id_i)`, but the receipt index `r` is replaced by an entry
  counter `e`. The full message is `(e, i, b)`.
  * Each **`τ` node record** sends its *own* digest once, from the `nf` row, using the `NPRE(nid)`
    `DIGEST` window it already receives. It does not send the digests of its children: a child that
    is revealed sends its own, and an unrevealed `Kid3.hash` is not a store entry.
  * Each **`τ` value record** sends `sha256(bytes)` once:
    * from `acct`/`akey` (`VPRE`) for an account or access-key value;
    * from the public bus (`VPUB`) for hint and scheduler values.
  * The `uniq` table is v1 `sort` with the receiving bus changed from `RIDS` to `DIGS`, the per-entry
    row count changed from 32 to 34, and `maxLog 21`. It checks `key_t = key_{t-1} + diff + 1`
    byte-serially. Strictly increasing keys mean all `(τ, digest)` pairs are distinct.
  * `SortViewStmt` / `sort_view` (`Extract/SortProof.lean`) is reused verbatim, made parametric in the
    bus id and the entry length. The statement it yields is that the multiset of received keys is
    strictly increasing, hence `Nodup`. The link has to show
    `(storeOf ns vs τ).map sha256 = (keys received with high part τ)`. This is exactly
    `store_digests` on the completeness side, mirrored.
* **Why per-`τ` and node + value together.**
  * Within one instance, a node digest and a value digest must also differ. Otherwise a value lookup
    in `buildFor` (`mkSlot`, first match) could return node bytes, and the reverse.
  * Across instances, the same digest may appear, because the main and implicit stores are separate
    witness lists.
* **Rows.** 34 per entry. At 3 MB of 56-byte nodes that is ≈ 58 k entries, so ≈ 2.0 M rows, under 2²¹.

### 2.2 `node` deltas (v1 `Tables/Node.lean` → `NodeV3`)

| v1 | v3 | Lean target |
|---|---|---|
| root `nf ∧ nid = 0`, `DIGEST (NPRE(0), len, pub root)` | root flag `rootf`: receives `ROOT (τ, d)` and `DIGEST (NPRE(nid), len, d)`; sends `ROOT (τ+1, d')` from `NPOST` | `RootedDag.root_inst`; `digest root = public root` |
| `PARENT (cid, depth+1, clen)` perm, `depth` column | `PARENT (τ, cid, clen)` **chained provider**: the child's first row provides with use count `u` (≥ 1 parents); the window sends; `cid > nid` by a range check on `cid − nid − 1` | `RootedDag.child` (`n < c`, same `τ`) |
| touched value window `DIGEST (VPRE(nid), 72, …)`, `VSLOT (nid)` | value-record window `DIGEST (VPRE(vid), vlen, d)` with `vlen` tied to the `u32` length bytes; `VSLOT (τ, vid)` chained (shared value records) | `VSlot3.val vid`, `RootedDag.vals`, `Rec3.wf` |
| — | `nf` row sends the record's own `(τ, NPRE(nid))` digest on `DIGS` | `DigestsDistinct` (node part) |
| `SUM` row: Σ revealed bytes | Σ over **records** (each shared record once) + Σ value records = `storeBytes` | `storeBytes ≤ 3,000,000` (`w.size`) |
| — | key rows provide `KEYAT (N, i, nib)` (chained); branch rows provide `BMAP (N, bm)` | `AbsentWitness` (`extNib/leafNib`, `brSlot`) |

**Post-state with shared records.** This is a finding for A-trie and must be decided before the node
table is fixed.
* A pre-state record reached by two read keys can be shared. Hash-consing makes this mandatory once
  digests are unique. An example is two identical account leaves under different branch slots.
* If both keys are written to different values, the post-state is no longer a DAG of the *same*
  records. The relation's trie is the unfolding, and `set` acts on one occurrence.
* So `NPOST` cannot be a per-record column when a written path passes through a shared record. Two
  options:
  * **(a)** Post-state records form their own (tree) instance, with `ROOT (τ+1)` from that instance.
    Its write paths are tied to the pre-records by `EDGE`, and they are not `DIGS`-constrained: the
    post-store is never looked up by hash.
  * **(b)** A D0 condition that no record on a written path is shared.

  (a) is complete; (b) is not. The spec lemmas used by (a) are `set_upsert_comm` and
  `find_set_ne`/`find_upsert_ne`: apply all writes in AIR order.

### 2.3 `walk` deltas

* Walks carry `τ`.
* Terminal kinds `FINAL (r, kind, k)` with `kind ∈ {VAL, ABS_BR, ABS_VAL, ABS_KEY}` follow
  `AbsentWitness` one constructor at a time:
  * `ABS_BR`: a `BMAP` lookup with bit `sym` = 0;
  * `ABS_VAL`: at `END`, the branch value flag is 0;
  * `ABS_KEY`: a `KEYAT` lookup `nib ≠ sym` (inverse), or the key ends inside a key (`extLen`), or the
    lengths differ at a leaf (`leafLen`).
* **Depth counter (new).** `PathsRevealed` needs `fdepth ≤ 400` (`trieFuel`).
  * v1 walks skip empty-key extensions (`EDGE` targets forward through them). Without a count, a long
    chain of empty extensions would make the relation's `buildFor` run out of fuel (`find = none`,
    the relation rejects) while the AIR accepts.
  * Fix: the `EDGE` message gains `Δ = 1 + #skipped empty extensions`. The walk keeps
    `dc += Δ` and checks `dc ≤ 400` once per walk (9-bit range check).
  * This is complete: `built_spec` gives `fdepth ≤ 400` on the relation's trie, and `fdepth_refinedBy`
    transfers it to the records.

## 3. Open: A6 (required for completeness of a strict-`uniq` AIR)

`storeComplete` assumes `StoreDag T rk`, where `T = partialTrie ws root keys`:

1. **Acyclic merged digest graph.** There is a rank `rk : Bytes → Nat` such that for every revealed
   node `o` of `T` and every child `c` of `o` whose digest is revealed *somewhere* in `T`,
   `rk o.hashOf < rk c.hashOf`.
2. **No role clash.** No revealed value has the digest of a revealed node.

**Why it is needed.** With one record per digest and `cid > N`, the merged graph must be acyclic:
* `T` is finite, because `buildFor` is fuel-bounded. But formally the store can contain a *SHA-256
  cycle*: entries `e₁ → h(e₂)` and `e₂ → h(e₁)`.
* Different occurrences of the same digest reveal different children, so a cycle can arise in the
  merge even when no root path repeats a digest.
* Likewise, a value whose bytes equal a revealed node's bytes is one store entry used in two roles.
  A strict `uniq` over `(τ, digest)` cannot accept that.

Neither can be ruled out without collision resistance, and the semantic theorems may not use it.
Both are false on every real chain, since no SHA-256 cycle is known. They are decidable from
`(c, w)`.

**Proposed D0 amendment A6 (`w.store_dag`).** For each partial trie `checkD0` builds, the revealed
node digests have a topological order (no cycle among "`o` revealed, `c` child of `o`, `c` revealed
somewhere"), and the revealed value digests are disjoint from the revealed node digests.

Possible implementation in `NearSpecV3`:
* collect `occs`/`valsOf` of the built trie;
* check that a DFS over the merged digest graph finds no back edge;
* check the disjointness.

This is about 60 lines. The Lean side then needs one more step: *acyclic ⇒ rank exists*, a standard
topological-sort lemma over a finite graph, which is not yet proved here. This lane does not edit
`spec/lean/v3`; **spec request to lane spec-v3 / V0.**

The alternative without A6 is a non-strict `uniq`:
* duplicate records with the same digest would prove byte equality with a canonical record through a
  content bus;
* but completeness still needs bounded rows (`T` can unfold a 3 MB store far beyond 2²² rows through
  a cycle), so A6 or an equivalent bound is needed anyway.

## 4. Notes for the next phase

* **Several partial tries per transition.** `checkD0` builds `t0 = partialTrie … [keyBufferedIdx]`
  and `tMain = partialTrie … (mainKeys …)` from the same store, and builds a trie per implicit
  transition. `storeBuild` applies to each key set separately, with the same records:
  `PathsRevealed` is per key list.
* **`readKey` determinacy.** `GoodV3` must assert `PathsRevealed` for exactly the keys the relation
  reads. `hread` in `storeComplete` is the same set.
* **Values of any length.** Hint values and scheduler states (`VPUB`) are value records like any
  other. Their `(len, sha256)` comes from the public bus instead of `sha_t`.
* **`partialTrie_hashOf`** makes `tMain.hashOf == prev_state_root` automatic. The AIR still needs
  `ROOT (0, prev_state_root)` only to *name* the root digest that `storeBuild` is applied at.

## 5. Modules and build

| module | content |
|---|---|
| `Spec/Codec.lean` | `nodeEnc`, LE round trips, `hpDecode_hexPrefix`, `kidHashes_hashes` |
| `Spec/StoreBuild.lean` | `Stored`, `fdepth`, per-node decode lemmas, **`buildFor_spec`**, `buildFor_hashOf` |
| `Spec/Records.lean` | `NodeRec3`, `ValRec3`, `fullTree`, `storeOf`, `HashFunctional`, `DigestsDistinct`, `RootedDag`, `PathsRevealed` |
| `Spec/StoreSound.lean` | **`storeBuild`**, **`storeBuildStmt`** |
| `Spec/StoreBuilt.lean` | **`built_spec`** (decode∘encode on accepted bytes) |
| `Spec/Occs.lean` | occurrences, `skel_eq` (`nodeEnc` injectivity via the decoder) |
| `Spec/StoreComplete.lean` | hash-consed records, **`storeComplete`**, `storeComplete_rebuild`, `partialTrie_hashOf`, `fdepth_refinedBy` |
| `Spec/TrieOps.lean` | **`trieOpsStmt`** (`find_set_ne`, `find_upsert_ne`, `set_upsert_comm`) |
| `Spec/Absent.lean` | **`AbsentWitness`**, `absent_iff`, `upsert_absent`, local insertion rewrites |

Build: `lake build ZkFormal.NearV3.Spec.StoreComplete ZkFormal.NearV3.Spec.Absent`. The modules are
not imported by `ZkFormal.lean`, so v1 targets are unaffected.
