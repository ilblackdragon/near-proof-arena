# E2E milestone M5a: INTAKE, working-set tree and FINAL in-circuit (state lane B)

Plan: `docs/zk-formal/E2E-GENERAL-CHUNK-PLAN.md` §3.2 (the `stRoot` working set), §4 (M5a).
Date 2026-11-03. Labels: **[M]** measured here, **[K]** kernel-checked Lean (std axioms),
**[S]** stated / design only.

## M5a-3 (fourth session, 2026-11-03)

### Bus-level step [K] (`lean/StateM5a/{Bus,Traffic,BusWalk}.lean`, std axioms, no `sorry`)

From bus balance to `rootHash (applyChanges …)`, with `Sha256CR` the only cryptographic premise:

* **`Bus`** (generic, ZkFormal): `busList A tr pub b s` = the messages sent / received on bus `b`,
  repeated by multiplicity; `count_busList` (= `busCount`), **`holds_perm`**: `Holds A pub tr` ⇒
  on every bus the sent list is a permutation of the received list (the LogUp predicate in list
  form); `perm_decode`: under an injective encoding the decoded message lists are permutations too.
* **`Traffic`** (generic record-level traffic):
  * **`walk_unique`**: at most one active row receives a `DOWN` at each `(w, d)`.  `UP` does not
    repeat the node's ref, so this is what lets a parent trust the answer at `(w, d')`.  Proof:
    the number of open `DOWN` edges of walk `w` crossing depth `d` is 1 at `d = 0` (one `WSB`
    root per walk) and never grows (`cross_step`: a row at `d` that descends replaces the edge
    that reached it), and the rows at `d` are at most the edges ending there.
  * **`walk_sem`**: any property `Sem` that every active row's step carries from its child's
    `(DOWN, UP)` pair to its own holds at every walk root (induction on depth, `child_of`).
  * **`tch_chain`**: `TCH` balance makes the writing `WSB` rows one chain from the public
    `TCH(0, prev)` to `TCH(n, post)` (row count `= n`, `a (j+1) = b j`).
  * **`ver_recv`**: a `VER` reader's record (all parts) is one published record, if publishers
    under one ref agree; **`reqresp`**: on a request / response bus (`MATQ`/`MATR`, `SIBQ`/`SIBA`,
    `SPQ`/`SPR`, `SXQ`/`SXR`) with one request per key, the response a requester receives comes
    from a responder that received exactly its request.
* **`BusWalk`** (the M5a instantiation):
  * **store**: `ver_store` — `σ = storeOf vers` (version-publishing rows' records by id; ids
    distinct); every `VER` reader's record is `OldOK σ ref R` (a version id's record, or a record
    hashed to the digest; digest publishers agree: `hashed_agree`, `Sha256CR` + `NodeSerInj` via
    `shallow_eq`).
  * **views**: `in_view_wf` (the expansion of a row's input ref reveals to its record with expanded
    children, well-formed), `out_view` (a node whose children collapse to the expansions of the
    published record's children collapses to the expansion of the output ref); `Cl` = collapse
    including written values (`.ref |x| (sha256 x) ↦ .val x`, leaf `slot` and branch `bval`),
    `cl_collapse` (keeps refinement), `cl_wf` (keeps `wf`).
  * **walk semantics** `Sem` = `SemF` / `SemU` / `SemD` by mode, and **23 row-local steps**:
    upsert `oLR`, `oUD`, `oEU`, `oUN` (with `MatRel`, the `MATQ`/`MATR` answer), `oUV`; delete
    `oLD`, `oLZ`, `oEZ`, `oES`, `oED`, `oEB`, `oDA`, `oDS`, `oDH`/`oDN`, `oDZ`, `oDV`; find `oLF`,
    `oLA`, `oEA`, `oEF`, `oFD`, `oFA`, `oFV` (`step_*`; `localOK_upsert`/`_delete`/`_find` turn
    them into `Traffic.LocalOK`).
  * **`chain_changes`** / **`bus_batched_changes`**: walk shape + `DOWN`/`UP`/`TCH` balance +
    every row's `LocalOK` + the writing rows as roots of the committed changes ⇒ on any revealed,
    well-formed witness trie with root `prev_state_root`, `applyChanges` succeeds and
    `rootHash = post_state_root`.  **Premise `Sha256CR` only**: `KeepsFW` (false, see below) is
    not used — well-formedness is carried along the walk (rows' memory / length bounds) and
    `Store.keepsFWRows` transfers it to the witness.

**What is still a premise** (open; field level / remaining ops): (1) decoding — each table's
`DOWN`/`UP`/`TCH`/`VER` interaction message is the injective encoding of the decoded record
(`perm_decode`'s hypotheses, refs as flag + 16 limbs); (2) `WalkShape` (`d' > d`: `BR` `d + 1`,
`SN` `d + klen` with `klen ≥ 1` from `isE·(1 − a₀)`; one root per walk: `WSB` `i` distinct,
`W_FINAL` offset) and active-row bookkeeping (`gdn ≤ gold` from the one-hot bundles); (3) the
per-row decoded facts each `step_*` takes (`OldOK` from `ver_store` / a hashing row, `NewOK`,
nibble lookups `K.drop d = …`, mismatch witness, memory / length bounds, kept-branch counts);
(4) row-local steps for the split ops (`oLX`/`oEX`/`oSL`/`oEP`/`oEM`/`oLM`), `oDL` and
`oD1`/`oLS` (the bus tool is `reqresp`); (5) the link from the write tape / `WRITE` order to the
change list (`KCMP` ⇒ `sortKV` is `Order`; the leaf ↔ change pairing is the `WSB` table).

### M5a-3 Lean (state, priority 2) [K]

* **`KeepsFW` is false** (`Store.not_keepsFW`: a `2^32`-byte value written into a well-formed
  leaf). Replaced by what holds (`Keep`): `RP P a b` = refinement whose stubs cover subtrees with
  property `P`; `upsert` and `del` commute with it for every `P` (`upsert_rp`, `del_rp`). With
  `P = False`: a change keeps the witness revealed, unconditionally (`full_upsert`, `full_del`,
  `full_applyChange`). With `P = wf`: every node of the spec's result is a node the rows
  rewrote or an old subtree, so `t₁'.wf` (the rows' new trie: range-checked memory limbs,
  nibbles, key / value lengths) gives `T'.wf` (`applyChange_wf_of_rows`). Together
  `keepsFWRows : KeepsFWRows`.
* **`batched_changes'`**: `batched_changes` without `KeepsFW`; premises `Sha256CR` and
  `ChangeRowsW` (the rows of every change, with `t₁'.wf`). The old `batched_changes` and
  `KeepsFW` are kept unchanged.
* Chain constructors `UChain.brVal` (`oUV`), `DChain.brDelVal` (`oDV`), `DChain.brValAbs` (`oDZ`),
  with their memory correspondence to `Br.memNew` in the docstrings; `uchain_sound` /
  `dchain_sound` extended (all other users go through them).
* `StepsBV.br_del_value_one` (+ `_leaf`, `_ext`, `_branch`, `_hash`, `br_del_value_none`): the
  spec step of the squash after a value delete leaving one child, for a future row op.

## M5a-2 (third session, 2026-11-03): batched FINAL in the AIR

Sections below this one describe M5a as first built (every walk row hashes its old and its new
node); the tables and the Lean list there are still valid, with the changes listed here.

### Design

Each trie node is hashed **once**:
* **pre-state nodes**: the first row that reads a node hashes it (`gsha = 1`) and publishes its
  record on a new bus `VER` under its digest, with a multiplicity (`vm`, 7 bits) equal to its other
  readers; every other reader — INTAKE finds and FINAL changes alike — receives the record from
  `VER` instead of hashing (this also batches INTAKE: T2's root was hashed by 53 walks, now once);
* **new nodes**: a node a later change rewrites is not hashed; its row publishes the record on
  `VER` under a *version id* (`nref = 1`; the id is the row's new-node message id
  `ID + 2·rid + 1`, unique per row and table); a node no later change rewrites is *final* and is
  hashed by its row, which publishes it under its digest for later readers (absent deletes read
  without rewriting). A final node's children are final (a rewrite of a child rewrites its parent),
  so its serialization has only digests (`gfin · isn = 0`).
* **refs**: every child slot, every `DOWN`/`UP`/`MATR`/`SPQ`/`SPR`/`SXQ`/`SXR`/`SIBQ` hash field and
  the root chain `TCH` carry a *ref* = (flag, 16 limbs): a digest, or a version id (cell 0 = id,
  others 0). The public ends `TCH(0, 0, prev_state_root)` and `TCH(n, 0, post_state_root)` are
  digests, so the last change must hash the root.
* **records**: a `BR` record is 17 `VER` messages (16 slots `(f, f·isn, f·32 bytes)` and one value /
  memory part), an `SN` record 3 (header with `isL`, `klen`, 36 payload bytes, memory limbs; key
  nibbles 0–31, 32–63): the backend caps a message at 63 fields. Every part carries the full ref.
  A key longer than one row (`cont`) is never on `VER` (always hashed, old and new).
* **range checks**: a published (unhashed) node's 8 memory bytes are looked up in `RNG` (the SHA
  table no longer checks them), as are a written branch value's length bytes.

No timestamps are needed: records are immutable values keyed by unique ids (a persistent store),
so the `VER` bus defines a function `σ : id → record`; the trie between changes is the expansion
of `TCH`'s ref through `σ` (`Store.Exp`). The trace generator runs twice: pass 1 (= the M5a
trace, still valid: `--unbatched`) finds every version's readers; pass 2 assigns `gsha`, `nref`,
`vm`, `vmn`.

### Results [M] (main stack: unified SWIRL, BabyBear Ext12, SHA-384 MMCS, stacked WHIR)

| | T1 (`d3c8/d3/02-h10196-s3`) | T2 (`d3c9/d3/00-h10018-s0`) |
|---|---|---|
| trie-node rows | 156 (unchanged) | 623 (unchanged) |
| SHA-256 messages of trie rows (M5a → batched) | 212 → 84 | 874 → 172 |
| SHA-256 blocks of trie rows | 524 → 172 | 2,370 → 327 |
| trie-row SHA-256 cells | 4.96 M → 1.64 M (−67 %) | 22.39 M → 3.12 M (−86 %) |
| cells per trie-node row (incl. SHA) | 32.6 k → 11.3 k | 36.7 k → 5.8 k |
| total used cells (`cost.py`) | 8.15 M → 4.83 M | 34.25 M → 14.97 M |
| committed (padded) cells | 14.52 M → 7.87 M | 47.33 M → 16.18 M |
| versions published / pre-state nodes hashed / final nodes hashed | 21 / 48 / 36 | 211 / 82 / 90 |
| proof (M5a → batched) | verifies: 1,243,380 → **1,258,042 B**, 268.2-bit, prove 260 s (8 threads, host load ≈ 45), verify 179 ms, peak RSS 1.52 GB | verifies: 1,533,468 → **1,296,042 B**, 268.2-bit, prove 4,392 s (throttled) → **478 s**, verify 190 ms, peak RSS 16.4 → **2.67 GB** |
| root | `1db48e38…249628` = Lean `stateRoot` | `61f5330a…07993006` = Lean `stateRoot` |

The final-node count matches the batching model's `fin` count (T1 36, T2 88 + 2 nodes with keys
longer than one row, which are always hashed). The prover is the M5a binary (unchanged,
`logs/SHA256SUMS-v2`); AIR hashes in `logs/SHA256SUMS-v3`. With the trie side batched, the
SHA-512 working-set chip (10.9 M of T2's 16.2 M committed cells, `WSA` 170 k cells per write) is
now the dominant state cost.

**Root equality.** `tracegen.py` asserts the circuit's last `TCH` root (a digest) = its
transcription's `applyChanges` root = the case's `post_root`; that root is the Lean `allFeatures`
run's `stateRoot` (T1, T2), and `m5a-tool apply` recomputes it with the Lean spec itself
(`revealTrie` → `applyChanges ∘ sortKV` → `rootHash`; `run.sh` step 2b) — equal on T1, T2 and
the synthetic case.

**Mutants** [M] (`logs/M5a2-mutants.txt`, on the final AIR): **T2 17/17, T1 9/9, synthetic
7/7 rejected** — each fails the precheck and the prover refuses it. The 12 of M5a, rerun, plus
five for the batched path: `verslot` (a row reading a version holds another off-path child byte
→ `VER` unbalanced), `vernid` (it claims another version's id → `DOWN` + `VER`), `vmcount` (a
pre-state node published for one reader more → `VER`), `finroot` (the last change leaves the
root as a version id → `TCH` against the public `post_state_root`, + `RNG`), `nidforge` (a version
under another row's id → the id constraint). Synthetic case: `bvalue` (`oUV` stores another value
byte → the `dvh` constraint), `bvmem` (`oDV` memory + 1 → the memory chain); its `node` and
`finroot` tampers do not apply (their helpers expect a leaf / branch root; that trie's root is an
extension). Proof sizes barely move: the WHIR query part (~0.94 MB) dominates and depends on
columns, not rows.

### Completeness: branch values (synthetic case)

New `BR` ops for a walk key that ends at a branch (a key that is a prefix of another): `oUV`
writes the branch value (over an old value or none; `valueMem` in the memory chain), `oDV`
deletes it keeping the branch (≥ 2 children, `squashBranch`'s last case), `oDZ` an absent delete
(no value; result `SAME`). The rewritten branch's value is now its own columns (`nhv`, `nvl`,
`nvh`; equal to the old value on every other op). No corpus case has them, so `synth.py bval`
builds a NEAR-shaped pre-state (`0x00 ‖ account`, `alice` next to `alice.near`, 18 keys) and 7
changes exercising `oUV` ×3, `oDV`, `oDZ`, `oFV` ×5, an extension-internal absent delete and
`extendChild` onto a kept branch; the Lean spec oracle confirms its root. **It proves** (D = 4): 26 `BR` / 31 `SN` rows,
1,237,614 B, 268.2-bit, prove 130 s, verify 172 ms (`logs/M5a2-syn-bval-*`).

### Lean [K] (std axioms, no `sorry`)

* `Store` — the batched-FINAL memory argument: `Ref` (digest | version id), records with ref
  children, the store expansion `Exp σ` and `exp_functional` (a ref expands to one trie: the trie
  one change leaves is the trie the next starts from); `Rv` (reveal: stubs replaced by nodes hashing
  to them) with `rv_refinedBy` (revealing keeps refinement of a revealed, well-formed witness;
  `Sha256CR` + `NodeSerInj` through `refinedBy_of_hash`) and `rv_collapse` (collapsing final nodes
  to digests keeps it; no assumption); `change_step` (one change, any step relation that carries
  refinement), `upsert_step`, `find_step` (INTAKE finds on the revealed pre-state), and
  `batched_upserts`: from `TCH(0) = prev_state_root` through every upsert change to a digest
  `post`, the spec's fold of the changes on the witness trie succeeds with root hash `post`;
  **`batched_changes`**: the same for every change, upserts and deletes (`del_step` from
  `Refine.del_refinedBy`), with `applyChanges` and `rootHash` themselves. Premises: `Sha256CR` and
  `KeepsFW` (applied changes keep the witness revealed and well-formed: a spec property, open);
  `NodeSerInj` is discharged by `SerInj.nodeSerInj`.
* `FieldVer` — the version constraints at field level: a `VER` publisher of an old node hashed it
  (`br_vm_gsha`, `sn_vm_gsha`) under its digest with digest children (`br_gsha_dig`,
  `br_gsha_isn`, `sn_gsha_dig`); a publisher of a new node has one (`*_vmn_gnew`); a version id is
  the row's own (`br_vid`, `sn_vid`); a continued key never uses `VER` (`sn_cont`).
* `StepsBV` — `br_upsert_value`, `br_del_value_keep`, `br_del_value_absent` (the spec steps of
  `oUV`, `oDV`, `oDZ`).
* `SerInj` (Lean sub-lane) — **`nodeSerInj : NodeSerInj` proved** from the spec's encoder (tag
  byte; `u16`/`u32`/`u64` injective under `wf`'s bounds, `leN_inj`; `hexPrefix_inj`,
  `packNibbles_inj`; bitmap + 32-byte child hashes slot by slot, `kids_inj`; a `ValueRef` pins the
  slot, `slot_of_valueRef`). `Shallow` now also requires value slots to be refs (a row holds a
  `ValueRef`; with a revealed row value the statement is false). `refinedBy_of_hash'` needs only
  `Sha256CR`.
* `Refine` (sub-lane) — **`del_refinedBy`**: `del` commutes with refinement for the general spec
  `del` (same deleted flag, refining result; via `squashBranch_refinedBy`,
  `extendChild_refinedBy`), `dchain_witness`, `change_del_witness`, `findRef_refinedBy`;
  **`rows_refinedBy`**: a well-formed rows' trie with ref slots and the root hash of a revealed
  well-formed trie refines it (`nodeSerInj` at every node, `Sha256CR` only); `find_spec`,
  `upsert_spec`, `del_spec` against any spec partial trie.
* `FieldRows2` (sub-lane) — `sn_hexPrefix`: a short-key `SN` row's `hp` bytes are exactly
  `hexPrefix` of its `klen` nibbles and `hplen = 1 + klen/2` (from the `a`/`k`/`ha`/`hp`/`odd`
  constraints, nibbles < 16); `br_sel`: a descending `BR` row has one selector, at a present slot,
  equal to the looked-up nibble.

### Open after M5a-2

1. Bus level: that the rows' `VER`/`DOWN`/`UP` traffic yields `Rv`, the chain relations and
   `Exp` (with `FieldVer` + `rid` = row index giving unique ids, the `VER` receives are a function
   of the ref) and the field facts building `wf` / ref slots of the rows' trie; `KeepsFW`; chain
   constructors for `oUV`/`oDV`/`oDZ`; field level: `BR` children block from `rank`, the other
   one-hot bundles, `cont` rows / `SNC`, `WS*`.
2. Completeness still missing: the squash after a value delete leaving one child, squash to a
   value leaf / onto an extension or branch sibling (`extendChild [i]` with a non-leaf), splits
   where one key ends at the new branch, a mismatch past a head's 63 nibbles, the empty trie.

## Result on T1 (`d3c8/d3/02-h10196-s3`)

| | |
|---|---|
| state accesses | 17 working-set keys (the clean-room checker's lookups ∪ the committed keys), 10 committed changes (7 upserts, 3 deletes), cross-checked against the Lean `allFeatures --emit-full` write log (`lean_matches_clean_room: true`) [M] |
| trace | 156 trie-node rows (`BR` 96, `SN` 60), 229 SHA-256 messages / 541 blocks, 270 SHA-512 compressions, 171 `KEY` rows, 51 `KCMP` rows [M] |
| precheck | every constraint on every row, every bus balanced (30,591 distinct messages) [M] |
| proof | **verifies** on the main stack (unified SWIRL, BabyBear Ext12, SHA-384 MMCS, 42-B digests, stacked WHIR): 1,243,380 B, 268.2-bit calculator, prove 193.3 s on 8 threads, native verify 93 ms, peak RSS 1.81 GB [M] (`logs/prove.log`) |
| root equality | the circuit's post-state root (the `TCH` chain's last root, closed by the public tape) = `1db48e38…249628` = the Lean run's `stateRoot` = the main transition's `post_state_root` (T1 has no implicit transitions, so it is also the header's `prev_state_root`) [M] |
| mutants | 4/4 rejected [M] (`logs/mut-*.log`): **node** (the first written key's leaf with memory usage + 1, parent's child hash unchanged) → `DOWN` (hash link) and `TCH` unbalanced; **prevalue** (one key's claimed pre-value length + 1) → `UP` (INTAKE answer) unbalanced; **omitwrite** (one write access dropped) → `RCH`, `WRITE` and 224 SHA-512 interface messages unbalanced; **postroot** (statement's post-state root, one bit) → `TCH` unbalanced. Each was then handed to the prover, which refuses (non-zero LogUp sum) |

The pre-state root is `9da2fa38…0d4c3f70`.

## What the AIR is

The AIR is a `ZkFormal.Air` value in Lean (`lean/StateM5a/{Trie,Ws,Air}.lean`), exported by
`m5a-tool air D` and interpreted unchanged by the prover (the pq-state-port interpreter).
Tables (width / constraints incl. the generated multiplicity-bit booleanity / interactions):

| table | rows | role | w / c / i |
|---|---|---|---|
| `SHA` | per block | the unchanged SHA-256 block table (`ZkFormal.Sha.Table`, soundness `sha_digest_contract_closed`) | 544 / 1028 / 17 |
| `KEY` | per key byte | key bytes → SHA-256 (the key digest the working set binds) and the `NIB(kid, idx, nibble)` / `KLEN` lookups | 63 / 59 / 6 |
| `BR` | per branch visited | old branch (16 slots, value ref, memory) → old serialization + digest; op (8 kinds, below); rewritten branch → new serialization + digest; 4×16-bit memory chain | 795 / 1331 / 1130 |
| `SN` | per leaf / extension visited | key as ≤ 64 nibbles (looked up in `KEY`), `hexPrefix` bytes, old/new serialization; 8 ops | 419 / 664 / 303 |
| `KCMP` | per common-prefix nibble | `ORD(ka, kb)`: key `a` < key `b` | 14 / 26 / 6 |
| `WSB` | 2^(D+1) | the working-set leaves, phase 0 (INTAKE) and phase 1 (FINAL); leaf digest = 2 SHA-512 compressions; INTAKE find walk per key; FINAL change walk per written key, chaining the trie root | 151 / 152 / 41 |
| `WSN` | 2·(2^D − 1) | inner nodes, SHA-384(`left48‖right48`) | 67 / 27 / 21 |
| `WSA` | per write access | old leaf → new leaf on one depth-`D` path (`4 + 2D` compressions), advancing the `RCH` root chain | 518 / 254 / 227 |
| `SHA512`, `SHA512T` | 128 per compression | the native SHA-512 compression chip v4 (`native/sha384-air4`, bus ids moved to 100–103) | 83 / – / – |
| `TAPE` | public | the write log `WRITE(kd, ref)` and the root chain's ends `TCH(0, prev_state_root)`, `TCH(n, post_state_root)` | – |

Walk protocol: a walk is one spec trie operation along one key (`w` = leaf index for INTAKE
finds, `2^20 + index` for FINAL changes). The parent sends `DOWN(w, d, childHash, kid, mode,
value)`; the child row must hash to `childHash` (it receives its own digest from `SHA`); it returns
`UP(w, d, kind, newHash, newMem, oldMem, leaf descriptor, find answer)`. Result kinds: find answer,
hashed node (upsert), hashed branch (delete), leaf descriptor (delete: a leaf whose key grows by
`extendChild` on the way up, materialized by `SN.oLM` where a branch embeds it), nothing.

Ops implemented (T1 uses the first set, T2 all of them): `BR` find-descend / find-absent (empty
slot) / upsert-descend / upsert-new-leaf / delete-descend with the branch kept (child hashed, leaf
descriptor, child removed) / delete with one sibling leaf left (`squashBranch` → `extendChild`);
`SN` leaf find / replace / delete / sibling read / materialize, extension find / upsert / delete
with a leaf-descriptor child.  **Added for T2 (second session):** `BR.oFV` find ending at a branch
(answers its value; `KLEN` proves the key ends), `BR.oDA`/`oDS` absent delete at an empty slot /
below an unchanged child, `BR.oSL` a split's new branch (two children: the walk's new leaf and the
old-side child); `SN.oLA`/`oEA` absent finds and `oLZ`/`oEZ` absent deletes at a leaf / extension
with another key, `SN.oES` delete below an unchanged child, `SN.oEB` delete whose child is a kept
branch (`extendChild k (branch …)`, the squash onto a branch), `SN.oLX`/`oEX` upsert splits
(`splitLeaf`/`splitExt`, both keys continuing past the common prefix), `SN.oEP` the new extension
over the common prefix (`wrapExt`), `SN.oEM` the re-keyed extension `xs ↦ c`.

An absent / split row carries a **mismatch witness**: the nibbles before `jm` are looked up against
the walk key, and at `jm` the walk key holds another nibble (`mN`, inverse of `y − kj`), ends (`mK`,
`KLEN`) or continues past a leaf's key (`mL`).  Nibbles no key lookup covers are range-checked by
the new 256-row `RNG` table (`v` and `v + 240` in `[0, 256)`); split rows look them up against a
second key `kid2` (the old leaf's full key, or the extension's path padded to bytes, registered in
`KEY`).  A new result kind `SAME` (`del` returned `deleted = false`) carries the node's own hash,
so the root chain `TCH` repeats the root on an absent delete.  **Long keys:** a continued `SN` head
(`cont`) holds `62 + odd` nibbles, and `SNC` rows carry 64 nibbles each (chained by `KC`/`KCR`),
sending `hexPrefix` bytes `32c … 32c+31` (`Layout.hpAt_chunk`).  New buses `SPQ`/`SPR`/`EPQ`/`SXQ`/
`SXR` (splits), `KC`/`KCR` (chains), `RNG`; `MATR` now carries the key id (a split materializes two
leaves at one depth).  Not in the menu (completeness gaps, never soundness): splits where one key
ends at the new branch, upsert/delete at a branch value, squash to a value leaf or onto an
extension sibling, a mismatch past the head's first 63 nibbles, the empty trie.

Working set: leaf = `(sha256 key, pre (present, len, sha256 value), cur (…), written)` in 16-bit
fields; FINAL walks run in leaf order, which `KCMP` makes the spec's raw-key order (`sortKV`), so
the circuit applies `applyChanges` in the spec's order. In M5a the writes come from the public
tape (stand-in for M5b's STATE rows) and the per-segment state is the `RCH` root (a boundary
would carry it).

## Lean lemmas ([K], `lean/StateM5a/`, `lake build StateM5a` prints the axiom audit)

Every theorem depends on at most `propext`, `Classical.choice`, `Quot.sound`; no `sorry`.

| AIR | lemma | spec function it links to |
|---|---|---|
| `BR` | `Steps.br_findRef`, `br_upsert_descend`, `br_upsert_new`, `br_del_keep` (+ `squashBranch_keep`), `br_del_one` | `PTrie.findRef`, `PTrie.upsert`, `PTrie.del`, `squashBranch`, `extendChild` (via `Kids.at`/`Kids.put`: `kids_findRef_at`, `kids_upsert_at`, `kids_delAt_at`) |
| `BR` | `Layout.kidsBitmap_eq`, `hashes_eq`, `block_at` | `PTrie.hashOf (.branch …)`'s bitmap and children block = the row's `Σ f_i 2^i` and slot `i` at offset `32·rank_i` |
| `SN` | `Steps.leaf_findRef`, `leaf_upsert`, `leaf_del`, `leafMem_eq`, `ext_findRef`, `ext_upsert`, `ext_del_leaf` | the leaf / extension cases of the same functions |
| `SN` | `Layout.hexPrefix_eq` | `hexPrefix k leaf` = the row's `hp_m` formula, `1 + |k|/2` bytes |
| `KCMP` | `Order.nibLt_bytesLt` | `bytesLt` (the order of `sortKV`, hence of `Ovl.finalize`) |
| `WSA` / `WSN` | `Merkle.write_access_sound` | the working-set root after a write = the root of the leaf list with that leaf replaced (collision-free `H`) |
| FINAL root | `Steps.applyChange_upsert`, `applyChange_del` | `applyChange` (one committed change of `applyChanges`) |
| `KEY` | `KeyField.key_row_nibbles` — **field level**: from `Key.table`'s constraints vanishing over BabyBear on a row, the row's `NIB` nibbles are `NearSpec.nibbles` of the byte it hashes | `NearSpec.nibbles` |
| T2 rows | `StepsT2.br_findValue`, `br_del_absent`, `br_del_same`, `leaf_findRef_absent`, `leaf_del_absent`, `ext_findRef_absent`, `ext_del_absent`, `ext_del_same`, `ext_del_branch`, `leaf_split`, `ext_split`, `wrapExt_cons`, `kids2_at`; mismatch witness `ne_of_mismatch`, `not_isPrefix_of_mismatch` (`k[jm]? ≠ key[jm]?`) | the new cases of `findRef`/`upsert`/`del`, `splitLeaf`, `splitExt`, `extendChild` |
| `SNC` | `Layout.hpAt_chunk` | `hexPrefix` byte `32c + m` = the nibble pair at key offset `64c − 2 + odd + 2m` |
| `KCMP` / `SN` / `BR` / chains | **field level** (`FieldRows`): `kcmp_fin_lt` (`xb − xa − 1 = Σ 2^t db_t` ⇒ `xa < xb`), `sn_mismatch_ne` (`mN = 1` ⇒ `y ≠ kj`), `br_keep` (kept branch ⇒ `Σ nf ≥ 1`, and `≥ 2` without a value), `memChain_sound` (the 16-bit limb chain ⇒ the exact `nw + minus = m + plus`), `onehot_of_sum` | the premises of `Order.nibLt_bytesLt`, `ne_of_mismatch`, `squashBranch_keep`; the memory arithmetic of the step lemmas |
| walks | `Walk.fchain_sound`, `uchain_sound`, `dchain_sound`, `change_upsert`, `change_del`: a chain of row steps (`FChain`/`UChain`/`DChain`, one constructor per row op) is `findRef`/`upsert`/`del`/`applyChange` on the trie the rows reveal; `fchain_witness`, `uchain_witness`: the same answer (slot up to `SlotRefines`) and the same new root hash on any trie the rows' trie refines; `refinedBy_of_hash` (premises `Sha256CR`, `NodeSerInj`) | `PTrie.upsert_refinedBy`, `hashOf_refinedBy` |

What these do not yet give (open, [S]): (1) field level: done for `KEY` (nibbles), `KCMP` (order),
`SN` (mismatch), `BR` (keep condition) and the `BR`/`SN` memory chains; open: the `SN` key /
`hexPrefix` layout from its 64-term sums (`hexPrefix_eq` is record level), the `BR` children-block
placement from `rank`, the per-op one-hot bundles (helper `onehot_of_sum`), `SNC`, `WS*`, and the
bus-level step (`DOWN`/`UP` balance ⇒ the chain constructors); (2) walk composition: proved on the
rows' trie and carried to the witness trie for finds and upserts given `t₁.refinedBy t₂`; open:
that refinement for the whole rows' trie (an induction along the chain from `refinedBy_of_hash`),
`NodeSerInj` itself (decode ∘ encode of the node preimage: stated, not proved), and
`del_refinedBy` (deletes are proved on the rows' trie only); (3) the SHA-512 chip's interface
soundness (`FAITHFUL-v4.md`, not Lean) used by `write_access_sound`'s `H`.  `Sha256CR` / `Sha384CR`
are definitions taken as premises, never axioms.

## Cost [M] (`cost.py`, `logs/T1-cost.json`; committed cells, before power-of-two padding)

| item | cells |
|---|---|
| per trie-node row, mean | 32,453 (`BR` 42,009 incl. SHA-256 of old + new node; `SN` 17,165) |
| per INTAKE find (T1: 17 walks, 93 rows, 23,671 cells/row) | 129,495 (old nodes only) |
| per FINAL change (T1: 10 walks, 63 rows incl. sibling/materialize, 45,417 cells/row) | 286,132 (old + new nodes) |
| per working-set key | 10,468 (`KEY` + `KCMP`) + 43,064 (`WSB`: two leaf digests, both phases) |
| per write access (`WSA`, D = 5) | 149,254 (14 SHA-512 compressions + the row) |
| tree build (`WSN`, D = 5, both phases) | 662,842 |
| T1 total used | 8.13 M (padded and committed: 14.52 M; the SHA-256 table pads 9,426 rows to 2^14, the SHA-512 chip 34,560 to 2^16) |

The SHA-256 node hashing dominates: a 16-child branch is 523 bytes = 9 blocks = 83 k cells per
message, and FINAL rehashes the shared upper path once per change (nearcore batches the changes;
doing the same — one rewrite per touched node — roughly halves FINAL).

## Commands

```sh
research/near-compression/e2e-general/m5a/run.sh <case dir> <out dir> [check|prove|mutants]   # D=5 (T1)
D=6 research/near-compression/e2e-general/m5a/run.sh <T2 case dir> <out dir> prove              # T2
python3 research/near-compression/e2e-general/m5a/batch_cost.py <out>/state.json <out>/dump <out>/names.json
# M5a-2: synthetic branch-value case (D=4); the spec oracle alone: m5a-tool apply <state.json>
python3 research/near-compression/e2e-general/m5a/synth.py bval <out>/state.json
D=4 research/near-compression/e2e-general/m5a/run.sh - <out> prove
UNBATCHED=1 …/run.sh <case> <out> check     # the M5a (every node hashed) trace, still valid
```

1. `nearspec-v3-check-successor --tier allFeatures --emit-full` (the Lean write log) and
   `extract_state.py` (the clean-room checker's nodes, lookups and committed overlay, cross-checked
   against the Lean log);
2. `lake build m5a-tool` + `m5a-tool air D` (the AIR and its column names);
3. `tracegen.py` (the spec recursions of `ptrie.py`, a transcription of `PTrie.findRef`/`upsert`/
   `del`/`applyChanges`; it asserts the post-state root against both the transcription and the
   checker before writing anything);
4. `prover/` (`cargo build --release`), `check | prove | mutant`.

Builds: Lean from `.lake` copied from the main checkout; cargo into
`/data/illia/nearproof-deps/e2e-m5a/target` from an own copy of the pq-state-port backend tree
(overlay hash `051a037b…`). One deviation from pq-state-port: the per-table `maxLog` cap hook
(`max_log_trace_height`) does not exist in this backend tree and is not passed to keygen (the trace
generator respects every cap). Binary hashes: `logs/SHA256SUMS` (first session), `logs/SHA256SUMS-v2`
(second session; the T2 proof).

## Result on T2 (`d3c9/d3/00-h10018-s0`) — second session, 2026-11-03

| | |
|---|---|
| state accesses | 52 working-set keys (D = 6), 42 committed changes; Lean write log = clean-room overlay [M] |
| spec cases | finds: 10 absent at a leaf, 8 absent at an extension, 1 ending at a branch value; upserts: 8 `splitLeaf`, 1 `splitExt`, 13 new leaves; deletes: 2 absent at a leaf, 1 absent at an empty slot, 1 extension over a kept branch (`extendChild k (branch …)`), 2 `squashBranch` → leaf descriptors; keys of 74, 76, 78, 80 and 90 nibbles (24 `SNC` continuation rows) [M] |
| trace | 623 trie-node rows (`BR` 376, `SN` 247), 24 `SNC`, 929 SHA-256 messages / 2,425 blocks, 1,006 SHA-512 compressions, 1,127 `KEY`, 498 `KCMP`; ops census in `logs/T2-stats.json` [M] |
| precheck | every constraint on every row, every bus balanced (140,241 distinct messages) [M] |
| proof | **verifies** on the main stack: 1,533,468 B, 268.2-bit calculator, verify 158 ms, peak RSS 16.4 GB; prove 4,392 s on 8 threads — the shared `zkbuild.slice` sat at its 40 GiB memory-high mark (sibling replays) and throttled the prover to ~1.3 cores, so this time is not representative (T1: 193 s at 14.5 M cells; T2 is 47.3 M) [M] (`logs/T2-prove.log`) |
| root equality | the circuit's post-state root (`TCH`'s last root, closed by the public tape) = `61f5330a…07993006` = the Lean run's `stateRoot` = the transcription's `applyChanges` root (asserted by `tracegen.py` before writing) [M] |
| mutants | **12/12 rejected** [M] (`logs/T2-mutants.txt`): the four statement-level mutants of T1 (node → `DOWN`/`TCH`, prevalue → `UP`, omitwrite → `RCH`/`WRITE`/SHA-512 interface, postroot → `TCH`) and one tampered row per new row type: `absent` (a present-key leaf find recast as absent with a fake mismatch) and `extabsent` (one more matching nibble claimed) → mismatch constraints; `branchval` (`oFV` answers "no value") → value-zero constraint; `split` (old-side child moved to another slot) → `NIB` and SHA-256 byte buses; `splitext` (`cm` + 1) → the `xm` constraint; `absdel` (mismatch where the nibbles agree) → the inverse constraint; `squash` (`oEB` memory + 1) → the memory chain; `chain` (an `SNC` nibble changed, its hp byte adjusted) → `NIB`/`RNG`/SHA-256 bytes. Each is then refused by the prover (~30 s) |

T1 on the extended AIR: the same 156 rows, precheck OK (the new tables are idle there).

### FINAL batching (nearcore's order): measured model, not yet the AIR

`batch_cost.py` (`logs/T{1,2}-batch.json`) counts the SHA-256 work of FINAL as proved now (every
change walk hashes the old and the rewritten node of every row) against nearcore's `Trie::update`
order, which is also the spec's (`PTrie.upsert`/`del` never hash; only `rootHash` of the final trie
does): apply the sorted changes to the in-memory trie, then hash each touched pre-state node once
(authentication) and each node of the final trie once.  Exact counts on the chunk [M]:

| | now (cells) | batched (cells) | saving | batched, reusing INTAKE's pre-node digests |
|---|---|---|---|---|
| T1 | 2,820,640 (119 msgs) | 1,502,528 (40 open + 36 final) | **46.7 %** | 713,184 (74.7 %) |
| T2 | 14,642,848 (584 msgs) | 2,650,368 (58 open + 88 final) | **81.9 %** | 1,555,296 (89.4 %) |

Every pre-state node a change walk reads is also on an INTAKE find path (the written keys are in
the working set), so with digest reuse only the final trie is hashed.  Of T2's 34.2 M used cells
(`cost.py`) FINAL hashing is 14.6 M; batching takes ~12 M off (35 % of the total).  The AIR change
this needs is in *Next steps* (an offline-memory node store instead of hash-addressed versions).

## Next steps (as of the second session; items 1–3 are done or superseded by M5a-2 above)

1. **Batched FINAL in the AIR** (the model above; done in M5a-2 with immutable versions instead of timestamps).  Per-change walk rows stay (narrow, no SHA) but
   address in-memory nodes by id through a node store bus `NODE(nid, t, record)` with timestamps
   (`t` = change index; read `t_r < t`, write `t`; Blum/Spice offline memory checking), records
   holding keys as `(kid, start, len)` references into `KEY` and children as hash-or-nid slots.
   `OPEN` rows hash a pre-state node once (or take its digest from the INTAKE walk that hashed it)
   and create its record; `FIN` rows hash each final node once, children first (`HASH(nid, h)`),
   the root's hash closing `TCH`.  Nid freshness from `(change, depth)`; key equality across
   records by `KCMP`-style segment rows.  Lean: the chain lemmas of `Walk` stay, the memory argument
   replaces the hash link for in-memory nodes.
2. **Lean**: `NodeSerInj` (decode ∘ encode of `PTrie.hashOf`'s preimage), the refinement of the
   whole rows' trie from `refinedBy_of_hash` along a chain, `del_refinedBy`; field-level `SN`
   key/`hexPrefix` layout, `BR` children block, the op one-hot bundles, `SNC`, `WS*`; then the
   bus-level step from `DOWN`/`UP` balance to the chain constructors.
3. Completeness gaps: splits where one key ends at the new branch (`oldEnds`/`newEnds`),
   upsert/delete at a branch value, squash to a value leaf / onto an extension sibling, a mismatch
   past the head's 63 nibbles, the empty trie.
4. M5b replaces the public `WRITE` tape by STATE rows and cuts segments at the `RCH` root.  The
   state-side boundary stays `(RCH root, TCH root, change index)`; it maps onto lane E's `stRoot`
   field of §3.2 once §3.5's `CM` boundary record is published (not yet on main).
