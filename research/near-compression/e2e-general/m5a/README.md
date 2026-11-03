# E2E milestone M5a: INTAKE, working-set tree and FINAL in-circuit (state lane B)

Plan: `docs/zk-formal/E2E-GENERAL-CHUNK-PLAN.md` §3.2 (the `stRoot` working set), §4 (M5a).
Date 2026-11-03. Labels: **[M]** measured here, **[K]** kernel-checked Lean (std axioms),
**[S]** stated / design only.

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

## Next steps

1. **Batched FINAL in the AIR** (the model above).  Per-change walk rows stay (narrow, no SHA) but
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
