# Native / AIR semantic assembly checkpoint

2026-10-07. Candidate-owned proofs in `ZkFormal/NearV3/Assembly/`; no frozen
specification or challenge changes. Worktree `lane/v3-assembly` starts at AIR
`7aba6ec8`. This is partial semantic factoring, not a final succinct certificate.

Completed and elaborated:

- `Scheduler.schedStep_iff`: the exact runtime step is equivalent to the actual
  previous-value read, native `schedPub`, successful `runCore`, output projection,
  and trie upsert. Main and implicit runtime success each imply `schedPub` success.
- `PrepFacts.prepD0_roots`, `prepD0_source_roots`, `prepD0_sched_count`: successful
  native preprocessing guarantees all three header roots and every source root
  have 32 bytes, and scheduler count is exactly `K + 1`. Source widths are carried
  through the real nested loops and seeded shuffle, not assumed at the boundary.
- `Compute.applyNewChunk_compute_guard`, `applyNewChunk_gas`,
  `applyNewChunk_receipt_bound`: execution implies the exact native compute guard,
  `gasUsed = receipt_count * G`, and at most 4481 receipts under A1.
- `Forward.applyNewChunk_fwdGasOk`, `applyNewChunk_status_guard`: successful main
  execution implies both the native gas-only forwarding check and destination
  membership check. The proof reconstructs the outgoing stream across system and
  ordinary receipts, then simulates the complete runtime forwarding fold.

Bounded serial Lean diagnostics pass against the AIR dependency cache, using the
shared build lock and 16 GiB / two Lean threads. Thirteen top-level transitive
axiom audits use only `propext`, `Quot.sound`, and (source shuffle only)
`Classical.choice`. Logs are `/tmp/nearproof-assembly-*-audit.log`.

Remaining semantic work:

- Connect successful `checkD0a` to one coherent decoded walk, applied source lists,
  main execution and implicit executions; derive successful `prepClaim` and the
  concrete honest hint, rather than assuming preprocessing success.
- Prove forwarding size-demand totals are bounded by the actual scheduler grants,
  then obtain native `< 2^24` demand guards from the existing scheduler bound.
- Lift the existing refund codec theorem through decoded source receipts so the
  native body's refund list equals execution's outgoing stream.
- Construct extracted views from accepted raw witnesses, preserving authenticated
  stores, source dictionaries and exact execution. The executable `ExtV3` /
  `witnessOfV3` and semantic `GoodV3` interfaces are implemented below.
- Derive `GoodV3` from the checked AIR tables, including store/root coherence and
  the actual main and implicit execution semantics.

The D3 logged read-set reference is a separate worktree and validation lane. Its
native/worker/formal checks do not discharge any succinct proof admission gap.

## Semantic assembly interface (2026-10-07)

`Assembly.Witness` now defines `ExtV3` from actual node/value/head, receipt and
source path views and computes `stateWitnessOfV3` / `witnessOfV3`. Ordered source
dictionaries preserve explicit unused fillers; no source lookup may select a
filler in `SourceSemanticsV3`. Main and implicit stores come from the existing
`Link3` record interpretation. Ignored transition hashes are canonical zeros.

`Assembly.Execution` separates exact main runtime execution and chronological
implicit execution. The queue-stage theorem uses the actual successful run;
authenticated pre-state queue reads additionally require the explicit `pre.wf`
premise from `Qv.ReceiptPreserve`. That premise has not been silently discharged.

`Assembly.Good` combines ordinary source selection/Merkle checks/shuffle,
cardinality, exact runtime, header/body comparisons and domain/codec bounds.
It contains no `checkD0` or `RelD0a` field. It proves decoding of reconstructed
bytes and all five frozen D0a amendments. Modular elaboration and four transitive
axiom audits pass (only `propext`, `Classical.choice`, `Quot.sound`).

`Assembly.FactorSound.factorSound` now proves the actual `FactorSound` statement:
`GoodV3` implies the unchanged `checkD0a` accepts the concrete encoded
`witnessOfV3`. It composes actual decoder round trips, `prepD0_guards`, exact
source-loop execution, main execution, implicit-loop execution, endorsed header
comparisons and all five amendments. No checker-success field or equivalence
premise was added to `GoodV3`. All three new transitive axiom audits pass using
only `propext`, `Classical.choice`, and `Quot.sound`.

Supporting checked modules now include:

- `ClaimFacts`: native preprocessing supplies all claim and chain-prefix guards.
- `PreparedSources`: actual preprocessing's source lists equal the candidate's
  exact nested-loop/shuffle computation.
- `SourceComplete`: authenticated source selection and successful shuffles yield
  the exact native applied receipts and source occurrence count.
- `ImplicitComplete`: the chronological semantic run yields the exact native
  zipped implicit-transition loop.
- `SourceResult`: successful native checking implies the actual applied receipt
  IDs are pairwise distinct. Receipt candidate modules consume this fact to
  derive repeated-key empty lists, including the first occurrence.

`FactorComplete` remains OPEN. The occurrence-tree view allocator reconstructs
the original trie but may expand a compact shared store. For arbitrary `B`, the
unfolded-byte A7 bound does not imply the reconstructed encoded witness is at
most 8 MiB. Original-record reuse or a proved nonexpanding allocation is required;
this cap cannot be silently assumed. Successful `prepClaim` / an honest hint,
exact root/store/runtime view construction, AIR-to-`GoodV3`, source capacity,
and global rendering remain separate obligations. This checkpoint is semantic
sound factoring, not an admitted succinct replacement.

## Nonexpanding transition-store construction

`Assembly.StoreNormal` proves stable first-occurrence byte dedup preserves the
actual native `storeGet` and every `partialTrie` computation, including stores
with interleaved digest collisions. It does not use SHA injectivity. The native
store is first-wins; the source receipt dictionary separately remains last-wins.

`ExtV3.rawStore` retains the original linked record interpretation;
`ExtV3.store` now serializes its stable byte dedup. `WitnessStore` proves exact
native trie equality before/after that encoder normalization. This collapses
both shared occurrence bytes and bytes serving as both a node and a value.
All existing Assembly modules, including FactorSound, recompile unchanged.

`normalStore_cost` charges the full vector encoding: four bytes for the vector
count and four plus payload length for each entry. From the existing unconditional
`StoreBuilt.built_spec` and occurrence `Found` lemmas, the deduplicated regenerated
store costs no more than the original store. No `StoreDag`/A6 premise, distinct
input digests, node/value separation, or desired size bound is assumed.
`TreeStore.treeStoreViews` is an executable single-instance constructor using
actual node/value view seeds; its native-store cost theorem composes these facts.
Its non-hash root and modular value-ID capacity premises remain explicit.

Seventeen transitive axiom guards and two collision-order regression guards pass
in `test/AuditStoreNormal.lean`; the three FactorSound guards pass again with the
normalized encoder. This closes the per-store duplication cost problem, not
FactorComplete: multi-instance allocation, exact runtime reconstruction and
whole-witness composition with the allocated views remain to be proved.

## Raw witness codec coverage

`CodecSize.decodeStateWitness_encodeSW_size` now derives
`(V3.encodeSW s).length ≤ raw.length` from actual successful
`decodeStateWitness raw = .ok s`, with no other premise. Account IDs, public
keys, D0 receipts, paths, dictionary entries, transitions and vectors have exact
encoding-consumption equalities. The header uses the actual minimum accepted
signature length (65 bytes), so longer accepted signature variants remain
covered. No canonical-input or forward round-trip assumption is used.

All thirteen transitive axiom guards in `test/AuditCodecSize.lean` pass with only
`propext`, `Classical.choice`, and `Quot.sound` (several use only the first and
last). This closes original decoded canonical witness coverage; composition
with changed transition stores and the full multi-instance view constructor
still remains separate FactorComplete work.

`WitnessSize` composes the decoded canonical bound with per-transition store
costs. Its executable `compactTransition` reconstructs the actual native
partial trie and serializes the deduplicated occurrence store.
`decodeStateWitness_compact_size` proves the resulting main and all implicit
transitions together remain within the original raw witness size; the only
additional premise is that supplied roots are 32 bytes. It does not assume a
serialized-size conclusion or A6. Seven more axiom guards pass.

This is a size theorem: replay equivalence of the reconstructed store, concrete
root/key choices from execution, and multi-instance view allocation remain
explicit and are not claimed by this compacting function.

`StoreReplay.normalStore_stored` proves every generated node and value is
available under actual native first-wins lookup. From native `built_spec`,
`partialTrie_normalStore_reads` proves replay preserves the authenticated root
and every requested determinate read, and is a hash-pruning of the original
partial trie. No SHA injectivity, A6, or store-size premise is required. Four
axiom guards pass. The theorem retains explicit read determinacy and does not
yet assert exact trie equality or whole-transition replay.

## Exact normalized-store replay

`ExactReplay.partialTrie_normalStore` now proves literal equality of native
partial tries rebuilt from normalized occurrence bytes, for the same root
and requested keys. Its only premise is the root's 32-byte width. Unlike the
earlier read theorem, it needs no determinacy premise. Missing/malformed
queried blobs are handled explicitly, not incorrectly counted as retained
occurrences. The general `buildFor_replay` combines target-store lookup
restriction with preservation of all originally revealed bytes.

All eight transitive axiom guards in `test/AuditExactReplay.lean` pass with
only standard Lean axioms. This closes same-key replay. Choosing roots/keys
from actual execution, the separate buffered-index first pass, multi-instance
view allocation, and assembling all GoodV3 fields remain FactorComplete work.

`RuntimeReplay` transports actual main and implicit executions through exact
store replay. The separate buffered-index first pass is now covered too:
actual successful `applyNewChunk` supplies pre-state buffered determinacy via
the checked Qv preservation theorem; `partialTrie_normalStore_singleton_find`
then equates both first-pass reads. No assumed first-pass equality or requested
key-subset condition is introduced. Four additional axiom guards pass.

`NativeMain.checkD0_native_main` extracts the actual main block, predecessor,
first-pass buffered shards, pre-trie, native run and post-root from successful
`checkD0`, aligned with independently successful claim/witness decoders.
`NativeValid.normalized` transports this result into `MainExecutionV3.Valid`
for views emitting the normalized store and the same applied receipts/post-root.
These are explicit view correspondence inputs, not assumed execution facts.
Both permanent axiom guards pass.

## Shared multi-instance allocation

`ForestViews.forestStoreViews` now allocates real NodeS3/ValE views for all
transition tries in one shared node/value address space. Checked node extraction
returns the offset occurrence records; checked value extraction returns exactly
each value's original instance, including across concatenated trees. The
combined `forestStoreViews_records` theorem requires ordinary tree wf and a
visible total value-ID capacity bound. It does not assume successful AIR checks.
Ten transitive axiom guards pass. Forest-wide Seg/fullTree/store reconstruction
and deriving native capacity remain open.
