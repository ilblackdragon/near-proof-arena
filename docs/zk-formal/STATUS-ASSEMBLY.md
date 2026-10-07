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
