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
- Build concrete extracted witness semantics / encoder coherence for the reverse
  direction. `ExtV3`, `GoodV3`, `witnessOfV3`, `FactorSoundStmt` and
  `FactorCompleteStmt` are design interfaces, not implemented declarations in this
  snapshot. Existing per-table semantics must be connected without adding them as
  unsupported assumptions.
- Equal source keys implying equal roots needs an explicit connection to hash
  binding / collision events; do not silently assume SHA-256 injectivity.

The D3 logged read-set reference is a separate worktree and validation lane. Its
native/worker/formal checks do not discharge any succinct proof admission gap.
