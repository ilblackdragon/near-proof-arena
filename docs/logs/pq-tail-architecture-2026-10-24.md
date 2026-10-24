# PQ tail architecture — 2026-10-24

Worktree `pq-tail-architecture`; goal still open: PQ recursive NEAR proof below
300,000 bytes, ready within 1–2 seconds of chunk. No main changes.

- [Event protocol](../../research/near-compression/tail-architecture/EVENT_PROTOCOL.md):
  prior-art-derived hypothesis; 3,120 algebra identities checked, no PCS claim.
- [Jolt screen](../../research/near-compression/tail-architecture/JOLT_SCREEN.md):
  current Akita path found and audited at source level. Benchmark workloads and
  security revisions differ from historical reports. Fat/thin LTO exceeded the
  16 GiB bound; CI-profile build proceeds with separate prover/CLI invocations.
- [Hash capacity](../../research/near-compression/tail-architecture/HASH_CAPACITY.md):
  all 64 D0a cases exported, no export failures. Largest receipt workload remains
  2,460 messages/5,875 blocks. Fixed bucket policy nominally 7,296 blocks; existing
  variable-length gadget's storage rounding would actually produce 10,384.
  Tighten with enforced bounds or measure that overhead explicitly.
- Actual hash-batch evidence/source is preserved under
  `research/near-compression/tail-architecture/evidence/actual-hash-batch`.
  Warm witness+prove median ~1.084 s; first proof ~10.143 s plus export ~0.261 s.
  Analytical size only, exact-layout setup, no receipt/hash bridge or recursion.

Next: finish independent Jolt run; then measure one reusable hash circuit on
different actual chunks. Keep full NEAR semantics, composed PQ security, actual
serialization and recursive history linkage as completion gates.
