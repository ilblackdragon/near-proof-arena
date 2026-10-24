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

Follow-up: current Jolt independently measured 97,998/99,490 serialized bytes at
scale 18/20, 1.99/7.46 s proving. Decoded-object verification and one wire mutation
passed on a patched scale-18 rerun (2.32 s full process). Reusable hash template
now proves both large and small actual layouts without rebuilding: four proofs
ready in 1.67–1.74 s warm; 24 mutants reject; tighter-length gadget passes 44
checks. Cold construction/setup adds 12.84 s. Evidence and source linked above.

Next: canonical LaBinius wire codec and authenticated receipt/hash connection;
measure complete capacity-class pipeline. Keep full NEAR semantics, composed PQ
security and recursive history linkage as completion gates. Current CPU Jolt
whole-VM path is too slow even for a small hash workload; preserve it as a baseline.
