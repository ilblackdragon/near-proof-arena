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

Export follow-up: complete hash-component exports are 165,950 bytes each, versus
~116 KB analytical. Fixed-width terminal coefficients suffice without entropy
coding. Independent structural reader consumes all fields and rejects six
malformed-framing cases. Native decoding and verification from bytes remain
unimplemented; do not promote the export to a verified proof claim. See
[codec evidence/gates](../../research/near-compression/tail-architecture/EXPORT_CODEC.md).

Decode follow-up: both 165,950-byte exports now verify in separate fresh processes
without witnesses, against Python-derived expected roots. Backend re-encoding is
byte-identical; wrong root/tape mutations reject (four checks). Decode ~0.06 ms,
verify ~0.65 s after cold setup. New packet-ready timing includes export/write:
1.672/1.728 s, and emitted packets match the independently verified ones exactly.
Decoder remains explicitly unsafe for untrusted metadata/RNS; arbitrary-input
hardening and statement-dependent dimensional checks are not established.
The first decode rejected legitimate tail kappa1=0; fixed the format check only.
Sources/logs: `evidence/import-codec` under the lane research directory.
Prioritize concrete PQ feasibility (16-byte C transcript/SHAKE128/AES128/lattice
sizing) before treating this as a full-system integration choice.

Security follow-up: parsed the exported backend's actual parameters and legacy
verifier bounds. Greyhound-reference scalar Euclidean SIS model estimates
92.485–117.925 quantum bits for all ten obligations; all pass the old gate.
Five regression checks and ten C/Python crosschecks pass. This rejects the
measured configuration as evidence of PQ128, not a demonstrated attack. Initial
commitment, outer PCS, structured attacks and QROM remain outside this screen.
Pinned sources/results: [security screen](../../research/near-compression/tail-architecture/SECURITY_SCREEN.md).
Next: justified bounds/parameter policy, regenerate real proofs, then test a
complete two-segment authenticated receipt/hash join. EVENT_PROTOCOL now defines
an execution-frontier hypothesis, completeness attacks and explicit cold/full/
online timing regimes. No recursion or novelty claim.
