# Prove private hashes; reconstruct the public outcome tree

2026-10-24. Implemented component, not a full NEAR or composed PQ128 proof.

The verifier reconstructs D0a internal outcome-Merkle nodes from proven leaf
hashes. It restores every removed record and checks the **same original complete
job root**, independently supplied. Odd nodes are promoted unchanged. Consecutive
leaf IDs, enabled digests and 68-byte leaf lengths are enforced; supplied internal
node records are rejected. This moves deterministic public computation across
the prover/verifier boundary without dropping it from the authenticated result.

| Case | Proven hashes | Native internal nodes | Actual packet |
|---|---:|---:|---:|
| 00-h10035-s3 | 1,647 | 813 | **225,985 B** |
| 00-h10012-s1 | 12 | 0 | **158,950 B** |

Packets include framing, compact public records, tape, openings, norms and backend.
Fixed setup and the independent expected job root remain verifier inputs.
Capacity is 2,064 message slots / 5,248 SHA blocks, down from 7,296 blocks.
The proof's public vector is 99,096 B; native reconstruction restores the original
148,248-byte vector before hashing its complete root.

Four alternating warm readiness observations on CPU 8: **1.517, 1.483, 1.506,
1.494 seconds** (original batch reading through export). Cold construction/setup
adds 9.208 seconds; original witness-to-batch export is excluded. Peak RSS was
4,305,412 KiB. No GPU measurement, held-out capacity test or p95 claim.

Fresh processes verify final large/small packets in 0.664/0.656 seconds against
original Python-derived roots, with no witness loaded and byte-identical backend
re-encoding. Root/tape mutations reject. Four proving runs pass 24 existing
mutations. Independent Python record audits restore every original source record.
The native wire checker passes 69 independent fixtures (64 real; 0/1/2/3/5 leaves)
and 208 mutation checks. The fixture generator was rerun successfully.

Backend scalar SIS audits pass all 44 C/Python checks, minimum modeled quantum
cost 144.955 bits. This is **not** a composed security estimate. Five modulus limbs
and stronger bridge/backend policy remain, but main ring rows fell from 1,024 to
512: the previous 176.49-bit main-ring estimate must not be reused unchanged.
Structured/CRT attacks, extraction factors, short challenges, QROM composition and
numeric norm-bound review remain open; see [outer security](OUTER_SECURITY.md).
The native decoder remains a trusted-local research interface.

## Next experiment and the broader hypothesis

All 64 fixtures satisfy `leaf = SHA256(LE32(2) || receipt_id || proven_PEO_digest)`
with consecutive leaf IDs and PEO ID exactly leaf ID minus one. Transmitting the
32-byte receipt ID allows native reconstruction of the leaf too. Candidate SHA
capacity falls further to **3,232 blocks**. This is audited source structure only;
the reduced proof is **not implemented or timed**. Pairing, completeness and the
same complete job root must remain enforced. See `leaf-link-census.json`.

The larger research hypothesis is to authenticate the smallest sufficient set of
execution events and let each consumer derive deterministic views. This extends
our reading of Jolt's representation/commitment co-design; neither public
computation nor event compression is claimed novel. A state-of-the-art claim
requires a sound, implemented composition and fair end-to-end measurements.

Crucially, the complete job root still lacks a proved link to the final NEAR chunk
claim. Other SHA jobs, receipt byte buses, state/Wasm execution, predecessor
binding and PQ history recursion remain. Transmitting this component every chunk
cannot replace a bounded recursive history accumulator. Any new composition must
prove that every emitted obligation is consumed exactly once and that receipt,
state and history boundaries refer to the same chunk. These are correctness
requirements, not optional optimization work.

## Reproduction

[evidence/non-merkle](evidence/non-merkle) preserves sources, logs, audits and
source/binary/packet hashes. Apply source files under LaBinius
`crates/binius/src/bin/` on the preceding public-event and stronger-policy source
checkpoints. Build `near-hash-non-merkle` and `near-merkle-wire-check`; use the same
isolated C backend. `NPNOMRK2` packets contain seven length-prefixed sections;
the first is `NPNOMRK1 || count_u32_le || (id_u32_le,len_u32_le,flag_u8,digest32)*`.

Generate independent fixtures with `make_merkle_fixtures.py CORPUS OUTPUT`, then
run `near-merkle-wire-check OUTPUT`. `audit_non_merkle.py PACKET SHA_R_JSON ROOT
--output REPORT` checks exact full-record/root restoration. Sources document the
fixed capacity policy and packet verifier arguments. Scratch artifacts live under
`/data/illia/pq-tail-architecture-20261024`; frozen executable is
`near-hash-non-merkle-frozen`.
