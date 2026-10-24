# Expose job records; prove only private work

**Correction:** the original hash-template metadata guards were underconstrained.
Use the [corrected NPSTRICT circuit and evidence](STRICT_METADATA.md); historical
measurements below do not certify the intended metadata relation.

2026-10-24. Component experiment, not a complete NEAR or PQ128 proof.

The hash proof now exposes `(id, length, digest-enabled, SHA256 digest)` records.
It removes the circuit's SHA512 hash over the 148,248-byte record vector. The
verifier hashes that public vector itself and compares it with the independently
supplied job-interface root. SHA256 of each private message remains constrained
inside the circuit. The relation is still bound to the same expected root; merely
accepting a root supplied alongside the proof would not bind it to a NEAR claim.

Public computations need not automatically become private proof work. This is an
ordinary verifier/prover tradeoff, not a new cryptographic primitive or novelty
claim. It also creates an explicit interface for receipt and state relations.

## Actual packet and timing evidence

The first dense wire format was 305,510 bytes, over budget. The final format sends
only active records in canonical bucket/ID order. It restores inactive empty
hashes and all header/padding words deterministically, reconstructing the exact
148,248-byte public vector supplied to the proof verifier. No proof checks or
record fields are discarded. Decoder rejects duplicate IDs, bad order, invalid
flags/lengths, excess capacity, truncation and trailing bytes.

| Workload | Active records | Public wire | Total packet |
|---|---:|---:|---:|
| 00-h10035-s3 | 2,460 | 100,872 B | **258,134 B** |
| 00-h10012-s1 | 12 | 504 B | **157,766 B** |

All headers, public records, opening sections and the backend are included.
The verifier also needs the expected job root and fixed circuit/setup policy,
as before. Private message bytes are not part of the public interface; this is
not a zero-knowledge claim. The native backend decoder remains trusted-local only.

Both packets verify in fresh processes against Python-derived expected roots,
with byte-identical backend re-encoding and root/tape mutations rejected. The
independent public-record audit reconstructs every source-message digest,
metadata value and inactive slot. Twelve codec/commitment boundary checks pass.
The final four-proof repetition passes 24 existing claim/tape/norm mutations;
its emitted bytes match the fresh-verified packets exactly.

Warm readiness observations (batch read through packet write):

- Dense transport, same public-vector circuit: 1.974 / 1.895 s.
- First compact run: **2.904 / 2.574 s**.
- Four alternating compact repetitions: **2.033 / 1.965 / 2.002 / 2.002 s**;
  median 2.0021 s. Cold circuit/setup ~10.55 s in this repeat.

The deadline is **not established**. File birth/modify times show our codec-test
build began after the slower compact proving run finished; it overlapped fresh
verification instead. The earlier suggestion that compilation explained the
proving slowdown was incorrect. Other host activity is uncontrolled. Repetition
ran after our build and fresh verifier completed, but is not representative p95.
Original NEAR witness-to-batch export remains excluded from these timings.

Five modulus limbs, bridge ranks 15/5/11, backend collision bounds and canonical
packing are unchanged. All 44 backend scalar model checks pass, minimum 143.895
bits across these two packets. All qualifications in OUTER_SECURITY.md remain:
this is not a composed security result, NEAR execution proof or history recursion.

## Next concrete reduction: public outcome-tree work

The large case's records contain 814 receipt-leaf hashes and 813 internal
outcome-Merkle nodes. The latter preimages are exactly pairs of public child
digests. Odd nodes are promoted unchanged, never duplicated and rehashed.
`collect.rs::merkle_jobs` assigns `id = 6 + 16 * (qBase + index)` in level order.
An independent implementation in [audit_public_merkle.py](audit_public_merkle.py)
reconstructs all internal preimages/IDs/digests from leaf digests alone and matches
**all 64 D0a cases**, including their enabled-digest flags.

This supports a next experiment: prove private non-Merkle SHA jobs, then have the
native verifier reconstruct and hash the public outcome tree. It must authenticate
the leaf digests with the proof, enforce consecutive leaf IDs, derive the exact
node set and bind the combined record root to the expected statement. Omitting
both sides of an interaction must not bypass completeness. The corpus check alone
is not that composed proof.

Removing internal Merkle jobs reduces the candidate fixed capacity from 7,296 to
**5,248 SHA blocks**, with the two-block bucket shrinking from 2,048 to 1,024 slots.
All 64 cases fit this candidate; held-out capacity is untested. The large case
would remove 1,626 actual SHA compressions and 813 transmitted records before any
further backend-size effect. No proving speedup is claimed until measured.

D1 transaction/outcome leaves and later NEAR variants require their own semantics.
The other SHA bin, receipt byte buses, state binding, Wasm execution and recursive
history are still required. The expected interface root is not yet linked by a
proof to the final NEAR chunk claim.

## Reproduction

[evidence/public-events](evidence/public-events) contains source, failed dense
size screen, timing variation, codec checks, fresh verification, independent
record audits and corpus tree reconstruction. Build `near-hash-events` on the
preceding five-limb backend/outer-policy source; copy the support modules to the
paths in its source. `NPEVENT2` is the new packet format; its first section is
`NPEVTS01 || count_u32_le || (id_u32_le,len_u32_le,flag_u8,digest32)*`.
The circuit sees the reconstructed dense big-endian word vector. Versioned wire
formats must not be confused with the earlier root-only proofs.
