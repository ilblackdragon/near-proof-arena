# Native receipt-leaf reconstruction

**Correction:** the original hash-template metadata guards were underconstrained.
Use the [corrected NPSTRICT circuit and evidence](STRICT_METADATA.md); historical
measurements below do not certify the intended metadata relation.

2026-10-24. Hash/outcome-tree component; full NEAR and PQ recursion remain open.

The proof now authenticates private SHA jobs other than D0a receipt leaves and
internal outcome-tree nodes. Public receipt IDs pair with consecutive proven PEO
records: `leaf_i = SHA256(LE32(2) || receipt_id_i || digest(PEO_i))`.
PEO IDs must be `3+16*i`, their digest flags enabled, and their count must equal
the receipt count. The verifier derives leaf IDs `4+16*i`, lengths 68 and flags 1,
then reconstructs internal nodes using the preceding native-tree implementation.
Supplied leaf/internal records are rejected. It restores the original full job
vector and checks its independently supplied expected root.

This is a deterministic verifier/prover tradeoff, not a new cryptographic primitive.
The external job root still needs a proved connection to the NEAR chunk claim.

| Case | Private SHA jobs | Native leaves / nodes | Actual packet |
|---|---:|---:|---:|
| 00-h10035-s3 | 833 | 814 / 813 | **266,607 B** |
| 00-h10012-s1 | 11 | 1 / 0 | **206,889 B** |

Capacity: 1,056 slots / 3,232 SHA blocks; witness log 20, column log 9, five
modulus limbs, left/opening commitments 4/11 polynomials, 36 norm bounds.
Warm readiness, alternating large/small twice: **0.844, 0.829, 0.863, 0.842 s**.
These include batch read and packet export, exclude original witness export, and
are four observations rather than p95. Cold circuit/setup adds 4.497 s; peak RSS
2,480,304 KiB. One CPU core, no GPU. The backend geometry changes: its 158,632-byte
serialization makes the packet larger than the preceding 225,985-byte variant,
despite fewer public records. The current large packet leaves only 33,393 bytes
below the 300,000-byte target; independent component packets cannot simply be
concatenated to obtain the required complete proof.

Independent Python fixtures match exact original-message data and roots for 64
real cases and five synthetic tree shapes. The Rust wire checker passes all 69
fixtures and 450 mutations. Four proving runs pass 24 proof/public/tape/norm
mutations. Backend scalar audits match 26 C/Python obligations, minimum modeled
quantum cost 140.185 bits; independently calculated initial norms match native
logs exactly. This excludes outer commitments, structured attacks, extraction,
Fiat–Shamir/QROM and recursive composition: **not a PQ128 security result**.
No prior outer estimate transfers automatically to this new geometry.

Fresh processes verify both serialized packets against the original independent
roots with no witness loaded and byte-identical backend re-encoding. Public-root
and tape mutations reject; exact timings are in `manifest.json`.

## Remaining work

Bind receipt IDs, PEO data, all other SHA records, byte buses and state transitions
to the actual chunk relation. Prove Wasm execution and predecessor/history
composition. Establish composed PQ security and representative end-to-end latency.
The native decoder remains a trusted-local research interface. Current evidence
covers D0a fixtures, not every NEAR receipt/transaction variant or held-out capacity.

## Reproduction

[evidence/non-leaf](evidence/non-leaf) records source, logs, hashes and audits.
Build `near-hash-non-leaf` and `near-leaf-wire-check` from the preserved sources
under `crates/binius/src/bin/` with the preceding isolated stronger backend and
outer policy. The proof's public dense vector has 50,712 bytes. `NPNOLEF2` is the
seven-section packet version; its public section is `NPNOLEF1`, record count,
41-byte records, receipt count, then 32-byte receipt IDs. Counts are little-endian
u32; records retain the preceding canonical bucket/ID ordering.

`make_leaf_fixtures.py CORPUS OUTPUT` generates independent wire/root fixtures;
`near-leaf-wire-check OUTPUT` checks reconstruction and mutations.
`audit_non_leaf.py PACKET FIXTURE ORIGINAL_ROOT --output REPORT` checks emitted
public bytes. `audit_sis_policy.py --profile non_leaf` selects this geometry,
including binary-vector rank 1,536 instead of 3,072.
