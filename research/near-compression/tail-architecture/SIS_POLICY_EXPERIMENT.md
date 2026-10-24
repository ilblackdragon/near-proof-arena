# Measured backend policy upgrade

2026-10-24. Component experiment, **not full-system PQ128 certification**.
The hash template now produces 150,526-byte packets under a stronger diagnostic
backend parameter policy. Both packets verify in fresh processes against independent roots, with wrong
root/tape mutations rejected and byte-identical re-encoding; these results must not substitute for outer PCS,
transcript, structured-lattice or NEAR composition analysis.

## Change

Ported the reference scalar SIS estimator and revised source/target collision
bound from greyhound-reference `672e74100496f6ef698ba35e241cf7593e3d57af` into an
isolated copy of the measured LaBinius backend. Selection and verification now
use row widths, source norm bounds and target norm bounds. Source bounds are
passed through Dachshund, Chihuahua and subsequent LaBRADOR reductions. Existing
LaBinius digit-width safeguards remain. Other backend algorithms are unchanged.

The first selection pass used predicted norms directly. Large-case verification
passed; the small case correctly failed at 127.995 modeled bits. Selection now
allows twice the predicted target L2 norm (four times its squared norm), while
verification checks the actual bound at the unchanged 128-bit floor. This is
headroom, not a proof of universally reliable parameter selection. There is no
retry protocol or adaptive weakening of verification.

The two exported proofs have eight backend reduction levels, versus four in the
old measurement. More reductions shrink the terminal witness enough that the
serialized packet is smaller despite larger commitment ranks. These are internal
backend reductions, **not NEAR history recursion**.

## Serialization defect found and repaired

Both first upgraded packets verified in process but failed fresh-process
verification at the terminal quadratic consistency check. An export-time
polynomial roundtrip assertion located a mismatch in a tail commitment:
`offset=72488, poly=54`. `polz_reduce` can leave a carry in the top limb; the old
48-bit packer assumes normalized input and drops that carry. Repacking decoded
bytes was identical, so that earlier check could not detect the loss.

The isolated backend now canonicalizes a copy modulo q before every bitpack,
including transcript hashing. Canonicalizing only the external export would
change transcript inputs without regenerating the proof and is insufficient.
The exporter checks equality modulo q after packing/unpacking each polynomial.
704 independent integer-residue boundary cases pass; the old packer fails 512
of those cases when given these noncanonical representations. This regression
covers serialization, not full protocol soundness. New transcripts are produced;
do not assume compatibility with old packets or reuse their timing evidence.

## Measurements

Same fixed capacity template, public root and input layouts; one CPU core (8),
16 GiB virtual-memory cap. Circuit/setup remains cold work outside warm readiness.
The canonical run measured 1.707 s and 1.724 s from batch input through serialized
packet write, for 2,460 and 12 actual messages respectively. Each packet is
150,526 bytes; backend 108,624 bytes. In-process verify ~0.731 s. Twelve existing
wrong-claim/opening mutations reject. These are two observations, not p95 or a
hardware-normalized speedup claim. A preceding run took 1.80/2.03 s, underscoring
that the deadline has no reliable margin for the rest of NEAR.

[audit_sis_policy.py](audit_sis_policy.py) derives the initial statement norm from
the packet's transcript-bound norms and the fixed template's binary-vector shape:
only vector 1 is binary, rank 3072, degree 64. Nonbinary vectors use max(norm,1)
plus 47 slack bits, matching the statement builder. It screens all subsequent
levels and both outer obligations. Each case has 22 finite model estimates,
all >=128 bits; minimum **140.45 bits**. All 44 match the independent C excerpt.
This is the selected scalar-model cost only, not a composed security level.

## Evidence and reproduction

[evidence/sis-policy](evidence/sis-policy) preserves final patches, failed-run
logs, parameter audits, boundary regression source and final logs/manifest.
`backend.patch` applies to the original LaBinius vendored backend at the pinned
revision in EXPORT_CODEC.md; apply in a separate copy. Build the existing template
with `LABINIUS_LABRADOR_DIR` pointing at that copy, as recorded in the manifest.
`export-assertion.patch` adds the codec check to the existing exporter. The copied
estimator/bounds derive from IBM Apache-2.0 sources; license/notice are preserved
in `evidence/security`. No code from other lanes is modified.

The native decoder remains a trusted-local research API. The implementation
retains legacy checks in the unused Greyhound path; do not advertise the entire
library as upgraded. Initial commitment, outer LaBinius PCS, structured attacks,
16-byte backend transcript/QROM, hash bridges and history composition remain
separate gates. Next: price the outer PCS and transcript security before making
this backend a NEAR integration dependency.
