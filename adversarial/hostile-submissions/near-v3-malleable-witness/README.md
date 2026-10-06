# Hostile case: near-v3-malleable-witness

**Attack family:** proof malleability (a sound verifier that accepts several byte strings for one proof)

**Expected decision:** REJECTED
**Expected failing gate:** ADVERSARIAL_PROOFS
**Expected reason code:** HOSTILE_PROOF_ACCEPTED

The first reference for `near-chunk-validation-d0` (live run 1,
`sub_7c6a67b0c3684852a8f755072744489a`, docs/e2e-results/v3-d0-reference/):
the proof is the raw `ChunkStateWitness` and the verifier decides `RelD0`
on it. The certificate is genuine and all formal gates pass. But nearcore's
validator, and therefore `RelD0`, ignores the chunk header's `height_included`,
its signature and every transition `block_hash`, so a bit flipped there is
accepted: two proofs for one claim.

Overlay on `examples/reexec-v3-d0` (`BASE`): `formal/ReexecV3D0/Model.lean`,
`Obligations.lean`, `source/src/bin/prove.rs` as of commit `87768e1`, and
`build-recipe/build.sh` with model closure `ReexecV3D0.Model` only.

**What it checks about the judge.** The worker's structure-aware mutator
`v3-ignored-fields` (runners/worker/src/mutators.rs) flips one bit of each
validator-ignored field of a `near-arena-witness-v3` proof, so this package is
rejected deterministically. Live run 1 was caught only because a random
`bitflip` position happened to land in the signature.
