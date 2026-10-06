# Hostile case: near-v3-lenient-witness

**Attack family:** proof malleability (a sound verifier that accepts several byte strings for one proof)

**Expected decision:** REJECTED
**Expected failing gate:** ADVERSARIAL_PROOFS
**Expected reason code:** HOSTILE_PROOF_ACCEPTED

The second reference for `near-chunk-validation-d0` (live run 2,
`sub_9b0c50fcdf80450da79cced76b4f7aea`, ADMITTED on `chl_4b431651…` before the
mutator below existed): the verifier accepts only *canonical* witnesses — the
chunk header's `height_included`, its signature and every transition
`block_hash` zero — and decides `RelD0`. That closes the validator-ignored
fields, but not the freedoms of nearcore's **lenient decoding**, which `RelD0`
mirrors faithfully:

* `source_receipt_proofs` is a `HashMap`: entries in any order, a duplicate key
  keeps the last value;
* every `PartialState::TrieValues` (`base_state`) is a `Vec` used as a
  hash-indexed store: any order, duplicates, and values no trie node references.

So reordering, repeating or padding gives a second accepted proof of one claim.

Overlay on `examples/reexec-v3-d0` (`BASE`): `formal/ReexecV3D0/Model.lean`,
`Obligations.lean`, `source/src/bin/prove.rs`, `source/Cargo.toml` and
`build-recipe/build.sh` as of commit `003a9cb`.

**What it checks about the judge.** The worker's structure-aware mutator
`v3-witness-freedoms` (runners/worker/src/mutators.rs) applies each freedom to
every honest `near-arena-witness-v3` proof (`entries/duplicate-key`,
`entries/reorder`, `values/reorder.<t>`, `values/duplicate.<t>`,
`values/inject-unused.<t>` for the main and every implicit transition), so any
v3 candidate that leaves one of them open is rejected deterministically. The
current reference closes all of them with a proved normal form
(`examples/reexec-v3-d0/formal/ReexecV3D0/NormalForm.lean`).
