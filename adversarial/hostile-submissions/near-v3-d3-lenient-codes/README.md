# Hostile case: near-v3-d3-lenient-codes

**Attack family:** proof malleability (a sound verifier that accepts several byte strings for one proof)

**Expected decision:** REJECTED
**Expected failing gate:** ADVERSARIAL_PROOFS
**Expected reason code:** HOSTILE_PROOF_ACCEPTED

The `near-chunk-v3` D3a reference (`examples/reexec-v3-d3`, `BASE`) with one change in its normaliser
(`formal/ReexecV3D3/Canon.lean`, the last line of `canonW`): the contract-code list of the witness
file is kept as the producer sent it. Every state-witness freedom is still fixed (ignored header
fields, receipt-proof entries, `base_state` values cut to those reachable from the pre-state root,
SHA-256 order), but nearcore's validator appends the code blobs to the main recorded storage as a
hash-indexed store (`pwt.rs:693-696`), and `RelD3` follows it. So a second accepted proof of the same
claim is obtained by

* reordering the code blobs;
* repeating one;
* appending a blob no executed contract needs (another contract's real code, garbage, an empty blob);
* moving a code blob that is also a reachable trie value between the code list and `base_state`.

The certificate is genuine: soundness (`check_sound`) and completeness (`relD3_normal`) of the
reference do not depend on what `canonW` computes. Only `ADVERSARIAL_PROOFS` can catch it, through
code-blob witness-freedom mutants (the D3 extension of `v3-witness-freedoms`).

Local evidence (`docs/e2e-results/v3-d3-reference/hostile-lenient-codes.txt`): on the public
positives with code blobs, the code reorder / duplicate / junk / empty mutants of this candidate's
proofs are accepted by its verifier; the reference rejects all of them.

Package: `BASE` plus this case's `formal/ReexecV3D3/Canon.lean` and `candidate.toml` (the base's,
renamed, pinned to the near-chunk-v3 challenge id; re-pin with the base after signing, see the
checklist in `spec/tools/build_challenge_draft_v3_chunk.py`).
