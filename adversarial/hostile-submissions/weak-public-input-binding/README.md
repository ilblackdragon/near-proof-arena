# Hostile case: weak-public-input-binding

**Attack family:** public-input-binding

**Expected decision:** REJECTED
**Expected failing gate(s):** ADVERSARIAL_PROOFS
**Expected reason code(s):** HOSTILE_PROOF_ACCEPTED

## What this proves about the judge

The verifier checks the proof is well-formed but never binds it to the claim's public inputs (pre_root / receipts / post_root). A proof valid for one transition then verifies for a different claim. The judge feeds the mismatched-context mutant; ADVERSARIAL_PROOFS must fail, and the independent oracle also forces CLAIM_MISMATCH.

## Notes

CLAIM_MISMATCH is an acceptable additional reason code.
