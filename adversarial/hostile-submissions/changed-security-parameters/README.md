# Hostile case: changed-security-parameters

**Attack family:** crypto-soundness

**Targets:** near-formal  (runnable: true)

**Expected decision:** REJECTED
**Expected failing gate(s):** FORMAL_CRYPTO_SOUNDNESS
**Expected reason code(s):** THEOREM_TYPE_MISMATCH

## What this proves about the judge

The reference proof, but the certificate is stated for a security profile with a 40-bit target instead of the challenge's 128 bits (all other parameters and artifacts as the judge renders them). The judge, not the candidate, fixes the profile in the statement, so a certificate about weaker parameters is a different theorem -> FORMAL_CRYPTO_SOUNDNESS fails with THEOREM_TYPE_MISMATCH.

## Package

Derived case: the reference `examples/reexec-witness` (see `BASE`) with only the files in this directory replaced/added; the e2e driver materializes base + overlay before packing. Every other file -- model, prover, build recipe, lemmas -- is the admitted reference.

## Notes

The checker never emits SECURITY_BOUND_INSUFFICIENT on this route: the profile is part of the judge-constructed statement, so weakened parameters surface as a statement mismatch. A backend whose certificate proves the bound for the required profile but whose concrete parameters differ is the same mismatch.
