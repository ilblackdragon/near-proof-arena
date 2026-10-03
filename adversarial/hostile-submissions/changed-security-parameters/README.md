# Hostile case: changed-security-parameters

**Attack family:** crypto-soundness

**Expected decision:** REJECTED
**Expected failing gate(s):** FORMAL_CRYPTO_SOUNDNESS
**Expected reason code(s):** SECURITY_BOUND_INSUFFICIENT

## What this proves about the judge

The manifest requests the 128-bit profile, but the concrete parameters (e.g. a 40-bit soundness error / too-few query repetitions) yield far fewer bits. The judge evaluates the CERTIFIED bound formula at the ACTUAL parameters (kernel-evaluated, no native_decide) and ignores the manifest claim; FORMAL_CRYPTO_SOUNDNESS must fail.

## Notes

manifest says 128 bits; parameters give ~40. The manifest number is never trusted.
