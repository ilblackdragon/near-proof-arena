# Hostile case: changed-security-parameters

**Attack family:** crypto-soundness

**Targets:** near-formal  (runnable: false)

**Expected decision:** REJECTED
**Expected failing gate(s):** FORMAL_CRYPTO_SOUNDNESS
**Expected reason code(s):** SECURITY_BOUND_INSUFFICIENT

## What this proves about the judge

The manifest requests 128-bit security but the concrete parameters yield ~40 bits. The judge evaluates the CERTIFIED bound formula at the ACTUAL parameters (kernel-evaluated) and ignores the manifest claim; FORMAL_CRYPTO_SOUNDNESS must fail with SECURITY_BOUND_INSUFFICIENT.
