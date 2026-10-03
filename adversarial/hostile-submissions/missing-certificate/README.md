# Hostile case: missing-certificate

**Attack family:** formal-missing

**Expected decision:** REJECTED
**Expected failing gate(s):** FORMAL_SEMANTIC_SOUNDNESS
**Expected reason code(s):** CERTIFICATE_MISSING

## What this proves about the judge

The manifest names `Candidate.certificate` but the Lean project defines no such constant. FORMAL_SEMANTIC_SOUNDNESS must fail with CERTIFICATE_MISSING rather than defaulting to pass.
