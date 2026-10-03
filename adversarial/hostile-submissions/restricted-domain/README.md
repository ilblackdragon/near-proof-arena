# Hostile case: restricted-domain

**Attack family:** theorem-type-mismatch

**Expected decision:** REJECTED
**Expected failing gate(s):** FORMAL_SEMANTIC_SOUNDNESS
**Expected reason code(s):** THEOREM_TYPE_MISMATCH

## What this proves about the judge

The certificate proves soundness only on a RESTRICTED domain (adds an extra hypothesis, e.g. `receipts.length = 1`). Its type is not the challenge's required relation type, so FORMAL_SEMANTIC_SOUNDNESS must fail on a type mismatch — the judge constructs the required type and will not accept a narrower theorem.
