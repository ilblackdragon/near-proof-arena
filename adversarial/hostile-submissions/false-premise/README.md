# Hostile case: false-premise

**Attack family:** theorem-type-mismatch

**Expected decision:** REJECTED
**Expected failing gate(s):** FORMAL_SEMANTIC_SOUNDNESS
**Expected reason code(s):** THEOREM_TYPE_MISMATCH

## What this proves about the judge

The certificate is `False -> Goal` (or assumes an unsatisfiable hypothesis), which is trivially provable and says nothing. Its type carries an extra `False`/unsatisfiable premise, so it is not the required relation type: FORMAL_SEMANTIC_SOUNDNESS must fail on the type mismatch.
