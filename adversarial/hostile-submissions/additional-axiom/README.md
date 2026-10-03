# Hostile case: additional-axiom

**Attack family:** axiom-audit

**Targets:** near-formal  (runnable: false)

**Expected decision:** REJECTED
**Expected failing gate(s):** AXIOM_AUDIT
**Expected reason code(s):** FORBIDDEN_AXIOM

## What this proves about the judge

An extra `axiom` not on the allowlist is used to close the proof. AXIOM_AUDIT walks the transitive axioms and must fail with FORBIDDEN_AXIOM.
