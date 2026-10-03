# Hostile case: additional-axiom

**Attack family:** axiom-audit

**Expected decision:** REJECTED
**Expected failing gate(s):** AXIOM_AUDIT
**Expected reason code(s):** FORBIDDEN_AXIOM

## What this proves about the judge

The development introduces an extra `axiom` not on the challenge's allowlist and uses it to close the proof. AXIOM_AUDIT walks the transitive axioms of the certificate and must fail on the forbidden axiom.
