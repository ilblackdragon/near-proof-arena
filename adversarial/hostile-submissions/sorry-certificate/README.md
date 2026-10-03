# Hostile case: sorry-certificate

**Attack family:** axiom-audit

**Targets:** near-formal  (runnable: false)

**Expected decision:** REJECTED
**Expected failing gate(s):** AXIOM_AUDIT
**Expected reason code(s):** SORRY_FOUND

## What this proves about the judge

The certificate is closed with `sorry` (emits `sorryAx`, an unsound axiom). AXIOM_AUDIT must fail with SORRY_FOUND.
