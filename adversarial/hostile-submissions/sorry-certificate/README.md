# Hostile case: sorry-certificate

**Attack family:** axiom-audit

**Expected decision:** REJECTED
**Expected failing gate(s):** AXIOM_AUDIT
**Expected reason code(s):** SORRY_FOUND

## What this proves about the judge

The certificate is closed with `sorry`. AXIOM_AUDIT (no sorry / no native shortcuts) must fail: `sorry` emits `sorryAx`, an unsound axiom.
