# Hostile case: shadowed-definition

**Attack family:** axiom-audit

**Targets:** near-formal  (runnable: false)

**Expected decision:** REJECTED
**Expected failing gate(s):** AXIOM_AUDIT
**Expected reason code(s):** SHADOWED_DEFINITION

## What this proves about the judge

The package ships its own altered copy of a trusted definition (a weakened `ArenaCore.Admits`) so the certificate type-checks against the wrong meaning. The checker pins trusted sources by tree digest and must detect the shadow.

## Notes

Also ships formal/ArenaCore.lean redefining Admits := True.
