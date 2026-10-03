# Hostile case: shadowed-definition

**Attack family:** axiom-audit

**Expected decision:** REJECTED
**Expected failing gate(s):** AXIOM_AUDIT
**Expected reason code(s):** SHADOWED_DEFINITION

## What this proves about the judge

The package ships its OWN altered copy of a trusted definition (a weakened `ArenaCore.Admits` / `NearRelation`) so the certificate type-checks against the wrong meaning. The checker pins the trusted sources by tree digest and must detect the shadowed/redefined trusted name.

## Notes

RECHECK_FAILED may also result when the frozen tree digest is re-pinned; the shadow is the root cause.
