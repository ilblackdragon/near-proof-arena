# Hostile case: ui-injection-manifest

**Attack family:** ui-log-injection

**Expected decision:** REJECTED
**Expected failing gate(s):** PKG_WELLFORMED
**Expected reason code(s):** MANIFEST_INVALID

## What this proves about the judge

Injection payloads in manifest fields. `name` is constrained to [a-z0-9-] so a payload there fails PKG_WELLFORMED (MANIFEST_INVALID); payloads in free-form fields (backend_family) must be stored and rendered escaped.

## Notes

The illegal name is the hard failure; the free-form backend_family payload below exercises API escaping.
