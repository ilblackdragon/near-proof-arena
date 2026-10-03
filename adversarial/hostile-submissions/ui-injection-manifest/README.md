# Hostile case: ui-injection-manifest

**Attack family:** ui-log-injection

**Targets:** demo  (runnable: true)

**Expected decision:** REJECTED
**Expected failing gate(s):** PKG_WELLFORMED
**Expected reason code(s):** MANIFEST_INVALID

## What this proves about the judge

Injection payload in the manifest `name` field, which is constrained to [a-z0-9-]. PKG_WELLFORMED must reject it with MANIFEST_INVALID before any code runs; the free-form backend_family payload must be stored and rendered escaped.
