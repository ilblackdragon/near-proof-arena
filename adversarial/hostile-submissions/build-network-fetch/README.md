# Hostile case: build-network-fetch

**Attack family:** build-integrity

**Targets:** demo  (runnable: true)

**Expected decision:** REJECTED
**Expected failing gate(s):** BUILD_REPRODUCIBLE
**Expected reason code(s):** BUILD_FAILED

## What this proves about the judge

The build recipe tries to fetch a dependency over the network (curl, then git). The build sandbox has no network, so the fetch fails and BUILD_REPRODUCIBLE fails with BUILD_FAILED. Honest packages vendor everything.
