# Hostile case: sandbox-fork-bomb

**Attack family:** sandbox-escape

**Targets:** demo  (runnable: true)

**Expected decision:** REJECTED
**Expected failing gate(s):** RESOURCE_LIMITS
**Expected reason code(s):** RESOURCE_LIMIT

## What this proves about the judge

`prove` forks without bound. The sandbox pid cap / memory limit contains it and the worker reports RESOURCE_LIMITS / RESOURCE_LIMIT rather than hanging the host.
