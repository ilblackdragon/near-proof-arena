# near-arena (Python)

Synchronous `httpx` client for the NEAR Proof Arena judge API, with
TypedDicts generated from `common/schemas` and an SSE iterator.

```python
from near_arena import ArenaClient

with ArenaClient() as c:          # ARENA_URL, ARENA_TOKEN or ~/.config/arena/config.toml
    data = open("pkg.tar", "rb").read()          # from `arena pack <dir> -o pkg.tar`
    sub = c.submit_archive("chl_...", data, parent=None)
    for view in c.watch(sub["id"]):
        print(view["stage"], view["decision"])
    print(c.leaderboard("chl_...")[0])
```

Errors map to the CLI exit codes: `AuthError` (4), `UnavailableError` (5,
retry with the same idempotency key), `RejectedError` (6), `NotFoundError` (7).

Regenerate types after a contract change:

```sh
python3 sdk/python/scripts/gen_types.py
```

Tests: `cd sdk/python && python3 -m pytest`.
