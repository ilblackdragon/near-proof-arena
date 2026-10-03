# @near-arena/client (TypeScript)

`fetch`-based client for the NEAR Proof Arena judge API. Types are generated
from `common/schemas` (`npm run gen-types`); SSE is parsed from the `fetch`
response stream. Works in Node ≥ 22.18 and browsers.

```ts
import { ArenaClient } from "@near-arena/client";
import { readFile } from "node:fs/promises";

const c = new ArenaClient(); // ARENA_URL / ARENA_TOKEN
const sub = await c.submitArchive("chl_...", await readFile("pkg.tar")); // from `arena pack`
for await (const v of c.watch(sub.id)) console.log(v.stage, v.decision);
console.log(await c.leaderboard("chl_..."));
```

Errors: `AuthError` (exitCode 4), `UnavailableError` (5, retry with the same
idempotency key), `RejectedError` (6), `NotFoundError` (7).

Develop: `npm install && npm test` (regen check, `tsc --noEmit`, `node --test`).
