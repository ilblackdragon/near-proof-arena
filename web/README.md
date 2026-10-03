# NEAR Proof Arena — web

Read-only leaderboard and submission browser for the arena judge. A pure client
of the `/v1` HTTP API (docs/CONTRACTS.md §10): it never authenticates, never
issues non-GET requests, and never loads candidate-supplied assets.

Stack: Vite 8 + React 19 + TypeScript 5.9, react-router 7, vitest + Testing Library. Package manager: pnpm.

## Commands

```sh
pnpm install
pnpm dev            # http://localhost:5173, proxies /v1 -> $ARENA_API (default http://127.0.0.1:8471)
pnpm dev:mock       # same, but /v1 is served from DEMO fixtures (mock/), with a DEMO banner
pnpm typecheck      # tsc -b (app, tests, mock, vite config)
pnpm test           # vitest (jsdom)
pnpm build          # typecheck + vite build + scripts/check-dist.mjs
pnpm preview        # serve dist/, proxying /v1 to $ARENA_API
pnpm gen:types      # regenerate src/generated/*.ts from ../common/schemas/*.schema.json
```

Configuration:

| variable | when | meaning |
|---|---|---|
| `VITE_API_BASE` | build | API origin+prefix, e.g. `https://arena.example`. Empty (default) = same origin. Its origin is added to the CSP `connect-src`. |
| `ARENA_API` | dev/preview | proxy target for `/v1` (default `http://127.0.0.1:8471`) |
| `ARENA_MOCK=1` | dev only | serve DEMO fixtures instead of proxying |

The app uses HTML5 history routing; the static host must fall back to
`index.html` for unknown paths (`/challenges/...`, `/submissions/...`, `/compare`).

## Pages

* `/` — challenges: tier, scope kind, restriction count, **excludes**, nearcore tag / protocol, security profile, suite revision.
* `/challenges/:id` — a "What an admitted proof does NOT establish" callout (excludes + restrictions + scope kind), the leaderboard, and the full definition (id, digest, nearcore pin, protocol version, security profile, hardware, workload suite, required obligations, toolchain). The browser **recomputes the challenge id/digest** (JCS + SHA-256, CONTRACTS §1) and raises a MISMATCH alert if they differ.
* Leaderboard sections:
  * **Official ranking** — only entries with challenge tier `formal`, entry tier `formal`, `decision = ADMITTED`, `accepted = true`, `revoked = false`, and not the reference baseline. Ranked client-side by `score_milli` (the server `rank` is ignored). Empty → "No formally admitted submissions yet." No placeholder data, ever. Non-formal challenges say they have no official board.
  * Formal tier not admitted / pending; **REVOKED**; **REFERENCE** (`workload_suite.baseline_submission` or `reference: true`); **EXPERIMENTAL**; **DEMO** (hatched magenta, "never ranked"). All unranked.
* Superseded / closed challenges (docs/PROTOCOL_UPGRADES.md): a challenge with `superseded_by` shows a SUPERSEDED badge (list + title) and a prominent banner linking the successor on both the challenge and its leaderboard (the board is frozen and labelled with its protocol version); `open = false` without a successor shows a CLOSED state (the API answers `409 challenge_closed`). A "Challenge lineage" card walks `definition.supersedes` back (bounded, cycle-safe) and links the successor. Leaderboard rows show `protocol_version` and a SUPERSEDED tag; an entry whose `challenge_id` differs from the board's challenge is never ranked and is flagged.
* `/submissions` — all submissions; filters (challenge, decision incl. PENDING, tier, agent) live in the URL query. `challenge_id`/`agent` go to the server; everything is also filtered client-side.
* `/submissions/:id` — summary, stage progress with live SSE updates, digests (package, verified surface incl. verify route `native` / `npai-v1` / `native-lean`, verifier bytecode digest and verifier model/module, artifacts), candidate/build metadata, parent lineage chain (max 20, cycle-safe) with change class, gates table (status, reason codes, evidence, `reused_from` links), assumptions & trusted base, evidence graph, per-workload performance, bounded logs, signed report download, revocation banner with reason/actor/history.
* `/compare?a=&b=` — two submissions side by side; differing rows marked ≠.

### Evidence graph

An SVG (columns: sources/semantics → theorems/assumptions → artifacts/trusted base → tests/measurements) plus a full edge table.
CHECKED = solid green, TRUSTED = amber dash-dot, TESTED = blue dotted, **MISSING = red dashed with a "MISSING" label**, drawn on top, counted in an alert and listed first in the table. Missing edges are never hidden or dropped by display caps; an edge with an unrecognised status is shown as MISSING; edges to unknown nodes stay in the table. A submission with no graph says so explicitly.

### Live progress

While `decision` is `null` the page opens an `EventSource` on `/v1/submissions/{id}/events`, listening for `message`, `stage`, `gate`, `decision`, `progress`, `log`, `status`, `done`. Event payloads are only displayed (sanitised, bounded); each event triggers a throttled refetch of `GET /v1/submissions/{id}`, which is the source of truth. The stream closes once a decision exists.

## API contract

All types are generated (`pnpm gen:types`, committed in `src/generated/`):
the frozen contract types from `common/schemas/*.schema.json`
(incl. the v1.1 additive `SubmissionView` / `LeaderboardEntry` fields, see
`docs/CHANGELOG-contracts.md`) and the API-only envelopes `StoredChallenge` and
`EventPayload` from `server/openapi.json`.

* `GET /v1/challenges` → `StoredChallenge[]`; `GET /v1/challenges/{id}` → `StoredChallenge`
  (`{id, digest, definition, signature, governance_key, registered_at, registered_by, tier, open}`).
  A record whose top-level `tier` disagrees with the signed definition is rejected.
* `GET /v1/leaderboards/{id}` → `LeaderboardEntry[]` (server: ranked first, then everything else with `rank: null`).
  The UI re-derives the official section from the entry fields and ignores `rank`.
* `GET /v1/submissions` → `SubmissionView[]`; `GET /v1/submissions/{id}` → `SubmissionView`.
  When `assumptions` / `trusted_base` / `artifacts` are empty, the corresponding
  evidence-graph nodes (`assumption`, `tcb_component`, `artifact`) are shown instead.
* `GET /v1/submissions/{id}/events` — SSE, `event:` = kind, `data:` = `EventPayload` (shown as `at action data`).
* `GET /v1/submissions/{id}/report` is linked for download (`<a download>`, same origin).

List endpoints must return bare arrays (anything else is an error). Records
failing a shape check are dropped (lists) or reported as errors (single
records); a response whose `id` differs from the requested one is rejected.
Responses over 8 MiB are rejected; lists are capped at 2000.

After a decision, a pipeline stage is shown as complete only if it produced
gate results; stages skipped by fail-fast or cancellation are shown as "not run".

### Checked against the real server (contracts v1.4)

With all four signed challenges in `challenges/` loaded (`--governance-pubkey-file
challenges/governance-dev.pub,challenges/governance-local.pub`, own db
`arena_web2_dev`): the v1 → v1-1 → v1-2 chain renders SUPERSEDED badges, successor
banners on challenge and leaderboard, the lineage in both directions, honest empty
formal boards, and in-browser id/digest verification for every challenge; the
server's `409 challenge_closed` for a submission to the superseded challenge was
confirmed with curl. No CSP / Trusted Types violations.

### Checked against the real server (v1.1)

With `arena-server serve --dev` (db `arena_web_dev`, `challenges/` +
`challenges/governance-dev.pub`, `security/`) and `ARENA_API=http://127.0.0.1:<port> pnpm preview`
(and behind `deploy/local/nginx.conf`) in headless Chrome: challenge list and
detail (id/digest recomputed in the browser match), the DEMO-tier "no official
ranked board" state, empty submissions/leaderboard, and a real submission
(uploaded `sdk/templates/empty`, no worker) showing live SSE events, then
refetching and closing the stream when it was cancelled. No CSP / Trusted
Types violations.

## Security model

Every string from the API is untrusted (candidates choose names, labels, logs, notes).

* No raw-HTML sinks: no `dangerouslySetInnerHTML`, `innerHTML`, `insertAdjacentHTML`, `eval`, `new Function`, iframes or `<img>`. `tests/security.test.tsx` greps `src/` for these.
* All untrusted text goes through `<T>` / `<TextBlock>` (`src/components/Text.tsx`): React text children inside `<bdi>`, after `src/lib/text.ts` strips ANSI/VT escape sequences (CSI, OSC incl. OSC-8 hyperlinks, 8-bit forms) and replaces bidi overrides/isolates, zero-width/invisible characters, C0/C1 controls and lone surrogates with visible `[U+XXXX]` markers. Lengths are capped (inline default 256 code points, logs 64 KiB) with a visible truncation note. SVG labels and `<option>` text use the same sanitiser.
* Links are internal only. Hrefs are built exclusively from ids matching `^sub_[A-Za-z0-9_-]{1,96}$` / `^chl_[0-9a-f]{32}$` (anything else is shown as text), plus the API report path. No candidate URL is ever linked; no candidate asset is ever loaded.
* `fetch` uses `credentials: 'omit'`, GET only.
* The production `index.html` carries a CSP meta tag (build only; the dev server needs inline HMR):

  ```
  default-src 'none'; script-src 'self'; style-src 'self'; img-src 'self'; font-src 'self';
  connect-src 'self' [VITE_API_BASE origin]; manifest-src 'self'; base-uri 'none'; form-action 'none';
  object-src 'none'; frame-src 'none'; worker-src 'none';
  require-trusted-types-for 'script'; trusted-types 'none'
  ```

  Trusted Types with no allowed policy means any string-to-HTML sink throws at runtime. The built app was smoke-tested in headless Chrome under this policy with no CSP/TT violations.
* `scripts/check-dist.mjs` (part of `pnpm build`) fails if `dist/` contains fixture markers (`DEMO FIXTURE`, `demo-fixture`, `sub_demo_`), a service worker, inline script/style, or lacks the CSP.

### Server headers

`arena-server` does **not** serve the web UI. It sets `X-Content-Type-Options: nosniff`,
`Content-Security-Policy: default-src 'none'; frame-ancestors 'none'` and
`Referrer-Policy: no-referrer` on every API response (`server/arena-server/src/lib.rs`).
The static UI is served by a reverse proxy; `deploy/local/nginx.conf` sets, on the
web locations only (so `/v1` keeps the server's headers):

```
Content-Security-Policy: <the policy above>; frame-ancestors 'none'
X-Content-Type-Options: nosniff
X-Frame-Options: DENY
Referrer-Policy: no-referrer
Cross-Origin-Opener-Policy: same-origin
Cross-Origin-Resource-Policy: same-origin
Permissions-Policy: camera=(), microphone=(), geolocation=(), payment=(), usb=()
Cache-Control: no-cache                                   (index.html / SPA routes)
Cache-Control: public, max-age=31536000, immutable        (/assets/*, content-hashed)
```

plus `proxy_buffering off` for SSE. Production deployments should add
`Strict-Transport-Security: max-age=63072000; includeSubDomains` at the TLS terminator.
If the API is served from another origin, set `VITE_API_BASE` at build time and add
that origin to `connect-src` in the proxy header too.

## Mock API (development and tests only)

`mock/fixtures.ts` holds fabricated data; every name is prefixed `DEMO FIXTURE` and every agent is `demo-fixture-*`. `mock/api.ts` is a framework-free router used by the Vite dev middleware (`ARENA_MOCK=1`; `mock/dev-server.ts`, loaded via `ssrLoadModule` only when serving) and by the tests' `fetch` stub. Mock responses carry `X-Arena-Mock: demo-fixtures`, which makes the app show a persistent "MOCK API · demo fixtures only" banner. Application code never imports `mock/` (enforced by a test), and the production build is scanned for fixture markers.

## Tests

`tests/` (vitest + Testing Library, jsdom):

* `security.test.tsx` — `<script>`, `<img onerror>`, RTL override, ANSI/OSC-8 payloads in names, agents, backend family, gate summaries, evidence labels, build metadata, logs, revocation reason, lineage ids and challenge excludes: no elements created, no handlers, no raw control characters in the DOM, payloads visible as literal text, only internal links; source audit for HTML sinks and mock imports.
* `leaderboard.test.tsx` — empty official board message, DEMO never ranked (even ADMITTED/accepted with the top score), revoked/reference/experimental sections, server `rank` ignored, score ± CI.
* `submission.test.tsx` — `accepted: null` pending display, stages not run after cancel/fail-fast, SSE subscribe → refetch → close on decision, revocation banner + history, `reused_from` links, lineage, MISSING edges red-dashed and listed first, unknown edge status shown as missing, per-workload performance, DEMO labelling, malformed ids never reach the API.
* `supersession.test.tsx` — successor banners/links, frozen board keeps its ranking, lineage both ways, closed state, list badges, foreign `challenge_id` never ranked.
* `challenge.test.tsx` (incl. registration fields, tier/definition disagreement, id mismatch), `submissions-list.test.tsx`, `compare.test.tsx`, `client.test.ts`, `board.test.ts`, `text.test.ts`.
