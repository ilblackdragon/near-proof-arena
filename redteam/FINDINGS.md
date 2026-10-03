# NEAR Proof Arena — independent red-team findings

Lane `lane/red-team`. Each finding has a reproducer that fails on the code as
it was and passes after the fix in this lane. Ranked by severity. All repo
tests stay green (`cargo -j 8`).

Scope covered: formal admission statement (`formal-core`), formal-checker
pipeline mechanics (`runners/formal-checker`), NPAI interpreter
(`runners/npai` vs `ArenaCore.Interp`), worker/sandbox stages, server/API,
benchmark/held-out leakage. Admission-soundness issues were prioritised.

## Summary

| id | severity | area | title | status |
|----|----------|------|-------|--------|
| RT-01 | HIGH | server (cache/change-class) | Verified surface omitted the verifier binding → formal gates reused for a changed verifier | FIXED |
| RT-02 | HIGH | server (revocation) | Revocation did not invalidate the formal-cache entry it sourced → revoked PASSes reused | FIXED |
| RT-04 | MEDIUM | worker (held-out) | Candidate-chosen failure details leaked held-out inputs into public summaries | FIXED |
| RT-05 | MEDIUM | report verification | `report::verify` trusted the key inside the envelope → self-signed forgeries verified | FIXED |
| RT-06 | MEDIUM | server (quota) | Daily upload-byte quota not serialized → concurrent uploads each used full quota | FIXED |
| RT-03 | LOW | formal-checker | Unvalidated `model_type`/`model_type_module` spliced into judge-compiled Lean | FIXED |
| INFO-ROM | info | formal-core | ROM soundness game reviewed, no hole | — |
| INFO-A | info | formal-core | Byte binding / domain / deterministic-soundness reviewed, no hole | — |
| INFO-B | info | formal-checker | Expected rendering, shadowing, export/recheck reviewed, no hole | — |

---

## RT-01 (HIGH) — formal-cache key and change class omitted the verifier binding

**Where:** `server/arena-orchestrator/src/lib.rs` (`VerifiedSurface` construction),
`common/arena-types` `VerifiedSurface`, `arena_jobs::BuildOutputs`.

**Problem.** The formal-cache key and the parent/child change classification
(`ProverOnly` vs `VerifierOrProtocol`) are computed from `VerifiedSurface`.
That struct carried `verify_artifact` (the native `verify` binary digest) but
**not** the npai-v1 verifier-bytecode digest, the native-lean model name, or
the verify route. For the `npai-v1` route the admission statement is about
`.interp <bytecode digest>` and the deployed `verify` binary is the judge's
fixed interpreter (same digest for every candidate), so two submissions with
different bytecode but the same interpreter binary produced the *same*
`VerifiedSurface`. A child that swapped only its verifier bytecode was
classified `ProverOnly`, the `FORMAL_CHECK` job was skipped, and the parent's
formal PASSes (checked against a *different* `.interp` digest) were reused —
a verifier never checked by the arena gets an admission. Same hazard for the
`native-lean` model name.

**Reproducer:** `server/arena-server/tests/pipeline.rs::redteam_formal_cache_covers_npai_bytecode`
(needs `ARENA_TEST_DATABASE_URL`, default `postgres://arena:arena@127.0.0.1:55471/postgres`).
`cargo test -j 8 -p arena-server --test pipeline redteam_formal_cache_covers_npai_bytecode`.
Before the fix the bytecode-swap child skips `FORMAL_CHECK` and is classified
`ProverOnly`; after, it runs `FORMAL_CHECK` and is `VerifierOrProtocol`.

**Fix.** `VerifiedSurface` gains `verify_route`, `verifier_bytecode`,
`verifier_model`, `verifier_model_module` (additive, v1.3; schemas + openapi
regenerated, `docs/CHANGELOG-contracts.md`). The orchestrator derives them
from the validated manifest route (never trusted from the agent) and the
build's bytecode digest. An `npai-v1` build that reports no bytecode digest
gets no verified surface and the run blocks (fail closed).

## RT-02 (HIGH) — revocation did not invalidate the formal-cache entry it sourced

**Where:** `server/arena-server/src/admin.rs` (`revoke`),
`server/arena-orchestrator/src/cache.rs`, `server/arena-db/src/views.rs`
(`compute_leaderboard`).

**Problem.** Revoking a submission inserted a `revocations` row and excluded
that submission from the leaderboard, but left its `formal_cache` entry live.
The formal cache is keyed by content (challenge + verified surface + checker
image + assumptions), not lineage, so **any** later submission with the same
verified surface — including a byte-identical re-submission under a fresh,
unrevoked submission id — hit the revoked entry and inherited its formal
PASSes. Revocation (e.g. "certificate found unsound") was therefore trivially
bypassable by re-uploading the same package.

**Reproducer:** `server/arena-server/tests/pipeline.rs::redteam_revocation_invalidates_formal_cache`.
Before the fix the re-submission skips `FORMAL_CHECK` (reused from the revoked
run); after, it re-runs the formal check with no reuse.

**Fix.** `revoke` calls `cache::invalidate_source`, which invalidates every
live entry sourced from the submission. Defence in depth: `cache::lookup`
skips entries whose `source_submission_id` is revoked (covers a race where a
child is mid-flight during revocation), and `compute_leaderboard` does not
rank a run whose formal gates were `reused_from` a revoked submission.

## RT-04 (MEDIUM) — held-out inputs leaked through candidate-chosen failure details

**Where:** `runners/worker/src/stages/common.rs`, `conformance.rs`, `benchmark.rs`.

**Problem.** On a held-out case, `prove` runs with the secret request and
witness. When a case failed, the worker put the failure `detail` into the gate
summary verbatim, and much of that detail is candidate-chosen: output file
names quoted by the collector (`output "out/LEAK-..." is not a regular
file`), exit codes, claim/proof sizes, peak RSS. A prover could encode the
witness bytes into one of these (e.g. create a symlink named after the
witness) and read it back from the public gate summary — a direct
exfiltration channel for held-out data, defeating `EvidenceRef.public` and the
`case_label` redaction (which only hid the case id, not the detail).

**Reproducer:** `runners/worker/tests/pipeline.rs::redteam_heldout_failure_details_are_not_a_covert_channel`
(`ARENA_DEV_UNSAFE=1 cargo test -j 8 -p arena-worker --test pipeline redteam`).
Before the fix the public summary contained `out/LEAK-witness-0`.

**Fix.** `StepFailure::detail_for(public)` and `exit_for(outcome, public)`
return the full detail only for public cases; held-out failures report just
the fixed reason code. Public-case diagnostics are unchanged.

## RT-05 (MEDIUM) — report verification trusted the key inside the envelope

**Where:** `server/arena-orchestrator/src/report.rs` (`verify`).

**Problem.** `report::verify(env)` checked the signature using
`env.public_key` — a value carried inside the same envelope. Anyone can mint
an ed25519 key, sign a forged `ADMITTED` report with a fabricated score, and
set `public_key` to their own key; `verify` returns `Ok`. The function is the
one tests and clients call to "verify a report", so a client that trusts its
result accepts forgeries. There was no binding to the arena's actual report
key.

**Reproducer:** `server/arena-orchestrator/src/report.rs::redteam_tests::forged_report_with_own_key_fails_pinned_verification`
(`cargo test -j 8 -p arena-orchestrator redteam`).

**Fix.** Added `verify_pinned(env, expected_public_key_hex)` which requires
the arena's out-of-band report key before checking the signature, switched
the signature check to `verify_strict`, and documented that bare `verify`
proves only self-consistency. The pipeline test now pins against
`orch.report_public_key_hex()`.

## RT-06 (MEDIUM) — daily upload-byte quota was not serialized

**Where:** `server/arena-server/src/public.rs` (`upload`).

**Problem.** The daily upload-byte quota was checked once before streaming the
body, outside any lock. N concurrent uploads all saw the same "remaining"
value and each streamed up to the full remaining quota, so an agent could
store far more than its daily byte budget (a storage/DoS quota bypass).

**Reproducer:** `server/arena-server/tests/security.rs::redteam_concurrent_uploads_respect_byte_quota`.
Before the fix, 8 parallel 60-byte uploads against a 100-byte quota all
returned 201.

**Fix.** After the body is stored, re-check the daily byte total under
`SELECT ... FROM agents WHERE id = $1 FOR UPDATE` (the same lock `submit`
uses) before recording the upload; over-quota uploads are rejected 429. The
pre-stream check stays as a cheap fast-path.

## RT-03 (LOW, latent) — native-lean model_type strings unvalidated

**Where:** `runners/formal-checker/src/pipeline.rs`. Committed as `4f194d1`.

**Problem.** `model_type_module` is spliced into a judge-compiled `import` and
`model_type` into a judge-compiled `axiom … : <type>` stub. They are
judge/challenge-set today (not candidate input), so this is not a live break,
but they were the only unvalidated strings on that path; a future caller that
forwarded candidate input could inject Lean syntax (extra commands, newlines)
into code the judge compiles and links.

**Fix.** Validate `model_type_module` as a dotted Lean identifier and
`model_type` as single-line printable ASCII with no comment/string/newline
delimiters, rejecting with `ManifestInvalid` otherwise.

---

## Reviewed, no admission-soundness hole found

**INFO-ROM — random-oracle game (`formal-core/ArenaCore/Security/ROM.lean`).**
The game runs the *deployed* bytecode under a lazily-sampled tape oracle (same
`code`, `ROHASH` → random, `SHA256` → real, verifier state continues the
adversary's). Tape overflow counts as an adversary win, so a short tape cannot
help. `PrLE` requires `0 < den` and the judge type requires
`num·2^targetBits ≤ den`, so an always-accepting (oracle-ignoring) verifier
forces `count = R^n`, hence `den ≤ num`, contradicting the target inequality —
correctly rejected (`Sanity.acceptAll_not_romSound`). The honest prover `P`
answers `prove` only on true statements (`romImpl` checks `S.Rel c w`), so it
cannot help accept a false claim; `ProverComplete` is a completeness guard,
soundness-irrelevant. `RomSound.mono` lifts `bk.InLang` to `S.InLang` via
`Backend.inLang_rel` under `semSound`. No hole.

**INFO-A — statement core.** `Bytes = List UInt8` so digest binding is exact;
SHA-256 length wraps only past 2^64 (unreachable). `Domain` is non-degenerate
(true in-domain claims exist) and appears only as a completeness precondition;
`DeterministicSound` quantifies over all claim/proof bytes and `InLang` uses
the strict canonical `decodeClaim`, so non-canonical claims are outside the
language (safe direction). `B := Rel` is allowed by design; the verifier-level
obligations carry the weight. CR reduction is fuel-bounded NPAI bytecode with
pointwise soundness. No hole.

**INFO-B — formal-checker pipeline.** The decisive verdict is an independent
SHA-256 Merkle NDJSON audit over a `lean4export` already accepted by `nanoda`,
cross-checked against `arena-audit` on rechecked `.olean`s, with
`leanchecker`/`lean4lean` as further kernels; any disagreement, missing
rechecker or unreadable export is UNKNOWN, never PASS. Expected-module
rendering splices only typed literals (printable-ASCII/`Nat`/hex validated);
candidate strings are validated dotted idents used only as constant names;
`is_ident` is ASCII-only; reserved judge namespaces blocked; the shadow check
hashes every reference decl and flags mismatches; statement type-equality is
structural-by-name (not `decide`) against a trusted `.olean` compiled before
candidate modules, so candidate `@[reducible]`/`Decidable`/`@[csimp]`/
`implemented_by`/`extern`/`initialize` cannot retro-alter it. No hole.
