# Lean chunk integration except W05 — 2026-10-24

Baseline: main `e44e2cdbd`. Merge: `c3976e326`, bringing L4 through `06dffaac6`.
User scope: merge committed Lean lane work except W05 and refresh remaining completion work.

## Merge ledger

| Lane | Inspected tip | Result |
|---|---|---|
| L0 | `190841d3d` | Already on main |
| L1 | `46ddb8746` | Already on main |
| L2 | `46ddb8746` | Already on main |
| L3 | `4a333be4e` | Seven pending W05 commits excluded |
| L4 | `06dffaac6` | Six pending commits merged |
| L5 | `6bf80d533` | Already on main |
| L6 | `ecd5a4fbd` | Already on main |
| L7 | `1edbf9cb4` | Already on main |
| L8 | `46ddb8746` | Already on main |

No lane branch was reset or rebased. Lane working changes, including L3 scratch work, are preserved.
Existing main BLS arithmetic, host dispatch and fixture runner are unchanged; excluding W05 does not
revert earlier merged BLS progress. Reconcile lane bases against this integration before later merges.

## Integration edits

- Kept all main Lake executable targets and added both L4 targets.
- Imported `GlobalContractChunk` from the root so default builds check the new declarations.
- Corrected misleading module comments: the widened action decoder is standalone, and the delegated
  ETH-local guard still rejects. No extra execution path is claimed validated.
- Regenerated coverage from combined sources: 147 implemented / 36 validated / 5 missing / 23 partial /
  11 impossible-at-boundary, 222 rows. Five L4 rows move missing to partial; 28 remain unresolved.
- Kept UQ-006 open: non-instant receipt status is insufficient to prove source-proof impossibility.
  The imported lane log is historical evidence, not an accepted boundary proof.
- Updated the completion workplan with all W00–W16 remaining obligations and parallel dependencies.

## Fresh validation

- `lake build NearSpecV3 NearSpecV3.Successor probe-l4 nearspec-v3-check-l4`: success, 178 jobs.
  This is an incremental integration build, not a clean release build.
- Re-executed all 539 case paths in the committed L4 replay with the freshly built driver:
  all rows exactly match recorded verdicts/reasons; all D3/L4 comparisons agree.
  This tests preservation on excluded cases, not new positive global execution.
- Python harness: 50 discovered, 49 passed, 1 skipped (environment-dependent corpus configuration).
- Coverage drift check, corpus manifest schema and `make pin-check`: passed.
- W05 crypto files unchanged from baseline; L3 pending commits not ancestors of the integration.

No full combined successor replay, new global positive fixtures, release axiom audit or admission
was performed. Gates A/B/C remain open. See
[remaining work](../requirements/LEAN_CHUNK_COMPLETION_WORKPLAN.md#remaining-work-by-package).
