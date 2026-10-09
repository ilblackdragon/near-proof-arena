# Receipt routing index repair candidate

Checked 2026-10-08. This is an isolated candidate; the active receipt table and frozen native spec are unchanged.

The old receipt constraints carry the interval index `q` but do not bound it. Since the boundary lookup address is `65*q+pos` in BabyBear, `q=1796452668` aliases address 2. The checked `Rcpt/Link/RoutingAlias.lean` fixture demonstrates the local routing problem against actual boundary records. It is not a complete AIR attack or an admission result.

The candidate appends one degree-three constraint:

```
sV * fs * (q - bitsX(12,7)) = 0
```

It reuses existing boolean scratch columns `xb12..18` on the first receiver row. Width, row cap, public input, interactions, and all original constraints stay unchanged. The full old constraint list was checked for scratch dependencies after semantic one-hot specialization: only the seven existing boolean checks read those current-row cells on receiver rows. Receiver rows and their receiver-length predecessors do not read the patched next-row cells. No bus expression reads these scratch columns.

Checked soundness APIs in `Assembly/RoutingQCandidate.lean` and `RoutingQExtract.lean` give candidate local legality → original local legality, first-receiver `q<128`, the same bound on actual extracted receipts, and canonical natural decoding of packed boundary addresses. The identified alias is rejected regardless of scratch filling.

Checked completeness APIs are in `RoutingQPatch.lean`, `RoutingQTrace.lean`, and `RoutingQPredecessor.lean`:

- `patchTrace` changes only those seven cells on first receiver rows; it preserves all heights and other cells.
- `patch_local_of_q_bound` converts any original locally valid trace whose first-receiver indices are below 128 into a candidate locally valid trace. The predecessor state is derived from the original control constraints, including the cyclic last-to-first edge; no renderer-shape assumption remains.
- `patch_busCount` and `patch_traffic` preserve every bus message and its exact natural multiplicity in both directions. They require no index-range premise.
- `honest_filling` checks the executable seven-bit assignment for every index below 128.

The unchanged boundary table has at most 8192 rows and uses 65 rows per interval. Existing physical capacity therefore implies fewer than 128 intervals and suffices for honest indices. Receipt `BndPublic.boundary_public_capacity` derives the capacity bound from actual boundary views and exact public traffic.

**Original representation coverage:** no bound on the old expanded interval count has been derived from full native acceptance; decoded layouts alone do not supply one. Native layout decoding does not require `boundaries.length+1=shardIds.length`; the ≤64 shard-ID bound must not be reused as a boundary-count bound. The checked `RoutingBoundedExamples` layout has 200 valid boundaries, one shard ID, and 201 original intervals, exceeding 8192 rows despite fitting the claim byte limit. This is a decoded-layout regression, not a complete accepted claim/witness fixture. A7/B0 bounds witness trie bytes, not these claim-side boundaries.

## Bounded candidate public representation

`RoutingBoundedLayout.lean` closes the interval-capacity issue through a semantics-preserving representation change. Keep only the first `l.shardIds.length` boundaries. The actual native `partitionPoint` counts a prefix, and the checked theorem gives

```
partitionPoint acct (boundaries.take n) = min n (partitionPoint acct boundaries)
```

Every shard lookup at an index at least `n` returns the same native default 0. Thus `shardOf_bounded` proves exact routing equality for arbitrary layouts, without sortedness, uniqueness, or a boundary-count premise. Applying `ownIntervals` to that bounded layout gives at most `n+1` intervals, including the default tail. With the actual native `n≤64` guard, this is at most 65 intervals and 4225 boundary rows.

`RoutingBoundedPrep.lean` defines candidate-only `boundedPrep` and `prepBoundedD0`. It retains the unchanged native preparation and changes only prepared `bnds`; header, source lists, scheduler, body, and forwarding records remain equal. `native_capacity` derives the row bound from actual successful `prepD0` and `walkD0`, using the existing native layout guard. `boundedIntervals_original` proves the new intervals denote exactly the old routing predicate. `public_boundary_records` identifies the new prepared public boundary records exactly; it does not pretend those records equal the old expanded family.

No BND height/width increase is needed, so this normalization adds no table footprint to the existing profile. The seven-bit receipt repair adds one cubic constraint and no columns or rows. Increasing BND height alone is unnecessary and, for the naive representation, even log22 is not a general consequence of the 1 MiB claim limit (six-byte minimum boundary encodings can produce over 11 million 65-row intervals). End-to-end candidate integration, public binding to normalized intervals, and the whole-proof size theorem remain separate obligations; the active table and native prep function are unchanged.

Validation: eight candidate modules compile with Lean 4.34.1, bounded 16 GiB and explicit `-j1`; `test/AuditRoutingQCandidate.lean` has 16 exact axiom guards and `test/AuditRoutingQTrace.lean` has 10, all passing. Only standard Lean axioms occur. Private checked oleans are under `/tmp/nearproof-assembly-modules`; no external worktree or Git metadata was changed.

The three bounded-layout/preparation/example modules also compile; `test/AuditRoutingBoundedPrep.lean` adds 16 exact passing axiom guards. Its sole new receipt dependency is checked `Rcpt/Link/OwnIntervals.lean`, available in the receipt overlay and linked into the private assembly overlay.

## Honest boundary provider and public encoding

`RoutingBoundedRender.lean` constructs one `BndE` for every exact normalized public boundary record, with usage counter equal to the number of matching receipt request keys. It proves `BndWf`, exact public record equality, physical `TableLocal`, and complete `TableTraffic` using the existing BND renderer. `RoutingBoundedUsage.lean` obtains the usage-counter range from the actual receipt request list, receipt well-formedness, and its existing physical receipt-count bound. The physical receipt-side prefix-use assignment is proved in the counter modules described below.

`RoutingBoundedPublicFit.lean` proves the normalized interval count never exceeds the original interval count. Since each interval contributes exactly 195 payload bytes and metadata has fixed width, the complete packed prepared statement cannot grow. Existing global public-size and u32 no-wrap bounds therefore transfer to the candidate with its counts and offsets recomputed by the existing encoder. The global public-size bound itself is not invented or discharged by this transfer theorem.

These three additional modules compile and `test/AuditRoutingBoundedRender.lean` adds 12 exact passing axiom guards, bringing this routing checkpoint to 54 guards.

## Physical counter assignment

`RoutingCounterRanks`, `RoutingCounterPatch`, and `RoutingCounterTraffic` construct prefix-use ordinals and prove that changing only `uB` preserves candidate local legality and exact traffic on every non-BND bus. The entire constraint list and all multiplicity expressions are checked not to read `uB`. There are 13 exact passing guards in `AuditRoutingCounters`.

`RoutingPhysicalRanks`, `RoutingPhysicalMessages`, `RoutingPhysicalProviders`, `RoutingPhysicalBalance`, and `RoutingPhysicalComplete` instantiate those counters on the actual `gBd`-enabled physical rows. Every per-key counter list is exactly `0..users-1`; the actual row message lists and counts are proved equal to the constructed messages. Provider usage counts come from those same physical requests. Exact provider uniqueness and stable request partitioning preserve repeated uses.

`normalized_physical_complete` now constructs a locally valid ranked receipt trace and a locally valid normalized boundary provider with complete provider traffic and exact physical BND balance for every message. Its remaining ownership premise is explicit: each physical routing request key belongs to the normalized prepared boundary records. Honest receipt-key construction and installation at distinct slots of the final global trace remain integration tasks. The theorem does not assume the desired counter-balance conclusion. `AuditRoutingPhysicalComplete` has 16 exact passing guards, for 83 routing guards in total.

### Native selection and honest routing arithmetic (2026-10-08)

`RoutingSelection`, `RoutingNativeSelection`, and `RoutingSelectedColumns` now
choose an executable normalized interval for every actual decoded applied receipt.
The selected q is below 128; every receiver-byte/end-marker lookup key belongs to
the normalized prepared public records. Account-length bounds come from actual
witness decoding. `AuditRoutingSelection` has nine exact axiom guards.

`RoutingLexComplete`, `RoutingFrame`, `RoutingFrameArithmetic`,
`RoutingFrameBits`, `RoutingFrameCells`, `RoutingFrameLocal`, and
`RoutingNativeFrames` construct honest comparison frames. Native interval
membership supplies prefix comparison inequalities; decoded endpoint validity
supplies positive upper bytes and strict end-marker comparison. All **18 actual
unchanged cRoute polynomials** hold for the executable frame, using concrete
9-bit difference pools and inverse witnesses. `applied_receipt_route_frames`
composes this with actual native receipt selection and public key coverage.
`AuditRoutingFrames` has 17 exact guards (standard Lean axioms only).

These are routing-group frames, not a complete V3 receipt renderer. The synthetic
frame trace provides only the current arithmetic row and next equality flags;
installing these fields into full receipt layouts, preserving other groups and
connecting adjacent physical rows remains open. The frame's Lv is only meaningful
on its end-marker, where it equals receiver length. No complete TableLocal,
whole-certificate, proof-size, or checker-admission claim follows from this
checkpoint. The routing series now has 109 exact guards, including the prior 83,
nine selection guards, and 17 frame guards.

The follow-up `RoutingFrameTransport`/`RoutingSpan` checkpoint proves actual
adjacent prefix-flag recurrence and cRoute at every row of a single coherent
receiver/end-marker span. `RoutingSpanQ`/`RoutingSlice` additionally install the
selected q and seven concrete bits, preserving cRoute. The final
`applied_receipt_route_slice` simultaneously proves all 18 routing equations,
the added qBound equation, boolean scratch bits, and exact physical BND-key
membership in normalized public records, from the actual decoded applied receipt.
The account-length bound derives the log-7 span capacity. `AuditRoutingSpan`
(nine guards) and `AuditRoutingSlice` (seven guards) pass: **125 exact guards**
across this routing series. This coherent routing slice still is not complete
receipt TableLocal: other groups, control-state installation, and global traffic
placement remain open. Filling q bits on every span row is specific to the slice;
other receipt states have their own scratch ownership.
