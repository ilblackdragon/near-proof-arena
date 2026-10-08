# Accepted scheduler hashing capacity checkpoint

2026-10-07. New sources are in the main workspace under
`zk-formal/ZkFormal/NearV3/Assembly/`. External worktrees and Git metadata were
read-only during this checkpoint; no commit or external write was attempted.

## Checked accepted-input bounds

`SchedulerAllBounds.checkD0a_upsert_all_bounds` constructs the same actual
scheduler-upsert witnesses for the main chunk and implicit chunks. It derives:

- 1–32 executions, each on a well-formed authenticated input;
- native requested-key depth at most 400 and at most 403 emitted parts;
- total input unfolded bytes at most the unchanged B0 = 2,000,000;
- total emitted node serialization bytes at most 2,131,072;
- each fresh scheduler state exactly 37 + 24*n*n bytes, with actual layout n≤64;
- each fresh value at most 98,341 bytes; all fresh values at most 3,146,912 bytes.

The tight output bound charges each input node once, plus 4,096 per upsert.
Only the actual scheduler write key `[0,15]` has the needed length-two bound.
Output memory is serialized modulo u64; no output `PTrie.wf` assumption is used.
`UpsertPointwiseCost` and `UpsertSourcePointwise` derive individual source/output
serialization lengths below 2^22 and fresh values below 2^24. The source proof
uses `Render.Ups.NativeSourceOccurrences.traceUpsert_source_occurrence`.

`UpsertShaCapacity.checkD0a_upsert_sha_capacity` builds concrete kind-12 messages:
at most 12,928 messages, 5,277,984 bytes, and 1,662,140 physical SHA rows. The
batch has `honestLog≤21` and satisfies `Sha.MsgsOk`.

## Shared SHA inventory and limitations

| Family | Current evidence | Remaining composition |
| --- | --- | --- |
| Source proofs, kind 13 | Actual deduplicated decoded path weights ≤8,932,712 rows; `DedupSha.sourceWeights_exact`, `relD0a_work_bounds` | Physical SHA partition routing/ownership |
| Upsert outputs and fresh values, kind 12 | Actual messages and bound above | Complete encoded-part BYTES/DIGEST balance |
| Scheduler sanity hashes, kind 11 | `Sched.Link.SoundSha`: 64-byte preimages, one per scheduler instance | Concrete native batch allocation and charging |
| Trie node/value pre/post, kinds 7–10 | Historical `Rcpt.ShaRows.trieShaRows` is arithmetic, not a constructor coverage proof | Actual allocation, retained shadow ownership/cost, pre/post multiplicities |
| Receipt RC/RF/PEO/LEAF/RID/MRK, kinds 1–6 | Historical `Rcpt.ShaRows.rcptShaRows` envelope; source lane has newer native receipt bindings | Actual batch costs, refund coverage, multiplicities |
| Remaining ownership kinds | Registry must be checked against final table list | Exhaustive final inventory |

`SourceUpsertShaCapacity.checkD0a_source_upsert_partition` now combines actual
source weights with concrete upsert SHA message weights. Their total is at most
10,594,852 rows, and the existing greedy `splitBudget` places whole messages in
two log23 partitions. This is **a checked placement/capacity theorem**, not a
constructed SHA AIR or a final certificate. In particular the existing active
`Sha.Table.maxLog` is still 22. The source candidate already uses two-log23
placement lemmas whose physical SHA realization remains separate. Do not
silently interpret this result as admission of a changed table parameter.

`SourceUpsertShaLog22.checkD0a_source_upsert_log22` subsequently closes placement
under the **existing active log22 cap**: three greedy whole-message source bins
plus one upsert bin, each at most 2^22 rows. Flattening the four bins reconstructs
all message weights exactly. Its four exact axiom guards pass. The upsert bin
can use log21 from the earlier bound, so the conservative padded footprint for
these four bins is 3*2^22 + 2^21 = 14,680,064 rows. Other families and physical
message routing remain to be included in the final single proof.

The source envelope alone exceeds a single log22 table. No single shared-table
fit or all-family certificate capacity is claimed. Multiple physical tables must
remain inside one proof; this checkpoint does not introduce proof composition.

## Reproduction

Use Lean 4.34.1, explicit `-j1` (the environment variable alone did not bound
thread startup), a 16GiB virtual-memory limit, and CPUs 8–15,24–31. The main
private overlay is `/tmp/nearproof-assembly-modules`; upstream library paths are
read-only `formal-core`, `spec/lean`, `spec/lean/v3`, and `zk-formal` build libraries
in `/data/illia/nearproof-wt/v3-air`. `NativeSourceOccurrences.olean` is linked from
`/tmp/ups-proof` into the private overlay.

Parent independently recompiled the seven modules through `UpsertShaCapacity`
and converted their five audits to exact `#guard_msgs`. Additional checked exact
audits: `AuditSchedulerAllBounds` (4), `AuditUpsertSourcePointwise` (2), and
`AuditSourceUpsertShaCapacity` (3). All reported dependencies are within
`propext`, `Classical.choice`, and `Quot.sound`.

The independent checker proof-recheck failure and the other global assembly
obligations remain open; this checkpoint is not a stateless-validator replacement.

## Physical SHA renderer extension (2026-10-08)

`SourceSchedulerShaRender.checkD0a_source_scheduler_sha_render` now constructs
`shaBinTrace` for the four actual message bins. For every physical table index
`t<4`, it proves `TableLocal` for the unchanged SHA table and exact `TableTraffic`
on the shared BYTES/DIGEST buses. The proof uses closed SHA completeness, not a
new assumed local/traffic contract. Concrete source payload IDs and bytes are
preserved; scheduler sanity preimages are extracted from actual native execution.

New dependency chain: `SchedulerSanityInput`, `SchedulerSanityJobs`,
`SourceSchedulerShaLog22`, `ShaMessagePlacement`, `SourceShaMessages`,
`SourceSchedulerShaMessages`, `SourceShaBytes`, `SourceSchedulerShaOk`,
`ShaBinRender`, `SourceSchedulerShaRender`. Exact audits respectively cover sanity
(8), concrete placement (10), and physical rendering (8), all passing standard
axioms only. Source and upsert pointwise bounds have separate checked audits.

Remaining: aggregate bus cancellation against actual consumers, multi-SHA
soundness ownership plumbing (older single-SHA ownership interfaces cannot be
applied unchanged), other receipt/trie hash families, and final certificate
layout/footprint. The UPS renderer separately has an insufficient row envelope:
4*32 + 3,146,912 fresh-value bytes + 2,131,072 output bytes = 5,278,112,
exceeding 2^22. This is not yet an accepted-input counterexample; do not treat it
as a closed UPS capacity theorem or impose a new domain restriction.

`ShaUnionFacts.shaUnionFacts` closes the soundness contract for an arbitrary list
of locally valid physical SHA tables: the existing `Near.ShaFacts` applies to the
sum of their send/receive counts. This is an arbitrary-trace theorem, not only an
honest-rendering result. `ShaBinUnion` specializes it to the constructed bins and
proves exact summed physical traffic multiplicities. `Link3.ShaHyp.sha` can use
this interface unchanged. Its global bytes balance, digest inclusion and
other-kind ownership fields still need evidence. `AuditShaUnion` has four passing
exact guards; no additional axioms were introduced.

Further checked interfaces:

- `ShaUnionBytes`: every positive physical or union SHA BYTES receipt has a
  byte component below 256, for arbitrary locally valid traces even without an
  exported digest. `AuditShaUnionBytes`: 2 exact guards.
- `SourceShaOwnership` / `SchedulerShaOwnership`: actual job IDs are canonical
  field naturals in kinds 13 / 11–12. `AuditShaOwnership`: 5 exact guards.
- `ShaOwnedBatch.checkD0a_owned_sha_bins`: combines operational validity, exact
  allocation, all `MsgsOk` contracts, and canonical kind IDs on **one** existential
  execution list. `shaBatch_other_ids` yields the existing trie linking
  `othersId` condition on the actual expected byte messages. `AuditShaOwnedBatch`:
  3 exact guards.
- `ShaBinExact.shaBinUnion_exact`: summed physical traffic equals the traffic of
  the single exact flattened message list, without requiring ID uniqueness.
  `AuditShaBinExact`: 3 exact guards.

No active process is required to preserve these artifacts. All new outputs are
in the private `/tmp/nearproof-assembly-modules` overlay; source/audit files and
this report are in the main writable workspace. No external or Git writes.
