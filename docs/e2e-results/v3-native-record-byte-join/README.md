# Original prior-record byte join

Strict Lean4.34.1 checks and eight exact axiom guards pass for ProcPriorRecordTraffic, ProcRawRecordTraffic, and ProcNativeRecordBalance (in that dependency order; the first two are independent).

The original RawFrame bus75 sender at each native record byte is exactly the decoded LinkAllowance encoding at the same original ordinal. The record table's nine limb rows receive exactly those24 bytes in order. `record` and `indexed` equate both inventories for every original occurrence, including repeated IDs and unknown IDs, with no current-layout ordering or distinctness assumption. Successful optional native decoding is used; missing state has no records.

This checkpoint covers all record-byte locations and receiver rows. Full physical table padding/header silence and concatenated record-table assembly remain separate next obligations. The priorRead68 physical inventory and last-write memory conservation are also not claimed; ProcPriorCodecQueries.native_queries already gives the semantic last-write identity.

Validation uses bounded single-worker strict Lean with prebuilt dependency overlays. No new axioms, sorry, domain restrictions, or selected table changes. Audit: test/AuditProcNativeRecordBalance.lean.

Selected component correction: all interactions now use the exact `ProcPriorVertical4` record component bus parameters `75 71 72 67 76`. The five-module dependency chain and both audits were rerun after this correction.
