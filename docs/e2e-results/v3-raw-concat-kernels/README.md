# Ordered raw-parser concatenation kernels

2026-10-09. Strict single-file compilation passed for these additive modules, in dependency order:

1. ProcRawConcatBoundary: complete original RawFrame constraint list at hash31→next header0, with actual tau increment; also final hash31→zero padding. Arbitrary next state, VID and presence are permitted; current absent state must be State.initial, and current record count must be below2^24.
2. ProcRawConcatStamp: constraint-preserving common tau stamping inside an instance, plus removal of per-instance physical-first flag. Exact conditions are current/next zero original tau, nonterminal row, and act=first for first-flag removal.
3. ProcRawConcatInterior: derives those interior conditions from actual raw slots and proves all interior equations, including the header0 of a nonfirst instance. It retains only count bound and actual absent-state condition.
4. ProcRawConcatGeometry: executable list concatenation of actual NativeBlock raw rows. Proves exact lengths, positive block length, indexed lookup, active-position decomposition, next-block lookup and zero padding.

Audit: test/AuditProcRawConcatBoundary.lean, 13 exact axiom guards, all PASS. Standard axioms only; no sorryAx. Checks use prebuilt dependencies, strict autoImplicit/relaxedAutoImplicit false, -j1, 24GiB virtual memory cap.

Remaining work is explicit: assemble these row kernels into whole physical TableLocal, prove first global row tau0 and bit projections, transport physical messages through concatenation, and derive aggregate raw-row capacity from accepted native witnesses. The executable concatenated trace exists, but this checkpoint does not yet assert its TableLocal or complete global conservation.
