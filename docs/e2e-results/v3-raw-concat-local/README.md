# Full concatenated RawFrame local proof and traffic

2026-10-09. New files in dependency order:

1. ProcRawConcatActive: derives global first-row, all interior rows, every actual inter-instance boundary, and final active→padding equations from the frozen raw kernels.
2. ProcRawConcatLocal: full physical RawFrame TableLocal at log22, including all interaction bits and cyclic padding wrap.
3. ProcRawNativeLocal: derives per-block count and absence validity from SAME NativeBlock.Valid witnesses and aggregate capacity. Final table theorem assumes only all blocks Valid, indexed tau=i, and total concatenated row count<2^22.
4. ProcRawConcatTraffic: every physical message on every bus/direction is exactly the ordered flatMap of actual block-row messages; exact tableBusCount follows. Capacity here is <=2^22 (Local uses strict < for terminal padding).
5. ProcRawNativeBudget: block rows<=unfoldedBytesT(native pre)+37; sum rows<=preBytes(bs.map witness.pre)+37*bs.length. The present branch uses actual readKey→find and find_value_unfolded; the absent branch pays37 framing rows. Repeated accesses remain repeated prestate occurrences. With bs.length<=32 and preBytes<=2,000,000, rows<2^22.

All five modules pass strict single-file Lean checks, -j1, autoImplicit=false, relaxedAutoImplicit=false, virtual memory24GiB. test/AuditProcRawConcatLocal.lean passes17 exact axiom guards, no sorryAx or extra axioms. Prebuilt dependencies are used; this is not an independent source-only closure.

Exact renderer formula: blockLength b = 37+24*b.old.links.length; rows bs = bs.flatMap blockRows. Prior record count is arbitrary and is never bounded by current-layout64.

Remaining accepted binding: relate SAME bs.map witness.pre from native_ordered_blocks to m.pre::steps.map pre, then apply checkD0a_preBytes. Its parameterized conclusion is <=B, not universally2M; use the actual frozen B0 or retain an explicit B upper bound. Root owns this final accepted-capacity composition. Named presence/original-byte inventories already checked separately; listwise joins to corrected Codec and prior-memory/sanity still require their matching consumer inventories.
