# Actual ordered prior-state byte inventory

`ProcRawNativeBytesList` strictly compiles and `AuditProcRawNativeBytesList` passes three exact standard-axiom guards.

`block_messages` binds every active raw block byte message to its actual optional native read bytes, using successful decoder canonicality. It requires no per-block capacity premise. Missing reads emit no synthetic initial-state bytes. Present reads preserve all bytes, order and positions.

`physical` and `count` lift this to the full common-log22 concatenated RawFrame trace, including padding. The result is the ordered flatMap of actual `priorMessages`, with every repeated access retained. Premises are actual NativeBlock.Valid for each block and aggregate raw capacity; the accepted native capacity theorem is parent-owned. Global VID ownership/provider balance is separate and remains parent-owned.

Checked using Lean4.34.1, -j1, autoImplicit=false, relaxedAutoImplicit=false, bounded address space and prebuilt checked dependency overlays. No new axiom, sorry, domain restriction or active table change.
