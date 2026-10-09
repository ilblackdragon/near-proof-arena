# Native block presence and original prior bytes

2026-10-09. Additive checkpoint after v3-codec-presence-physical.

Dependency order: Candidates/ProcRawInstancePresence, then Candidates/ProcNativeBlockPresence. Both strict single-file compiles pass with -j1, autoImplicit=false, relaxedAutoImplicit=false and 24 GiB virtual-memory bound. test/AuditProcBlockPresence.lean passes nine exact axiom guards. Checks use prebuilt project dependencies, not independent source-only closure.

- traceAt stamps the actual scheduler instance tau on active raw rows; padding stays zero. Physical presence is exactly one (tau,present,vid) packet. All physical VBYTES messages are unchanged by stamping.
- NativeBlockPresence.presence consumes the SAME NativeBlock.Valid witness as native_main_block/native_missing_block and proves full physical Codec/RawFrame presence conservation at its actual run.tau. No equality of independently selected states/VIDs is assumed.
- original_bytes: if the actual prior read is some bs, successful native decoding proves bs=old.encode. Existing ProcPriorDecode.decode_exact rejects suffix/trailing ambiguity and preserves arbitrary record count/order/IDs; no canonical-layout restriction is imposed.
- present_bytes: exact physical raw VBYTES counts equal the original bs under the explicit physical-fit condition bs.length<=2^22.
- absent_bytes: physical raw byte count is zero, while presence remains a singleton with present=false.

Remaining: discharge actual read-byte fit from accepted-state bounds in the final allocation; prove RawFrame TableLocal for traceAt; assemble multiple native blocks into one physical raw trace and carry the exact presence/byte counts through that placement. This checkpoint does not claim those obligations or the full transition certificate.
