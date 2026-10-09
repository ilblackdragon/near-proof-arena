# Ordered native Codec/Raw presence balance

Strict Lean 4.34.1 compilation and 12 exact axiom guards pass for:

1. `ProcCodecConcatTraffic`: every corrected Codec interaction is current-row dependent; zero padding is silent; full physical traffic decomposes into the actual ordered native block arrays on every bus and direction.
2. `ProcRawPresenceList`: concatenated RawFrame presence receives are exactly one `(tau,present,vid)` packet per actual block, retaining absent states and repetitions.
3. `ProcNativePresenceBalance`: the same ordered native blocks give exact full physical Codec-send/Raw-receive count equality on SPOST.

The generic balance requires actual block validity, current scheduler n<=64, block count<=32, and aggregate raw capacity. It does not assume prior record count<=64. `SchedulerCodecRawAccepted.accepted_tables` supplies the accepted execution and aggregate capacity in the parent lane. VID/provider ownership remains a separate join.

Validation uses prebuilt checked dependency overlays, strict autoImplicit/relaxedAutoImplicit disabled and one Lean worker. This is not a new source-only full-project build. No axioms or sorry were introduced. Audit: `zk-formal/test/AuditProcNativePresenceBalance.lean`.
