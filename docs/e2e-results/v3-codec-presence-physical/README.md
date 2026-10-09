# Corrected Codec / RawFrame presence conservation

2026-10-09. Strict Lean single-file checks passed with autoImplicit and relaxedAutoImplicit disabled, -j1, 24 GiB virtual-memory cap. These checks use prebuilt project dependencies; they are not an independent source-only certificate.

Dependency order (all under zk-formal/ZkFormal/NearV3/Candidates):

1. ProcCodecPresenceTraffic: exact actual corrected Codec SPOST send and RawFrame receive row inventories, including absent values.
2. ProcRawPresencePhysical: actual RawFrame has exactly one presence receive across all 2^22 physical rows, at row zero. No prior-state record count/fit assumption is needed for this presence-only statement.
3. ProcCodecPresenceGate: exact generated kF projection; only header zero has kF=1, all actual successful record/hash/ash rows have kF=0.
4. ProcCodecPresencePhysical: exact whole physical corrected Codec send singleton and tableBusCount; exact main-instance balance against RawFrame.
5. ProcNativeMainPresence: accepted main chunk constructs the SAME old read, decoded prev, replay R, distribution gd and corrected Codec result as ProcNativeMainCodecLocal. Retains complete Codec TableLocal and proves physical presence conservation against RawFrame(prev,vid,old.isSome), for every trace time/public vector/message. R.tau=0 is derived from the actual run, not assumed.

Audits:

- test/AuditProcCodecPresenceTraffic.lean: 3 exact axiom guards.
- test/AuditProcPresencePhysical.lean: 14 exact axiom guards.

All guards passed without sorryAx or additional axioms beyond the standard Lean axioms. Checked oleans are in /tmp/nearproof-receipt-check; new-module symlinks are also present in /tmp/ups-proof.

Explicit scope: this closes the physical presence join for the accepted main chunk, including missing prior state. It does not prove RawFrame TableLocal, prior-allowance lookup/memory joins, nonmain lifted presence conservation, all corrected Codec interactions, or the global transition certificate. The generic main_balance theorem accepts an arbitrary prior State because presence packets do not contain its contents; native_main binds that State to the actual successful decode.
