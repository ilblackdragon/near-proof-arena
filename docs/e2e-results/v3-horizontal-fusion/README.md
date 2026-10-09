# Kernel-certified horizontal candidate budget and header

`Candidates.HorizontalAccounts` fuses the 19 log-22 members of
`PackedMerkleFamily.tables 4`, retaining 11 smaller tables and replacing the
account table with the checked empty-account candidate. The active AIR and
protocol are unchanged. Four width-512 SHA tables and the zero-capable Merkle
table remain in the inventory.

`HorizontalCertified` proves in Lean's kernel:

- Fused shape: width 3372, aux 106, quotient 7, finals 106, log 22; 12 tables total.
- Exact group-size-2 proof-size model: **8,288,148 bytes**, 100,460 below 8 MiB.
- `sizeMaxDedup air (V2.G.pg 2) < 8388608`.
- Every table and the AIR satisfy the actual protocol wf-16 check.
- Grouped degree is at most 16 (fused degree exactly 8).
- Multiplicity bound 921,280,516; fingerprint bound 53,434,269,928 (<2^36).
- The actual unchanged `Stark.headerOk` accepts the table maximum heights.

This is a certified candidate budget/header, **not end-to-end admission**.
Remaining obligations include honest log-22 renderers for every fused component
(not arbitrary trace extension), concrete family inventory/ownership composition,
and the complete native SHA inventory fitting four bins. Full-list generic local
and exact traffic transport are checked in both directions, as detailed below.

Strict checked source order, under `zk-formal/ZkFormal/NearV3/Candidates`:

1. `HorizontalTables`: executable layout/fusion and expression transport.
2. `HorizontalTrace`: physical local projection and two-block expression transport.
3. `HorizontalJoin`: honest two-block local assembly from equal physical heights,
   component legality, and ordinary source column bounds.
4. `HorizontalDegree`: column-shift degree and shape invariance.
5. `HorizontalProfile`: small degree signatures and fusion constraint bounds.
6. `HorizontalAuxCheck`: kernel-checked exact fused degree and shape.
7. `HorizontalWf`: generic fusion well-formedness from component well-formedness.
8. `HorizontalAccounts`: actual empty-account replacement and exact rest shapes.
9. `HorizontalCertified`: exact full size, footprint, AIR and header checks.

`test/AuditHorizontalCertified.lean` contains 14 exact axiom guards, all limited
to propext and Quot.sound; SHA256
`6b01c754e8cb480d02753a0edfcd4c94bf7825666708ae5db97530a00a17d2c4`.
`test/AuditHorizontalCore.lean` additionally prints ten core axiom inventories.

Logs: `/tmp/horizontal{profile,auxcheck,wf,accounts,certified}.log` and
`/tmp/horizontalcertified-exact-audit.log`. Checked oleans: `/tmp/ups-proof`.
AccountEmpty olean is provided by `/tmp/nearproof-receipt-check` through the local
overlay. Other baseline dependencies come from the existing SHA packing and
PackedMerkleFamily checkpoints.

Checks used Lean 4.34.1, both implicit-binding options false, one thread and
16 GiB virtual-memory limit. The original monolithic kernel reduction exhausted
that limit. Factoring degree signatures resolved the problem without increasing
memory or weakening the checks. `HorizontalChecks` now forwards to the factored
certified module instead of retaining the failed monolithic proof attempt.

## Full-list physical transport

Additional stable dependency order is `HorizontalAssembly` → `HorizontalTraffic`
→ `HorizontalProjection`, after `HorizontalJoin`.

- `HorizontalAssembly.trace_local` constructs an executable concatenated trace
  from component traces with an explicit common physical clock. Component local
  legality and ordinary column bounds imply fused local legality.
- `HorizontalTraffic.trace_count` proves exact natural bus-count conservation for
  every bus, send/receive direction and message under that construction.
- `HorizontalProjection.split` projects an arbitrary physical fused trace back
  into the original component table views. `fused_local` derives each local
  legality proof; `fused_count` proves exact reverse bus-count conservation.
- These results preserve traffic independently of balance, hashes, capacities or
  semantic assumptions. They neither pad arbitrary traces nor establish native
  component completeness at the shared height.

`test/AuditHorizontalAssembly.lean`: 14 exact guards, SHA256
`f114e6b476982c1e34ddfe6088f27b0f1869c86a287547eeb8c5b78d1d2b29ea`.
`test/AuditHorizontalProjection.lean`: 6 exact guards, SHA256
`c4d31fa09ff6419ddf23a4e6c67500668ae888a0e58558c8294b481203f57c0a`.
All use only propext and Quot.sound. Logs are `/tmp/horizontalassembly.log`,
`/tmp/horizontaltraffic.log`, `/tmp/horizontalprojection.log`, and corresponding
`-exact-audit.log` files. All strict bounded checks passed.
