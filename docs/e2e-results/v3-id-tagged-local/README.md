# Repaired native ID concatenation

Seven additive modules strictly compile; 32 exact axiom guards pass. No axioms beyond the standard Lean three, no sorry, and no accepted-domain restriction.

The old data-only concatenation had incorrect endpoint inverse/equality metadata: its last row was generated against no successor even when another active block followed. The new tagged trace uses the actual next row, fixes top equality/inverse and dependent gates across increasing transition IDs, and preserves all data columns 0–9. Empty blocks, duplicate public IDs, unknown prior endpoints, and repeated records are retained.

`ProcIdNativeLocal.prepared` proves full selected ID TableLocal with actual successful prep supplying 64-bit shard ID bounds. `length_eq` matches the previously budgeted ID row count; `suffix` proves all-zero padding at every position beyond that count. `ProcIdTaggedTraffic.balance` proves physical RecordLinear request71/result72 conservation against this repaired trace, retaining ordered occurrences and multiplicity.

The selected ID table itself is unchanged here. The separate family bus69→40 repair and vertical stage installation must still be composed. Public-ID bus70 transport is a remaining additive connection. Compilation used prebuilt checked dependencies; parent independent source closure remains separate.
