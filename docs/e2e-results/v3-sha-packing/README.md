# Isolated SHA column packing feasibility

The actual544-column SHA table has no syntactically unused columns: `EvalShaColumns.lean` reports all544 used and an empty unused-index list. This is an executable syntax audit, not a kernel theorem; a monolithic kernel syntax search exceeded the bounded16GiB process allowance and was not retained as a claimed proof.

Two new candidate tables retain every original constraint and interaction under exact polynomial substitution. Neither replaces the active SHA table.

| Candidate | Base width | Aux | Quotient | Finals | Max log |
|---|---:|---:|---:|---:|---:|
| Original |544|9|5|9|22|
| ShaCarryPairs |520|9|5|9|22|
| ShaCarryKinds |512|9|5|9|22|

Each of24 three-bit carries becomes one low-pair digit and one high bit. Cubic interpolation decodes each low pair; all old Boolean constraints remain, now degree6. At auxiliary grouping2 this does not increase the already-degree6 table bound. Every Boolean pair is checked to round-trip in BabyBear. The second table similarly packs16 round selectors into8 digits. Start/digest selectors remain separate: packing them too produced degree7 counter/Seen constraints and an extra quotient column, more expensive than the one-column saving.

Kernel-checked results include exact candidate shapes, table well-formedness, generic expression-evaluation commutation, original constraint satisfaction from candidate constraints in the decoded environment, and exact evaluation of interaction message/multiplicity lists. Twenty-one exact axiom guards pass with only the standard `propext`, `Classical.choice` and `Quot.sound`. No carry-range, digest correctness or SHA assumption is used in these local transport results.

`ShaPackingTrace.decode_local` now transports actual candidate TableLocal to original SHA TableLocal, and `table_traffic` preserves exact physical bus counts. `ShaPackingEncode.encodeTrace` is the executable512-column honest encoder; `cell_roundtrip`/`eval_roundtrip` recover every original cell/expression on each physical row, including cyclic successor reads. `encode_local` derives candidate TableLocal from any original TableLocal and `encode_traffic` preserves exact traffic. No extra Boolean/range premise is needed: Booleanity comes from the original constraints. These physical bridges are checked; integration into the complete family and SHA job allocator remains separate.

Replacing all four SHA tables in `CurrentFamily` with the actual512-column candidate costs9,379,590 bytes (saving118,784), still990,982 above8MiB. A hypothetical complete three-bin placement costs8,806,661, still418,053 above8MiB. Three-bin capacity remains unproved; the current conservative all-family total exceeds it. These figures are exact model evaluations of actual candidate definitions, not admission claims.

## Column groups and further opportunities

- A/E/W data:384 bits, all semantically used by rotates, Boolean SHA operators, addition and byte traffic. Naive universal two-bit packing makes cubic bit operators degree9, then10 with gating, violatingdegree8. Packing row selectors concurrently makes this restriction tighter.
- Carry bits:72→48 in the checked candidate. The schedule carry's high bit may be eliminable if its≤3 bound is derived from authenticated helper arithmetic; that is not a syntactic redundancy and remains unproved.
- I4/I8/I12 helpers:24 columns carry delayed17-bit limb sums. W3 has6 delayed16-bit limbs. Hin has16 chaining-value16-bit limbs. Packing two full16-bit limbs into one BabyBear element would alias32-bit values and cannot be done without additional information.
- One-hot row kinds:18→10 in the checked candidate; the remaining S/D distinction preserves the better quotient count.
- Data flags:16 bits occur in BYTES multiplicities and framing. Packing them can increase grouped interaction degree; their cost must include the bus polynomial, not only constraints.
- Framing:8 columns. `Pn=P80*(1-Last)` is explicitly derived and could be substituted out, but combined with packed round selectors its padding expressions would increase quotient degree; this is not an automatic net saving.

The checked32-column reduction is a useful incremental result, not a route to the remaining418KB by itself. Larger savings still require a complete workload allocation and a materially different data representation or verified sharing. No field, cap, accepted domain, proof format or frozen protocol was changed.
