# Candidate: prove a compact trace representation

The 1–2 s goal requires cutting the represented work as well as accelerating it.
This experiment tests an interval representation against the largest sampled
D0a receipt trace. It preserves the original field values and original local AIR
constraints; it does **not** yet provide a succinct authenticated proof.

## Measurements

Input: `00-h10035-s3`, 814 receipts, receipt table 262,144 rows × 263 columns.
The complete chunk has 156,624,112 cells. SHA-receipt and receipt tables account
for 89.5% of them. The current small terminal-proof profile rejects this shape.

| Receipt operation | Dense | Intervals |
|---|---:|---:|
| Field-value storage | 275,775,488 B | 23,463,144 B |
| Evaluation at point 1, all columns | 0.771 s | 0.040 s |
| Evaluation at point 2, all columns | 0.543 s | 0.040 s |
| Local-constraint evaluation sites | 235,929,600 | 32,999,727 |

Encoding cost: 0.264 s per witness. Each compact evaluation includes row-weight
prefix preparation. Exact agreement with independent dense folding for all
columns at both deterministic pseudorandom base-field points. These are NumPy
microbenchmarks; production uses extension-field challenges and costs will differ.
They are not GPU measurements or soundness tests.

The interval checker evaluates all 900 original receipt constraints, including
next-row wrap and first/last/transition selectors. Honest local check: 5.58 s
Python, plus 0.24 s boundary preparation. Three bad active-cell mutations at the
first, interior and last row are rejected. Unit tests exhaust positions for
rotated singleton failures with selector boundaries. The original Rust full
precheck independently accepted the same original trace and balanced its buses.
The new checker itself does not check buses.

## Algebra

For each column, store nonzero constant intervals `(start, end, value)`, covering
`[start,end)`; all omitted positions are zero. At a multilinear point `r`, let
`w_j = eq(r, bits(j))` and `W(t) = sum_{j<t} w_j`. Then exactly:

```
MLE(column, r) = sum_intervals value * (W(end) - W(start)).
```

This uses only field identities. The prototype materializes N row weights, but
never N×width field cells during evaluation. It stores 1,955,262 nonzero intervals.
Receipt bit packing alone is less effective: syntactically established static
bounds give 136 MB vs intervals' 23.5 MB. The dense SHA-receipt table differs:
495 of 544 columns have explicit unconditional boolean constraints, so static
bit representation reduces 285 MB to 33 MB. Use different representations for
receipt structure and SHA arithmetic rather than forcing both into dense fields.

To check a local constraint, split the row domain at the union of all changes
in its referenced columns, shifting boundaries for rotated references and adding
selector boundaries. The expression is constant between consecutive boundaries,
so one evaluation covers each interval. All products, additions, negations and
public inputs retain their original field semantics. This coverage argument is
implemented and tested, but not yet proved in Lean.

## Missing authenticated construction

1. Commit to canonical interval arrays and shape. Define expansion exactly;
   enforce bounds, order, non-overlap and nonzero/canonical values, or deliberately
   use an additive-interval relation with its own equivalence proof. Prover-chosen
   endpoints must not silently change the declared trace domain.
2. Authenticate MLE openings via a proof of the interval-weight identity. A bare
   fast evaluation over supplied intervals is an explicit input oracle, not PCS.
   Measure this on the full 1.96M-interval witness, including endpoint comparisons,
   extension-field prefix-weight computation and commitment work.
3. Authenticate the constraint-boundary unions: each source change must appear,
   with correct rotations, order and wrap. Omitting a change can hide a violating
   row. Prove local expressions vanish on every resulting interval and bind the
   same interval roots used in the opening argument.
4. Preserve all bus messages and multiplicities, including interval lengths and
   row-dependent indexes. A local-constraint proof alone is not chunk validity.
5. Prove equivalence to the original AIR, then integrate the complete authenticated
   argument with the shared terminal proof. Count every argument against 300 KB,
   measure witness-to-proof latency, and derive the full composed PQ bound.

**Kill criterion:** if authenticated reconstruction/union checks recreate dense
work or overwhelm the 300 KB budget, discard this representation as a proof
architecture even if it remains a useful trace storage/CPU-check optimization.
Do not claim a 7× prover speedup from a 7× reduction in evaluation sites.

## Reproduction

Scripts and results are local to this lane:

- `trace_census.py`: lossless bit packing and per-column run/sparsity census.
- `air_bounds.py`: only unconditional boolean or no-wrap affine range deductions.
  Witness observations never justify a static range. Certificates are not Lean proofs.
- `virtual_trace.py`: interval MLE vs dense folding, with per-witness preparation.
- `interval_air.py`: complete local-row coverage through constant intervals.
- `test_virtual_trace.py`: arithmetic wrap, boolean/nonboolean points, rotations,
  selector boundaries and singleton mutations.

Evidence: `evidence/large-trace-census.json`, `air-range-bounds.json`,
`virtual-receipt-evaluation.json`, `interval-receipt-constraints.json`.
The AIR hash and original input hashes are recorded. Full dumps remain in
`/data/illia/pq-tail-architecture-20261023/live-native/00-h10035-s3/dump`.
