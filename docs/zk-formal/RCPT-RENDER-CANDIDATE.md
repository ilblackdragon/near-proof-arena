# V3 receipt renderer: staged construction

This work constructs an honest V3 receipt trace. It does not yet prove full
`TableLocal`, complete global traffic, or final certificate admission. Active
receipt tables and frozen native specifications remain unchanged.

Checked modules under `ZkFormal/NearV3/Assembly`:

- `RcptSkeleton`: executable field/segment/list rows from native receipts and
  their runtime refund flags. Every source list retains its 12-row header,
  including empty and repeated lists. Exact receipt row count is
  `176 + pred.length + receiver.length + signer.length + 32*keyTag + 74*[refund]`.
  Native `Receipt.wf` implies at most 474 rows per receipt; all rows are bounded
  by `12*listCount + 474*receiptCount`.
- `RcptSkeletonFields`: generated field states are legal and lengths positive;
  every generated coordinate has the exact field length and a valid index.
- `RcptSkeletonControl` / `RcptSkeletonContinuation`: concrete one-hot/boolean
  control assignment and all 26 actual continuation polynomials, proved a
  literal subset of active `cStates`, on generated adjacent segment rows.
- `RcptSkeletonTransitions`: generated field adjacency enables the correct
  actual `succ` edge; all alternative same-source edges are disabled. Both
  refund branches, first field, and final field are checked.
- `RcptSkeletonLastIndex`: all actual `lastIdx` expressions equal the native
  field length minus one, with account nonemptiness derived from `Receipt.wf`.
- `RcptSkeletonPlan`: annotated multi-list rows carry global receipt indices,
  per-list counts/indices, RC/body offsets, and final-list/receipt metadata.
  Erasure is exactly the original row skeleton, preserving order and capacity.
- `RcptSkeletonEncoding`: RC increments are exact native `Receipt.encode`
  lengths; refund increments are exact native `gasRefundReceipt` lengths.
  Both public-key tags and system receipts are covered.
- `RcptSkeletonIndices`: list and receipt indices are exact natural consecutive
  ranges; list membership/count metadata is constant within each receipt plan.

Exact audits: `AuditRcptSkeleton` (16), `AuditRcptSkeletonFields` (9), and
`AuditRcptSkeletonPlan` (14), all 39 guards pass with standard Lean axioms.
Checks use read-only AIR imports and private oleans in
`/tmp/nearproof-assembly-modules`, explicit Lean `-j1`, 16 GiB virtual-memory limit,
reserved-safe CPUs, and per-module timeouts.

The independently checked `RoutingSlice` constructor supplies the 18 routing
polynomials, candidate q bound/bits, coherent receiver-prefix recurrence, and
exact normalized public BND-key coverage from actual decoded applied receipts.
See `ROUTING-Q-CANDIDATE.md` for its separate 125-guard checkpoint.

Next obligations: combine annotated control/shape cells into a single physical
trace; prove field/list/header/global `cStates`; port byte loads and emissions,
characters, key/system/refund logic, gas and deposit arithmetic, and end-state
constraints; install the routing slice with shared-column agreement; derive
whole-table capacity from actual prepared/native counts; prove complete traffic.
The refund Boolean in `Input` must be supplied by actual runtime semantics, not
chosen merely to satisfy AIR rows. No `Good` predicate is defined as AIR validity.

`RcptSkeletonCells` and `RcptSkeletonCellControl` now define the shared header and
receipt cell assignment and padded physical `plannedTrace`. Bookkeeping fields
cannot be supplied by the arithmetic group: indices/counts/offsets, boundary
flags, and shape fields are fixed by the annotated plan. All per-receipt constant
columns carry automatically between rows of the same receipt. Arithmetic groups
provide `aux` only on other columns; this is an explicit unfinished constructor
component, not an assumption that its local constraints hold. The exact 26
continuation equations survive the shared cell assignment by a checked syntactic
footprint. `AuditRcptSkeletonCells` adds 11 exact guards, for **50 skeleton guards**.
The global field/list boundary cStates proof and auxiliary arithmetic assignments
remain unfinished.

The shared cell API now separates per-receipt constants from coordinate-dependent
auxiliary cells; all rconsts route through constants, while registers and bytes
can vary across rows. `RcptSkeletonRegisters`, `LoadExpr`, `LoadCells`, and `Loads`
construct the actual 16-state register-load streams and prove all 120 original
load polynomials on the shared row assignment. `Shifts` proves all 31 shift
polynomials, including vacuity at a field end.

`Streams`, `StreamLoads`, `StreamShifts`, and `ByteHead` add native byte selection
and explicitly supplied SHA digest streams for XRI/XLH. They preserve the same
120 loads, 31 shifts, and the byte-head polynomial. The active cRegs has exactly
200 polynomials: these cover 152 for receipt rows; 48 token-register polynomials
and header installation remain. Supplying digest streams is not yet a proof of
SHA-job ownership or digest correctness. Additional audits are
`AuditRcptSkeletonRegisters` (6), `AuditRcptSkeletonLoads` (9), and
`AuditRcptSkeletonStreams` (15), for **80 exact skeleton guards**.
