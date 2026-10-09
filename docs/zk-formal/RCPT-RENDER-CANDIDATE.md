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


`RcptTokenWindows`, `TokenCells`, `TokenGas`, and `TokenCarry` now construct
old/new u128 windows and prove the actual 16 gas-token equations, including the
GP-to-TL endpoint, and 16 carry equations inside receipts and between their
non-GP fields. `AuditRcptTokens` adds 21 exact guards. The remaining 16 cRegs
initial-token equations and full header/cross-receipt installation remain open.

`RcptNativeTokens`, `RcptTokenLedger`, and `RcptMainTokenLedger` connect these
windows to native execution: ordinary receipt success gives exact burn addition
and the actual checked u128 bound; system receipts preserve the total; successful
ordered `applyReceipts` gives every intermediate bounded window and the final
sum. Successful `applyNewChunk` derives zero initialization directly, so the
result adds no initial-value or overflow premise. The executable ledger preserves
receipt order and concatenation (including empty lists), and adjacent endpoints
serialize to identical bytes. The three new audits contain 2, 5, and 1 exact
guards, respectively: **109 exact skeleton/native-ledger guards** in total.
Full physical receipt TableLocal/traffic and SHA stream ownership remain open.


`RcptHeaderTokens` installs prefix-burn bytes in list headers, proves same-header
carry, and discharges all 16 initial-token polynomials on the actual padded
`plannedTrace` (also when there are no lists). `RcptLedgerIndex` proves exact
indexed native ledger entries, adjacent endpoint byte equality, and actual
receipt-plan index/input correspondence. Their audits add 9 and 4 exact guards,
for **122 skeleton/native-ledger guards**. The cRegs subgroups now all have
checked constructor lemmas, but whole-trace composition remains unfinished:
header byte/register loads, cross-receipt/list placement, and digest ownership
still require their exact shared-row and global-order bindings.


`RcptPlanLedger` connects generated receipt plans to the same flattened native
input, preserving global indices across empty lists. Its concrete
`receiptPlanToken` assignment equals the actual ordered native ledger entry,
and successful native `applyNewChunk` proves each generated window's no-overflow
bound. `AuditRcptPlanLedger` adds 4 exact guards, totaling **126**. This binds
token choices to execution; it does not yet establish whole-trace adjacency.


`RcptBoundaryTokens` proves all 16 carry equations across a receipt endpoint
and the next receipt's first field, using the constructed native prefix ledger
and consecutive generated indices. It supports both final-field variants.
Four exact audit guards bring the total to **130**. The remaining global
placement proof must show which adjacent physical rows instantiate these local
boundary lemmas, including intervening source-list headers.

`RcptRowNeighbors` and `RcptSegmentPlan` now classify every indexed active-row
neighbor as a continuation of the same annotated segment or a segment endpoint.
The segment flattening is exactly `plannedRows`; empty source lists keep their
headers. `RcptTerminalRows` proves the active-to-padding boundary is likewise
an endpoint. `RcptHeaderStreams` supplies the native 12-byte u64-shard/u32-count
header stream while preserving token cells.

`RcptHeaderRegLocal` proves all 200 cRegs equations for consecutive header rows
away from the physical first row, with the ordinary public binding that the
eight PH_OWN bytes equal u64 own. The active load family includes this CL load;
it is checked explicitly, not assumed inactive. Actual first-row initialization
was separately proved by `RcptHeaderTokens`. The five new audits contribute
9+8+2+6+5=30 exact guards, totaling **160**. These modules and audits pass with
both `-DautoImplicit=false` and `-DrelaxedAutoImplicit=false`. Global trace
transport, cross-segment/header boundary composition, terminal padding equations,
and the remaining non-cRegs constraint families are still open.

Physical composition checkpoint: `RcptRegTransport`, `RcptPhysicalHeaders`,
`RcptRegInterior`, `RcptPhysicalInterior`, and `RcptRegPadding` prove all 200 cRegs
on every actual segment-interior coordinate and every zero-padding row, including
padding that wraps to an active first row. Initial token equations hold at every
physical position. These five audits add 14 guards.

`RcptSegmentLedger` proves an exact processed-receipt index chain from zero to
the flattened receipt count; only the GP segment increments it.
`RcptSegmentAdjacency` derives nonempty fields from native Receipt.wf and recovers
the actual adjacent segment pair at every active boundary. Their audits add 12.
`RcptSegmentTokenBytes`, `RcptSegmentTokenCells`, and `RcptBoundaryCarry` bind those
indices to native token bytes and prove all 16 carry equations at every non-GP
active segment boundary, including receipt/header and empty-header transitions.
Their audits add 10: **196 exact skeleton/native/physical guards** now pass.

The full cRegs theorem is still unfinished. Remaining endpoint composition
includes the GP last-window-to-next-segment case, loads/shift gating at arbitrary
active endpoints, and final-active-to-padding lastR. Other receipt constraint
families and complete traffic remain open. No full TableLocal or certificate
admission claim follows from these staged proofs.

**Unified cRegs checkpoint:** `RcptPhysicalRegs.nativeReceiptTrace_cRegs` now
proves all **200 unchanged cRegs polynomials at every physical row** of the
single executable `nativeReceiptTrace`. The proof includes every header/receipt
interior, every active boundary, final GP shift, empty source lists, final active
row, zero padding and cyclic wrap. `RcptLastPlans` and `RcptFinalSegment` derive
the actual final flags; `lastR`, adjacency and token equality are not theorem
premises. This supersedes the endpoint gaps in the preceding progress entries.

The theorem explicitly takes native receipt well-formedness, the eight public
PH_OWN bytes equal to `u64 own`, and `plannedRows.length <= 2^log`. Capacity and
public binding must still be composed with accepted-input facts. SHA digest
streams, per-receipt arithmetic constants and non-register auxiliary columns
remain parameters for the separate unfinished constraint groups. This is a
complete register-group constructor, **not full receipt TableLocal or complete
traffic**, and not a succinct-certificate admission result.

Latest checked order after `RcptBoundaryCarry`: `RcptCurrentRegs`, `RcptRegGates`,
`RcptGasTransport`, `RcptPhysicalGasBoundary`, `RcptActiveBoundaryRegs`,
`RcptLastPlans`, `RcptFinalSegment`, `RcptFinalRegs`, `RcptPhysicalRegs`.
Their matching exact audits have 4+5+3+1+2+3+5+3+2 = 28 guards; cumulative
skeleton/native/physical audit total is **224**. All pass with explicit Lean
`-j1`, both strict implicit-variable flags, the 16 GiB process limit and
read-only external dependencies. Sources and compiled overlays remain separate
from frozen/trusted files.

**Unified emission/register checkpoint:**
`RcptEmittedTrace.emittedReceiptTrace_regs_emit` (namespace `RcptSkeleton`)
proves all 189 cEmit and all 200 cRegs equations on one concrete
`emittedReceiptTrace`. The executable extension overwrites exactly emission
columns 31..42 with values evaluated from the unchanged emission catalog. A
checked footprint proves these expressions never read their own output columns
and the extension preserves every register equation. One-hot state controls,
active flags and Boolean refund flags are derived from actual row plans; header
refund flags are concretely zero. The assumptions remain ordinary receipt wf,
actual PH_OWN public bytes and physical row capacity. Digest streams and gas/
deposit auxiliary bytes must still be bound to native semantics; this checkpoint
does not establish complete traffic or TableLocal.

Checked actual constraint inventory: cStates248, cEmit189, cRegs200, cChars61,
cKey49, cSys14, cRoute18, cGas40, cDep39, cEnd23, total881. Thus 389 polynomials
are jointly proved on this trace; the other492 remain (with reusable earlier
routing/control pieces). Latest order: `RcptEmitPatch`, `RcptEmitCatalog`,
`RcptEmitRules`, `RcptEmitLocal`, `RcptEmittedTrace`. Their exact audits add
5+7+4+4+4=24 guards, for **248 cumulative renderer guards** under strict Lean
implicit-variable settings. The numeric count is a constraint-group checkpoint,
not a percentage of full certificate completion.

### Concrete Boolean trace extension (2026-10-08)

`RcptBooleanInputs`, `RcptBooleanCells`, `RcptBooleanTrace`, and
`RcptBooleanLocal` strictly compile with both implicit-variable flags disabled.
Their 19 exact axiom guards pass (267 renderer guards cumulatively).
`booleanReceiptTrace_regs_emit_bool` proves 200 register, 189 emission, and
119 Boolean polynomials jointly on one concrete trace. The Boolean polynomials
are proved members of unchanged `cStates`; 129 structural state polynomials
and the remaining semantic families are still open.

The constructor specializes `emittedReceiptTrace` by normalizing only Boolean
caller parameters. Native controls, key tags, refund flags and GP token bits
are Boolean by construction. `boolInput_preserves` proves already-Boolean
flags unchanged. This is not a proof that arbitrary normalized gas/key flags
have their required native semantic meanings; those identities and actual
native digest binding remain separate obligations. No full `TableLocal`,
complete traffic, certificate admission, or validator replacement is claimed.

`RcptStateCurrent` and `RcptStateContinuation` additionally close all26
continuation polynomials on that same Boolean trace, with 7+4 exact guards
(278 cumulative). Actual planned-neighbor classification proves interior
advancement; endpoint and padding gates close boundary/wrap cases.
`booleanReceiptTrace_regs_emit_bool_continuation` jointly proves534 of881
receipt polynomials;103 structural `cStates` equations remain, alongside all
remaining semantic families. Full first/last control also requires nonempty
source lists and strictly fewer active rows than physical height. These are
not implied by the non-strict capacity premise used at this checkpoint.

### Native field endpoints and transitions

Five further modules, `RcptStateLastIndex`, `RcptStateLastIndexPhysical`,
`RcptStateBoundary`, `RcptStateSuccessors`, and `RcptStateSuccessorPhysical`,
strictly compile; their 28 exact axiom guards pass (306 cumulative).
The unchanged 23 last-index equations, two boundary reset equations and22
successor equations now hold on the same concrete Boolean trace. Field sizes
come from native receipt well-formedness; actual nested source/list/receipt
order proves the successor choices, including real refund branches, empty
lists and terminal padding. `booleanReceiptTrace_structural_checkpoint`
jointly proves581 of881 receipt polynomials. It explicitly requires strict
active-row capacity, as needed to leave padding;56 structural `cStates`
constraints and other semantic families remain open.

The native receipt-first/end flags are now checked in `RcptStateReceiptFlags`,
`RcptCurrentFamily`, and `RcptStateReceiptEnd` (12 more exact guards).
The joint flag checkpoint contains586 unchanged polynomials. `RcptStateSizes`
adds the two exact receipt/refund offset equations on the same trace (five
exact guards); these arithmetic equalities are derived from the executable
native length functions, without extra offset assumptions.

`RcptNativeCapacity` (two guards) derives activeRows≤2,147,802<2^22 from actual
successful `prepD0` (source count≤1984) and actual `applyNewChunk` of the
flattened native receipt list (all receipt count≤4481, including system).
It retains the exact ordinary source-plan length correspondence and accepted
context gas-limit bound as semantic linking premises. Every source receipt
list also has length<2^16. No historical hypothetical56-byte entry bound is
used. Renderer audit total is325 guards; full `TableLocal` remains unfinished.

### Physical state checkpoint: 617 unchanged polynomials

`RcptStateTableEnds` closes all six initial conditions, final inactivity and
padding absorption (five exact guards). `RcptStateReceiptContinuity` and
`RcptStateReceiptCarry` prove all21 receipt-constant carry equations from the
actual nested plan order, including empty sources and the final active row.
`RcptStateCheckpoint.booleanReceiptTrace_state_checkpoint` combines these
with previous groups into617 unchanged polynomials on one concrete physical
trace; the list length is kernel checked. These three modules add7+8+2 guards,
for347 renderer guards cumulatively. No shared receipt, field successor,
current-cell agreement, or final-receipt assumption is supplied externally.

Twenty `cStates` equations remain: header/list counters and offsets, boundary
flags, two header carries, two list carries, and refund-implies-surplus. The
last obligation still needs the actual native refund flag/gas semantics;
Boolean normalization alone does not discharge it. Full receipt `TableLocal`
continues to require the other semantic constraint families.

### Native state family closed (2026-10-08)

The shared physical log22 renderer now proves all 248 `cStates`, all 200
`cRegs`, and all 189 `cEmit` polynomials together (637 of the 881 active receipt
polynomials). `RcptStateCoverage` checks exact symbolic coverage; the remaining
refund constraint is discharged by `RcptNativeRefundLocal`, then composed by
`RcptNativeStates.booleanReceiptTrace_native_states`.

The refund flag is executable: ordinary receipts refund exactly when
`G * (receipt.gasPrice - min receipt.gasPrice ctx.gasPrice)` is nonzero;
system receipts never refund. The `ge` flag independently compares the two gas
prices. `RcptNativeRefundResult` proves the exact refund suffix of a successful
native ordinary receipt and preservation of refunds in the system branch.
`nativeInputs_flags` supplies flag consistency for the native input constructor.

Capacity uses the actual successful-preparation source count (at most 1984)
and successful native receipt execution count (at most 4481, including system
receipts), giving at most 2,147,802 active rows, strictly below log22. The source
list correspondence, native receipt well-formedness/nonemptiness, execution,
gas-limit bound, and prepared public own-shard bytes remain explicit semantic
inputs. There is no assumed row bound or physical neighbor classification.

New exact axiom audits: entity/list-boundary closure 33, native flags/refund/full
states 11; renderer cumulative total 419. Checks use both strict auto-implicit
flags and bounded Lean `-j1`. All checked axioms are standard. This is not yet
full `TableLocal`: the remaining 244 account/key, system, routing, gas, deposit,
and finalization polynomials and global traffic/native digest correspondence
still require composition on the same trace.

### Finalization and native refunds (2026-10-08, subsequent checkpoint)

`RcptNativeEndCheckpoint.booleanReceiptTrace_native_end_checkpoint` proves
all 23 `cEnd` constraints jointly with the previous families: **660/881** on
the same physical log22 trace. `FinalPublicBytes` explicitly requires the raw
public count, body-length and token-burn byte bindings; connecting those bytes
to the actual prepared statement remains an integration obligation.

These endpoints have native meanings already proved independently:
`booleanReceiptTrace_lastR_position` locates the actual final active row;
`booleanReceiptTrace_final_metadata` derives exact count/body totals from the
list plan; `booleanReceiptTrace_final_tokens` binds all 16 token bytes to the
successful native execution. `applyReceipts_refund_ledger` and
`applyNewChunk_refund_ledger` derive the exact ordered outgoing refund sequence,
and `applyNewChunk_planned_body_length` proves its actual encoded body length
is the renderer's endpoint, including system receipts and empty source lists.
The numeric u32 bounds follow from native receipt count and receipt wf, rather
than being additional capacity assumptions.

The 32 byte-local character equations were also identified as definitionally
the unchanged legacy equations (`RcptCharLocal`) and their existing kernel
proof reused. They are not included in the 660 physical-trace total until the
actual byte/character-column transport is complete. Remaining physical local
families: chars61, key49, sys14, route18, gas40, dep39 (221 polynomials).

New exact audits after the 419-guard checkpoint: digest metadata8, final
endpoints/public composition11, native refund ledger/body4, character primitive3;
**445 cumulative guards**. All strict single-file checks passed with both
auto-implicit flags disabled. No active-table or trusted-spec changes.

### Native character transport composed (2026-10-08)

`RcptCharacterComposition.booleanReceiptTrace_native_character_checkpoint`
now checks **692/881** receipt constraints jointly. The first32 `cChars`
equations are installed on the actual native predecessor, receiver and signer
bytes; their validity follows from each native receipt's `wf`. Non-string
rows and padding have zero character scratch columns. The character and digest
metadata overlays provably commute, so this is the same concrete trace as the
prior register/state/emission/end composition, rather than independent traces.

Dependency order after `RcptCharLocal`: `RcptNativeCharacters`,
`RcptCharacterCells`, `RcptCharacterZero`, `RcptCharacterPhysical`,
`RcptCharacterComposition`. New17 exact guards all pass, **462 cumulative**.
Remaining physical polynomials: chars29, key49, sys14, route18, gas40, dep39
(total189). `FinalPublicBytes` and the native digest-byte/global-traffic
integration obligations remain explicit and unchanged.

### Native character checkpoint: 707 / 881

The same physical `booleanReceiptTrace` now satisfies all six predecessor/system
character equations, in addition to the 701-constraint separator checkpoint.
`RcptPredecessorComposition.booleanReceiptTrace_native_predecessor_checkpoint`
uses actual native predecessor bytes, the fixed `system` comparison stream,
and explicit field inverses; its next-row proof uses the real planned receipt
successor and physical height. Scratch writes commute with character, length,
and digest metadata assignments. This does not yet prove full `TableLocal`.

The unchanged V3 `pReceipt` decoder already requires named receivers.
`RcptNativeNamed.appliedReceipts_named` lifts that exact parser check through
witness dictionary membership to the actual applied receipt list. System
predecessors remain permitted; no strengthening of `Receipt.wf` is used.

Strict dependency order after the 701 checkpoint:
`RcptPredecessorScore`, `RcptPredecessorFrame`, `RcptPredecessorBytes`,
`RcptPredecessorArithmetic`; independent `RcptNativeNamed`; then
`RcptPredecessorCurrent`, `RcptPredecessorCurrentPhysical`,
`RcptPredecessorStep`, `RcptPredecessorStepPhysical`,
`RcptPredecessorCommute`, `RcptPredecessorComposition`.
Their `Audit`-prefixed tests contain 30 exact axiom guards, bringing the
renderer audit total to 511. Checks use both auto-implicit flags disabled,
Lean `-j1`, 16 GiB memory limit and the established isolated overlay imports.

Remaining: fourteen named-receiver equations, key 49, system 14, routing 18,
gas 40 and deposit 39. Raw prepared-public endpoint binding and actual digest
stream/global traffic binding remain explicit integration work.

### Native named receiver checkpoint: 713 / 881

`RcptNamedInverseComposition` adds the three receiver score/inverse checks.
`RcptNamedEndComposition` adds their three endpoint equations on the identical
trace, now totaling 713 constraints. `appliedInputs_named` derives the named
receiver predicate from actual decoded source witness and exact applied receipt
mapping. The shared scratch assignment leaves system predecessors supported.
`RcptHexCells` also binds physical `hexE` to the actual native receiver byte's
hexadecimal predicate for the remaining progression equations.

After the predecessor checkpoint, strict dependency order is `RcptNamedScore`,
`RcptNamedFrame`, `RcptNamedInversePhysical`, `RcptNamedCommute`,
`RcptNamedInverseComposition` (16 exact guards); then `RcptNamedArithmetic`,
`RcptNamedEnd`, `RcptHexCells`, `RcptNamedEndComposition` (11 exact guards).
The cumulative audit total is 538. Eight character equations remain, plus the
previously listed key/system/routing/gas/deposit families and global binding.

### Full character family: 721 / 881

`RcptCharacterComplete.booleanReceiptTrace_native_characters_complete` now
proves **all actual `cChars`**, alongside all `cRegs`, `cEmit`, `cStates`, and
`cEnd`, on one physical log22 trace. The coverage lemma checks membership in
the actual active family, rather than merely counting a collection of helpers.
The last five equations use exact first/second receiver bytes, hex flags and
physical next-row accumulator updates; first rows have a real successor because
native account validity derives receiver length at least two.

Stable continuation after 713: `RcptNamedFixed`, `RcptNamedFixedComposition`
(5 guards), then `RcptNamedCells`, `RcptNamedStart`, `RcptNamedStep`,
`RcptCharacterComplete` (14 guards). All strict checks and exact guards pass;
the cumulative renderer guard total is **557**. Remaining polynomial families:
key 49, system 14, routing 18, gas 40, deposit 39 (160 total). Native public
endpoint and digest/global traffic bindings remain explicit as before.

### Full system family: 735 / 881

`RcptSystemComplete.booleanReceiptTrace_native_system_complete` adds every
actual `cSys` equation to the same physical log22 trace. Native equality and
length modes are computed from receipt bytes. Equal-length unequal names use
an executable first unequal byte, with a proved index bound and nonzero field
difference; unequal lengths use their nonzero bounded length difference.
The SREC lookup count is initialized, advanced at the actual physical successor,
and checked at the final signer row. Header and padding lookup gates are zero.
Scratch/header commutation preserves every previously proved family.

Strict new dependency order: `RcptCurrentInputFamily` (1 guard),
`RcptSystemFrame` (3), `RcptSystemCells` (3), `RcptSystemArithmetic` (3),
`RcptSystemIdentityLocal` (7), `RcptSystemCounter` (4),
`RcptSystemLookupArithmetic` (3), `RcptSystemLookupLocal` (5),
`RcptSystemLookupPhysical` (2), `RcptSystemCounterPhysical` (2),
`RcptSystemCommute` (7), `RcptSystemComplete` (4). Their exact Audit-prefixed
checks all pass, bringing the cumulative count to 605 guards.
Remaining polynomial families are key49, routing18, gas40 and deposit39 (146).
SREC physical traffic aggregation and the other global bindings remain separate.

### Exact physical SREC balance

`RcptSystemCertificate.booleanReceiptTrace_native_systemBalance` now proves
ordered equality of all physical SREC sends and receives on the same log22
trace used by the 735-constraint theorem. The proof enumerates actual receiver
and signer rows, covers every list header and padding row, and derives trace
capacity from actual preparation and successful native execution. Equal-name
mode emits the entire equal-length byte sequence; unequal equal-length mode
emits the same selected mismatch position on each side; other modes emit none.
No SREC balance premise is used.

Strict dependency order: `RcptSystemTraffic` (6 exact guards),
`RcptSystemTrafficPlan` (4), `RcptSystemTrafficRows` (4),
`RcptSystemTrafficPhysical` (2), `RcptSystemCertificate` (1).
All pass; cumulative renderer audit count is 622. The remaining 146
polynomials and non-SREC global bindings are still open.

### Routing integration groundwork

The original native interval-frame proof is now adapted to the actual shared
receipt registers: receiver rows retain their total receiver length, while
first RID rows retain index zero and the real receipt-ID byte. All eighteen
routing equations are invariant under these state-specific adjustments.
A checked restricted-column footprint avoids requiring unrelated receipt cells
to equal the standalone frame. The executable routing assignment claims shared
scratch only on receiver/first-RID rows; inactive gates are zero and other
states retain their own scratch. Boolean normalization preserves every routing
bit, and the actual stream/token/receipt wrappers preserve all active routing
scratch values. Both receiver and first-RID current-row matches are checked.

Strict dependency order and exact guards: `RcptRoutingAdjusted` (4),
`RcptRoutingFootprint` (3), `RcptRoutingFrame` (4),
`RcptRoutingBoolean` (3), `RcptRoutingCells` (3),
`RcptRoutingReceiver` (3), `RcptRoutingRid` (1). All 21 pass
(cumulative 643). Physical successor transport and inactive-row composition
remain; this groundwork does not yet increase the 735/881 full-trace count.

### Full routing family: 753 / 881

`RcptRoutingComplete.booleanReceiptTrace_native_routing_complete` now proves
all 18 actual cRoute polynomials on the same physical log22 trace as the prior
735 families. The proof derives the exact receiver successor from the actual
planned row list, including the last receiver byte followed by the first RID
row. It excludes padding and unrelated receipt boundaries at that transition.
First RID rows do not constrain irrelevant next-prefix cells. Inactive receipt
rows, list headers, and all padding rows satisfy the zero-gate cases. Concrete
scratch/header commutation preserves every preceding constraint family.

New strict dependency order after the seven groundwork modules:
`RcptRoutingInactive` (3 exact guards), `RcptRoutingNext` (4),
`RcptRoutingRowLocal` (3), `RcptRoutingNeighbors` (2),
`RcptRoutingPhysicalReceiver` (2), `RcptRoutingPhysical` (2),
`RcptRoutingCommute` (7), `RcptRoutingHeaderCommute` (3),
`RcptRoutingComplete` (2). All 28 guards pass (cumulative 671).

`RcptRoutingNativeSelection` then computes the interval and its public index
from the actual native layout. Successful preparation/walking/witness decoding
and the actual ordered receipt list discharge interval containment, positive
upper endpoint bytes, index <128, and normalized-public request-key coverage.
`RcptRoutingNativeComplete` composes these facts with all753 constraints and
sets each receipt's q constant to that native selected index. Its theorem has
no supplied interval/routing-validity premise. These two modules add 3 exact
guards, all passing (cumulative 674).

Remaining actual polynomial families: key49, gas40, deposit39 (128 total).
Candidate seven-bit q equations and BND rank/traffic composition still require
integration with this concrete trace; the original 18 routing equations alone
do not close that candidate repair. Native digest/public endpoint and remaining
global bus bindings are also still explicit. No full TableLocal or final
certificate admission is claimed.

### Native key assignment and six physical key equations

`RcptKeyFrame` constructs both account/access-key symbol slots from native
receipt bytes, state positions, and the previously computed system-equality
mode. Public-key nibble scratch is assigned only on PK rows. Account and
access-key provider IDs are explicit constructor inputs; no lookup ownership
or absent-key semantics are inferred from those inputs.

`RcptKeyGatePhysical.booleanReceiptTrace_keyGates` proves the actual first two
key emission gate equations and the four FINAL/AKC gate/value equations over
all physical rows, including headers and padding. The account prefix's
`kz` transition and native byte/nibble bounds are separately checked. This
six-equation theorem has not yet been composed with the existing753 trace;
that composition must preserve character-length scratch and the other
assignments, and the remaining43 key equations still need checking.

Strict dependency order: `RcptKeyFrame` (3 exact guards), `RcptKeyGates` (2),
`RcptKeyCells` (1), `RcptKeyFinalArithmetic` (4), `RcptKeyGateLocal` (3),
`RcptKeyGatePhysical` (2). All15 pass, cumulative689. The full same-trace
constraint count remains753 until the key-family composition is completed.

### Complete native key family on the shared trace

`RcptKeyNativeComplete.booleanReceiptTrace_native_key_complete` now proves
**802 of 881** receipt constraints together on the same physical log22 trace.
All49 `cKey` equations are included: native account and signer character
nibbles, native public-key bytes and nibbles, exact positions/end markers,
the physical account-prefix continuation, and gate/FINAL/AKC equations.
Headers and terminal padding are covered. `RcptKeyCommute` proves assignment
compatibility, including the shared length/PK scratch with disjoint states.

Provider account/access-key IDs remain explicit constructor inputs; their
global authentication and absent-key semantics are not proved by these local
equations. The candidate q7bit/BND rank integration and native digest/public
endpoint bindings remain separate. Gas40 and deposit39 are the remaining
original local polynomial families. No full TableLocal or certificate
admission is claimed.

Stable additional dependency order (matching exact `Audit<module>` guards):
`RcptKeyPkBits`3, `RcptKeyCharNibbles`3, `RcptKeyCharacterCommute`2,
`RcptKeyAccountLocal`3, `RcptKeyZeroPhysical`3, `RcptCurrentBoundedFamily`1,
`RcptKeyAccountPhysical`2, `RcptKeyAccessBytes`3, `RcptKeyAccessLocal`3,
`RcptKeyAccessPhysical`2, `RcptKeyComplete`3, `RcptKeyCommute`7,
`RcptKeyHeaderCommute`3, `RcptKeyNativeComplete`2. All40 strict guards pass;
cumulative729. Checks use both disabled-autoimplicit flags, bounded memory,
and one Lean worker.

### Native gas subtraction and system-price domain probe

`RcptGasBorrowNativeComplete` composes the first four original gas equations
with the802 checkpoint: **806 of881** on one physical log22 trace. Price
bytes, subtraction digits, the complete borrow chain, final comparison,
headers, padding and assignment commutation are checked. This signature
explicitly adds ordinary `GasPublicBytes ctx pub` and `ctx.gasPrice<2^128`;
these still need the final prepared-public/context binding.

`RcptSystemGasDomain` checks a narrower runtime-domain probe: a well-formed
system receipt with gasPrice=u128Max round-trips through actual `pReceipt`
and succeeds under actual `applySystemReceipt` on a revealed account.
Its raw unused surplus at block price0 exceedsu128. The native system
branch ignores gasPrice, whereas the original `cGas` surplus convolution
uses `ge*DE` without a system mask and forces its final carry/overflow zero.
This is not a complete checkD0a acceptance fixture or an AIR soundness
attack. It prevents assuming surplus no-overflow merely from system-runtime
success. A possible isolated repair is to use existing `gq=ge*(1-sys)` for
surplus; active/frozen constraints have not been changed.

Additional audited dependency order: `RcptSystemGasDomain`5,
`RcptGasBorrow`7, `RcptGasBorrowFrame`4, `RcptGasPriceCells`1,
`RcptGasBorrowLocal`2, `RcptGasBorrowCurrent`5,
`RcptGasBorrowTransition`3. All27 exact guards pass (cumulative756).

The gas-borrow composition audits subsequently passed:
`RcptGasBorrowCommute`9, `RcptGasBorrowPhysical`1,
`RcptGasBorrowNativeComplete`2 (cumulative768).
`RcptGasEffectiveNativeComplete` adds the two original `pc`/`gq` equations
on that same trace, **808/881**. Actual native min-price byte selection and
the zero system burn-price mask are derived; the added public gas-price
binding and context width premise remain explicit. Stable audited order:
`RcptGasEffectiveFrame`5, `RcptGasEffectiveLocal`3,
`RcptGasEffectivePhysical`2, `RcptGasEffectiveCommute`13,
`RcptGasEffectiveNativeComplete`2. All25 exact guards pass (cumulative793).

### Complete original gas delay lines

`RcptGasDelayNativeComplete` proves **824/881** constraints on the shared
trace, adding all16 original delay-line equations. Native earlier burn-price
and raw surplus bytes, eight initial zeros, both stream heads, six shifts,
physical neighbor positions, last GP rows, headers and padding are checked.
The raw system surplus is explicitly not claimed to be a refund or to meet
the pending no-overflow condition. Remaining families: gas18 and deposit39.

Stable strict-audited order: `RcptGasDelayFrame`7, `RcptGasDelayCells`5,
`RcptGasDelayLocal`2, `RcptGasDelayFootprint`4,
`RcptGasDelayPhysical`1, `RcptGasDelayCommute`9,
`RcptGasDelayNativeComplete`2. All30 exact guards pass; cumulative823.

Deposit preflight also identifies an unresolved completeness limit:
the original first-DEP-row constraint represents `r-tprev` in9 bits, while
accepted execution may contain4481 receipts. The legacy numeric constructor
assumes `r<512`; this is not a native accepted-domain fact. A later first
read of an initial account requires examining authenticated version allocation,
or an isolated wider difference representation. No full native fixture,
AIR soundness attack, or active constraint change is claimed here.

`RcptAccountRead` proves native `get = find.join` for both trie and child
structures. `RcptNativeBalances` derives the actual decoded pre-account,
amount below the V2 sentinel, total belowu128, and the native storage-stake
condition from each successful ordinary/system receipt application. Its
`nativeBalanceAccount` is executable, and the selected account is proved to
be exactly that read. This is groundwork for deposit rendering, not an
assumption that account version IDs or the9-bit distance bound are valid.
Both modules strict-check;2+4 exact guards pass (cumulative829).

### Checked arithmetic obstructions and isolated repair candidates

`RcptGasContradiction` proves that the original receipt `TableLocal` plus an
actual receipt layout cannot encode gas price `u128Max` against block price
zero. The final surplus overflow equation already contradicts the borrow
stream, without requiring any refund-amount byte-range premise. Together with
`RcptSystemGasDomain`, this exhibits a native-valid, decodable system-receipt
runtime case excluded by the original gas equations. It is not yet a complete
accepted `checkD0a` transition fixture.

`RcptSystemGasCandidate` parameterizes the exact original 40 gas equations and
replaces surplus `ge*DE` with existing non-system gate `gq*DE`. It adds no columns
or equations. All original polynomial evaluations are preserved when `gq=ge`;
system surplus becomes zero. Remaining migration: candidate `GasProduct`
extraction and surplus delay/convolution proofs, corrected honest system
scratch streams, and full same-trace local composition. The active table is
unchanged.

`RcptDepositContradiction` proves the original table cannot represent receipt
index 512 reading initial account version zero. This is a precise local
obstruction, not a full native accepted-transition fixture. The isolated
`RcptDepositAgeCandidate` retains exactly 39 deposit equations and widens the
first-row age from nine bits to thirteen using `xb53..65`. The checked native
4481 receipt bound fits this range, and canonical candidate arithmetic implies
exact natural predecessor ordering. Storage uses overlapping bits only on the
second DEP row; full global scratch-patch independence, real version ownership,
and candidate extraction migration remain required. No `r<512` premise is
introduced.

Strict compilation with both auto-implicit flags disabled and 14 exact axiom
guards passed for these four new modules. Cumulative renderer-lane exact guards:
843. Original same-trace coverage stays 824/881; these isolated candidates are
not counted as active-table completion.

`RcptGasPrepared` and `RcptGasPriceBound` now close both gas-side renderer
boundary premises from actual preparation and native main execution:
`prepD0_native_gas_evidence` supplies prepared-public gas byte equality and the
native context's u128 range from `prepD0`, `walkD0`, and `MainExecutionV3.NativeValid`.
The proof follows the actual block-header u128 parser, selected decoded previous
block, prepared context, and exact static header byte offsets. Twelve exact
guards pass; these facts require no caller-chosen gas equality or range premise.

`RcptSystemGasZero` implements concrete system-branch zero multiplication
scratch and proves all ten candidate burn/refund convolution, carry, and final
overflow equations on actual renderer row pairs with their real interior
successor. It permits arbitrary system gas-price differences. The patch leaves
ordinary receipts and columns outside its explicit ownership set unchanged.
Five exact guards pass. It is still a row-local candidate theorem: full physical
transport, other constraint-group preservation, and candidate extraction remain
open. Cumulative exact guards: 860; original same-trace coverage: 824/881.

`RcptSystemGasFootprint` and `RcptSystemGasPhysical` extend the corrected system
multiplication proof to all physical rows of `booleanReceiptTrace` for
system-only input lists. All ten candidate equations hold through list headers,
empty lists, ordinary field interiors, the final GP endpoint, zero padding, and
wrap; only the ordinary planned-row capacity premise is used. No system surplus
or gas-price bound is required. Five footprint/endpoint guards and one physical
transport guard pass. Mixed ordinary/system composition and preservation of
other renderer groups remain explicit. Cumulative exact guards: 866; active
original coverage remains 824/881.

`RcptNativeSurplus.applyReceipts_refund_amount_bounds` derives corrected refund
product `<2^128` for every receipt in an actually successful native batch,
including system receipts without imposing any gas-price restriction. Five
exact guards pass.

`RcptDepositAgeScratch` checks the entire other-family constraint lists,
structural state constraints, and all interaction multiplicities/messages for
independence from `xb53..65`. The exact old deposit overlap is only its old age
equation and the storage770 equation gated by second-row `r1`. A generic
expression-preservation theorem includes next-row accesses and boundary flags.
`RcptDepositAgeFrame` constructs the thirteen bits on the actual first DEP row,
sets `r1=0` there, proves the new age equation under ordinary `previous≤index`
and native `index<4481`, and proves the overlapping storage equation vanishes.
Authenticated previous-version allocation and full deposit arithmetic/physical
composition remain open. Ten further exact guards pass. Cumulative exact axiom
guards: 881 (a test count, not completed polynomials). Active original
same-trace coverage remains 824/881.

### Mixed native refund flags and token accumulator: 832/881 original equations

`RcptGasFlagNativeComplete` composes all four refund/surplus-sum equations into
the same native mixed trace, preserving the preceding 824 equations. The sum
inverse is justified by actual native refund semantics, bounded byte sums, and
field injectivity. Physical next-row sums include headers, padding and endpoint
handling. Its eight-module package passes 37 exact axiom guards.

`RcptGasTokenNativeComplete` then composes all four gas token-accumulator
equations into that SAME mixed trace. The executable carry chain uses the
actual `receiptPlanToken`; numeric bounds come from successful native execution
at the receipt's true global index, not a bound on arbitrary fabricated plans.
The final carry is zero and physical successor carry checks include all
boundaries. Thirteen auxiliary commutations preserve the earlier 828 equations.
Its ten-module package passes 37 exact guards.

Original same-trace coverage is now **832/881**. Cumulative exact axiom guards
are **955**. Remaining original families are gas products10 and deposit39;
full-domain completion must use the isolated gas/deposit repairs. In particular,
the candidate system fix must migrate both surplus product equations AND the
surplus delay stream, so its final coverage must be reported separately from
the unchanged original table. No full original-domain TableLocal or final
succinct-certificate claim is made.

### Candidate native products and corrected delays: 26 equations together

`RcptGasProductDelayPhysical.booleanReceiptTrace_acceptedGasProductDelay`
constructs both corrected product families (10 equations) and corrected delay
family (16 equations) on the SAME physical mixed receipt trace. All native
ordinary/system inputs are supported. Product carries are executable convolution
carries, bounded by 840; the final carry and top-byte overflow gates are derived
from actual native product bounds. `applyNewChunk_product_bounds` extracts both
burn and actual refund bounds from successful execution, with no surplus-price
restriction added to system receipts. Headers, empty lists, final GP rows,
padding, and physical wrap are covered.

The candidate uses `gq * DE` for the actual refund-price stream, including its
delay registers. It does not mutate the active table. The ordered new modules
are `RcptGasProductArithmetic`, `RcptGasProductPrices`, `RcptGasProductFrame`,
`RcptCandidateGasDelayCells`, `RcptCandidateGasDelayLocal`,
`RcptGasProductLocal`, `RcptGasProductCells`, `RcptGasProductReceipt`,
`RcptGasProductEndpoint`, `RcptGasProductPhysical`,
`RcptGasProductNativeBounds`, `RcptCandidateGasDelayFootprint`,
`RcptCandidateGasDelayPhysical`, and `RcptGasProductDelayPhysical`.
All strict checks and 50 exact axiom guards pass; cumulative exact guards 1005.
Original same-trace coverage remains **832/881**. The candidate 26-equation
conjunction is not added to that number: preserving the remaining 816 original
equations on this corrected physical trace is still required, followed by the
39-equation deposit migration and native/authenticated account linkage.

### Complete candidate gas migration: 842/881 on one native mixed trace

`RcptCandidateGasProductNativeComplete.booleanReceiptTrace_native_candidateGas_complete`
now composes all 40 corrected gas equations with all eight previously completed
families on the SAME concrete log22 trace. The candidate trace preserves 816
other equations while replacing the old delay stream and supplying product
carries. Scratch commutations preserve byte/control/character/key/routing/system,
register and emission proofs. The actual successful native execution derives
burn/refund product bounds; no new gas-price or refund restriction is imposed on
system receipts. The public gas-price, source list correspondence, named receiver,
native execution and other previously explicit native-boundary premises remain.

Strict checking and 32 new exact axiom guards pass for ordered modules
`RcptCandidateGasDelayCommute` (9), `RcptGasProductCommute` (9),
`RcptGasCandidateCommute` (4), `RcptCandidateGasDelayNativeComplete` (2),
`RcptCandidateGasFlagNativeComplete` (2),
`RcptCandidateGasTokenNativeComplete` (2), and
`RcptCandidateGasProductNativeComplete` (4). Cumulative exact guards: 1037.
Candidate coverage is **842/881**; original unchanged coverage remains
**832/881**. The active table is untouched. Remaining local completeness work is
candidate deposit39, including actual account/version ownership, followed by
all interaction multiplicity and native digest/value linkage obligations.

### Candidate arithmetic renderer: all 881 equations and TableLocal

`Assembly.RcptCandidateNativeComplete.booleanReceiptTrace_native_candidate_complete`
now proves all 881 candidate equations on one concrete physical log22 trace.
`Assembly.RcptCandidateNativeTable.booleanReceiptTrace_native_candidate_tableLocal`
packages that same trace into `TableLocal receiptArithmeticCandidate`, including
all actual interaction multiplicity bits and the height bounds. This isolated
candidate changes the gas surplus/delay equations and the deposit version-distance
width; it preserves the original receipt interactions, columns, and log22 bound.
It does **not** silently install the separate routing-q repair or normalized public
boundary representation. Original-equation coverage remains 832/881.

The deposit accounts come from `nativeDepositLedger` for the same successful
`applyNewChunk`, beginning at its actual post-scheduler trie. Exact receipt order,
account reads, arithmetic validity, receipt-index bounds, and strict row capacity
are derived. Earlier receiver occurrence numbers supply bounded version-distance
witnesses; global MEM provider/version ownership remains a separate obligation.
Existing theorem premises retain the actual public byte bindings, named receiver
slice, receipt/refund correspondence, and gas-price bound. Digest streams are
still explicit inputs; this result alone does not authenticate their native hashes.

Strict Lean checks used both auto-implicit flags disabled and bounded `-j1`.
New exact axiom audits, all standard axioms:

- Physical deposit: Footprint4, Endpoint2, Idle3, Physical1, PlanLedger5,
  NativePhysical1 (16 guards).
- DepositCommute12, DepositFrameCommute3 (15 guards).
- DepositFinalCommute17, DepositGlobalCommute3, CandidateNativeComplete2
  (22 guards).
- CandidateTableLocal3, CandidateNativeTable1 (4 guards).

All module names above carry the `Rcpt` prefix, and their audit files are
`zk-formal/test/Audit<module>.lean`. Candidate soundness migration, degree/table
installation, routing-q integration, and global traffic/native digest binding
remain open. No full succinct certificate or stateless-verifier replacement is
claimed by this renderer checkpoint.

### Routing integration and changed arithmetic soundness

`RcptCandidateRepairedTable.booleanReceiptTrace_native_repaired_tableLocal`
now produces full `TableLocal ReceiptCandidateRouting.candidateTable` on the
same native execution's patched log22 trace: **882 constraints**, including the
seven-bit routing-index check. The q bound comes from actual native bounded
interval selection. Candidate control/predecessor proofs establish the cyclic
patch shape; no old gas/deposit local validity is assumed. All original bus
counts are exactly unchanged by the q patch. This extends the arithmetic-only
checkpoint above; global public boundary installation remains an independent
assembly boundary.

The changed arithmetic extraction has also been migrated to candidate-local
premises. `ReceiptCandidateProof.layout_of` constructs the original `Layout`
from actual candidate-local rows. `ReceiptCandidateProof.arith_of` proves the
unchanged native receipt arithmetic clause using candidate local validity,
that layout, and explicit authenticated byte ranges. System surplus is masked
in the extracted SN stream and the comparison gate is derived, not assumed.
Balances, storage/stake, burn/refund convolutions and token recurrence are checked.

Widening age9 to age13 changes its no-wrap prerequisite: the old `P-512`
condition cannot be reused. `deposit_previous_row` uses `tprev<P-8192`;
`deposit_previous_provider_bound` derives it from the ordinary authenticated
version bound `tprev≤2^22`. Global MEM provider ownership must still supply that
bound. Candidate whole-receipt Wf/traffic extraction and native byte/digest
ownership are not yet fully assembled.

Exact candidate soundness audits: Bounds5, GasSound4, Regs8, GasCompare9,
GasProduct12, Deposit17, GasTokens5, Segs7, Layout15, ReceiptBalance1,
ReceiptArithmetic1 (84 guards). Routing integration adds Control41,
RoutingPatch5, RoutingTrace4, RoutingPredecessor2, RoutingNative1,
RepairedTable3 (56 guards). These counts refer to reproducible exact axiom
audits, not additional polynomial equations. Source migrations retain source
hashes and explicitly change table/membership premises; common semantic data
types are reused.

### Repaired receipt traffic soundness

The main-workspace `Assembly/RcptCandidateRepairedTraffic.lean` now proves
`repaired_extract_traffic`: fully repaired candidate `TableLocal` yields one
actual physical `ListChain` and complete `TableTraffic` for its exact extracted
list views. This covers BYTES, RCL, KEYNIB, MEM, RIDS, MPOS, SREC, AKC, BND,
FINAL, DIGEST, both directions, and all other bus identifiers. It does not assume
old receipt `TableLocal`, public ranges, a routing provider, or memory provider
ownership. The interactions remain exactly those of the repaired table.

Strict checks use both auto-implicit options disabled and bounded Lean `-j1`.
New exact axiom audits: list/header chain 21 modules/78 guards; BYTES/RCL view
composition 9/36; memory/position/access/signer/boundary traffic 15/63;
FINAL/DIGEST 8/33; KEY and all-bus composition 20/78; repaired wrapper 1/2.
Each migrated module records its original source SHA256. All guards report only
standard Lean logical axioms. These checks extend earlier base traffic and
per-receipt bytes checkpoints.

Per-receipt semantic `wf_of_route` has also been migrated, retaining an explicit
previous-version provider bound of `2^22`; the expanded thirteen-bit age proof
must not reuse the former `P-512` no-wrap premise. Global semantic Wf/token and
native hash ownership composition remains separate work. This is not a complete
succinct-certificate claim or a claim that the original 881 constraints suffice.

The global semantic migration is now checked as well (20 modules/77 exact
guards), with `RcptCandidateRepairedSound` combining `RcptV3Wf` and complete
traffic for the same chain (2 guards). Public count/body ranges and memory
version ownership remain explicit. `RcptCandidateMemoryVersion` (4 guards)
derives the needed previous-version bound from positive physical MEM receive
counts: each extracted receipt contributes its byte-zero account read, and its
version is canonical directly from field decoding. The global provider inventory
and bus balance must still establish the bound on those physical receives;
age no-wrap is not assumed or circularly inferred from receipt Wf.

`RcptCandidateMemoryProviders` further derives that version bound from the actual
provider forms (4 exact guards): account opens have version zero; receipt writes
have their real global index plus one, bounded by physical receipt count/height
without assuming receipt Wf. `repaired_sound_of_mem_providers` leaves only the
family-level count-domination obligation that every receipt MEM receive is
supplied by the account opens or the same extracted receipt writes. Global MEM
balance and exclusion of other sender families must establish this obligation.

### Concrete family memory and public admission

`RcptCandidateFamilyMemory` now checks the actual fused candidate sender
inventory: MEM send counts equal the projected repaired receipt component plus
account openings at physical table 6. All other components are excluded by their
actual interaction lists. Global balance therefore bounds every positive fused
MEM receive version by `2^22`, without receipt Wf or age-order assumptions
(12 exact guards).

`RcptCandidateFamilyPublicMemory` adapts this to `HoldsP`, rather than incorrectly
requiring public-free balance on every bus. The actual nine prepared public
segments send and receive no MEM messages. With the candidate's concrete tables
and these segments, `HoldsP` alone yields the memory-version bound (6 guards).

`RcptCandidatePublicAdmission` derives both receipt public ranges from successful
native preparation, actual `pubFit`, and the static configuration condition
`AP.maxPub + 8 < P` (11 guards). The proof does not interpret `pubFit` as a bound
on the entire public byte array: it uses the actual body segment and exact
modular u32 decoding. It also supports the bounded-routing prepared statement,
which preserves the header and body, and provides conversions to the unchanged
source-link `ReceiptPublicRanges` type. No new native-domain restriction or
statement-size premise was added.

Strict checking for these three files uses a private symlink-only union at
`/tmp/nearproof-d3-family-overlay` (assembly, root UPS, receipt, and HPL compiled
imports). Existing worker overlays and external build trees remain untouched.

### Native outcome and physical leaf identity (2026-10-08)

The eight additive modules `RcptNativeOutcomes`, `RcptNativeFieldPositions`,
`RcptNativeByteCells`, `RcptNativeSlices`, `RcptNativeLeaf`,
`RcptNativePlanOrder`, `RcptNativeLocations`, and `RcptNativeLeaves` compile
with both implicit-binding checks disabled; their matching `Audit` files
contain 27 exact axiom guards. The outcomes theorem covers both native system
and ordinary branches and preserves the complete execution order.

`executed_leaves` reads views directly from the actual q-patched boolean
receipt trace at executable offsets (including empty-list headers) and proves
their leaf preimages equal the successful native execution's ordered outcome
preimages. Receipt-ID length 32 is explicit, and the supplied XLH digest stream
is computed from the native outcome. No assumed leaf-list identity is used.

This is not yet the complete honest renderer certificate. The remaining
bridges are: identify these executable located views with the canonical
extracted physical `ListChain`; instantiate all renderer register/SHA premises
with the same native outcome/refund streams and native flags; derive ID width
from accepted receipt decoding when composing the final constructor. Choosing
the native digest stream alone does not prove its SHA preimage traffic matches
all emitted PEO bytes.

The canonical-view gap above is now closed by seven additional modules:
`RcptNativeShapeIdentity`, `RcptDecodedEntities`, `RcptNativeEntityHeads`,
`RcptDecodedHeadIdentity`, `RcptDecodedNativeSequence`,
`RcptCanonicalNativeViews`, and `RcptCanonicalNativeLeaves` (18 exact guards).
The proof compares complete ordered physical partitions, using native head
flags, uniquely decoded shape columns, exact row lengths, and terminal padding.
`canonical_executed_leaves` binds the SAME extracted `ListChain` views to actual
native outcomes, deriving receipt-ID width from native receipt well-formedness.
The remaining honest-construction obligation is instantiating the repaired
TableLocal theorem with these native outcome/refund digest streams and all
register/SHA preimage compatibility premises. The new theorem does not assume
leaf identity or the equality of extracted and located views.

Native PEO compatibility now also checks: `RcptNativePeoPositions`,
`RcptNativePeoSlices`, `RcptNativeBurntCells`, and `RcptNativePeo` provide 10
exact guards. `native_peo_slice` reads receiver/refund-ID/burnt fields from the
same complete arithmetic renderer and proves native partial-outcome encoding.
`native_peo_digest` proves that its actual PEO digest hashes those emitted PEO
bytes. Both ordinary and system token semantics are included; the native refund
flag correspondence remains explicit. `nativeDigests` supplies both native
refund IDs and partial-outcome hashes and specializes the prior outcome stream.
Global canonical membership transport and the other receipt job families
(RC/RID/refund serialization) still require composition.

`RcptCanonicalPeoDigest` now transports the PEO hash equation to every SAME
canonical extracted receipt (one guard). `RcptNativeRid` and
`RcptCanonicalRefundDigest` establish the RID hash equation from actual receipt
ID/public-height bytes (three guards). `RcptHeightPrepared` derives those height
bytes from actual prepD0/walk/native execution and prepared public encoding
(six guards). RC/source-list encoding and refund-body serialization remain to
be composed before claiming the complete honest receipt SHA contract.

### Native RC and refund serialization closure (2026-10-08)

Twelve exact guards across `RcptNativeFieldBytes`, `RcptNativeInputSlices`,
`RcptNativeEncoding`, `RcptNativeRefundAmount`, and `RcptNativeRefundEncoding`
bind the physical input fields and complete arithmetic refund amount to native
receipt/refund encodings. `RcptCanonicalNativeEncoding` and
`RcptCanonicalRefundEncoding` add four guards for exact ordered canonical
encodings and actual native outgoing receipts.

The six modules `RcptGroupTokens`, `RcptEncodingTokens`,
`RcptCanonicalGroupedEncoding`, `RcptNativeHeaderRanges`,
`RcptNativeRcHeaders`, and `RcptCanonicalRcPayloads` add 14 exact guards.
`canonical_rc_payloads` proves exact ordered per-source native RC preimages,
including physical list headers, empty lists, and repeated sources. Header
byte ranges and count equality are derived from the honest trace and its actual
ListBlockWf; no grouping/count equality premise is introduced.

`RcptOutcomePrepared` adds six guards. Its final theorem derives normalized
public PH_OUT bytes from prepD0/walkD0/decodeW/checkD0 and the SAME native
execution witness, using native execution uniqueness. It does not assume the
outcome-root equality. All checks use both strict implicit-binding flags and
exact axiom guards. There is no claim that arbitrary successfully prepared hint
bodies equal native outgoing bytes: final honest construction must retain its
actual hint/body choice when connecting the public refund body.

### Native RC job identity and duplicate output multiplicity

The checked `RcptCanonicalRcJobs` identifies every canonical physical RC preimage
with the ordered native encoding, proves its bytes are below 256, and identifies
its native digest. `RcptSourceInputs` constructs the ordered renderer input lists
from actual prepared last-wins dictionary selections and derives exact equality
to `appliedReceipts` plus the native destination shard from D0a acceptance.
`RcptSourceRcDigest` binds each actual compiled source RC request to that native
preimage. `RcptSourceRcOutputs.sourceRcShaJobs` retains every occurrence preimage
but sets SHA digest multiplicity to `!sourceDup`; its exact digest outputs equal
the computed source blocks' RC requests, and all preimage bytes are unchanged.
This distinction is required: skipped duplicate source headers request no RC
digest. It is not yet a claim that the global job constructor uses these flags.
`RcptSourceRcPreimages` identifies this job inventory's bytes with the SAME
canonical physical receipt lists when instantiated with `sourceInputLists`.
These five modules have 12 exact axiom guards, all strict-checked. Full physical
source digest partitioning and whole-family inventory installation remain at the
global linker boundary.

### Honest canonical receipt SHA capacity and byte contract

`RcptNativeShaLengths`, `RcptCanonicalShaLengths`, `RcptShaLengthCapacity`,
`RcptCanonicalCounts`, and `RcptCanonicalShaCapacity` prove the existing
1,373,299 SHA-row bound for the SAME extracted honest receipt ListChain.
The native receipt serializer gives encoded length ≤347 and native outcome PEO
length ≤133. Preparation and successful execution give actual source-list and
receipt-count bounds; no separate `RcptE.Wf` or assumed receipt SHA-row bound is
required. Ordinary account Wf and the account count ≤8192 remain account-family
inputs. Eight exact guards pass strict checking.

`RcptCanonicalShaBytes`, `RcptMerkleShaBytes`, and `RcptShaByteContract` derive
UInt8 byte bounds for that same receipt-family inventory. RC, PEO, LEAF, RID,
and Merkle branches are discharged from the native trace and public header bytes.
Only account VPOST preimage byte bounds remain an account-specific premise;
`AcctWf.canon` supplies <P and cannot be used as a substitute for <256. Five
exact guards pass. This is a same-trace SHA contract, not yet final certificate
installation or a closed account constructor.

### Complete physical source DIGEST conservation

`SourcePathDigests` proves the executable `proofItems` digest chain: each
intermediate output appears once in the next path request, and the final output
is `rootFromPath`. `SourceBlockDigests` binds that final digest through actual
native `verifyReceiptProof`, with decoded sibling widths; `SourceAcceptedDigests`
derives these facts for the selected dictionary entry at every prepared index.
`SourceBatchDigests` preserves all occurrences and duplicate suppression in the
batch permutation. Finally,
`SourcePhysicalDigests.physical_source_digest_balance` proves:

```
count(expectedDigests(sourceShaMessages))
+ count(expectedDigests(sourceRcShaJobs))
= physical DIGEST receives across all four NativeSourceFour log22 tables
```

The theorem uses actual `checkD0a`, `prepD0`, `walkD0`, and witness decoding;
it introduces no separate hash, path, root, or digest-multiplicity assumption.
All five modules and eight exact axiom guards pass strict Lean checking. The
parent linker still must install this equality into the same full certificate.
