# Queue parser candidate (2026-10-07)

This is an isolated parser candidate, not an admitted AIR or the final queue
read table. The active proof parameters and accepted relation are unchanged.

The semantic foundation is checked in `NearV3/Qv`: exact parser acceptance,
byte-level buffered witnesses, real runtime reads, preservation through the
scheduler and both receipt branches, and executable main/missing read requests.
The obsolete A4 128 KiB bound is not assumed. Repeated and unsorted buffered
shard IDs are preserved. Missing chunks demand only a determinate delayed read.

`Qv.Candidates.ValueTable` has 37 columns, 97 explicit constraints and five
interactions. Kernel checks establish static table well-formedness at degree4
and g2 shape `(37,3,6,3,22)`. The log22 cap is provisional: assembly must prove
capacity from authenticated value bytes and zero-length value markers.
`ValueGen` supplies executable rows. Eleven acceptance/rejection fixtures pass
both integer and actual BabyBear evaluation, including malformed second queue
indices, mismatched buffer counts, truncated headers and mixed segments. `ValueTraffic` additionally proves exact natural VBYTES records for every
empty, buffered and raw generated segment; three traffic axiom guards pass.
Two static shape/well-formedness axiom guards pass. These results do not replace
general field extraction and honest local-constraint proofs. `EmptyLocal` and
`EmptyRender` now prove all local constraints for arbitrary empty-index bytes
and their actual sixteen-row generator, over any commutative ring. `ShardTraffic`
proves exact generated buffered shard-byte records. `RawLocal` and `RawRender`
prove all local constraints for arbitrary raw bytes, including the empty marker
and every padding row of any fitting power-of-two trace, over any commutative
ring. This is connected by trace equality to executable `rawRows`.
`BufferRows` proves the exact 4+24*n row count and pointwise header/entry/padding
indexing for every sized byte-buffer list. `BufferTrace` connects that formula
to the executable generator. These are row-layout facts, not buffered local
constraint validity.
`BufferHeader` reuses the isolated HPL repair’s exact `Spec.U32Bytes` helper
to prove four-byte count reconstruction and zero top byte under count<2^24.
`BufferLocal` now proves all local constraints on all four buffered header rows,
including the empty-vector boundary and the transition into a nonempty vector.
`BufferHeaderRender` connects this to the actual row generator. `RowCells` caches
cell projections to avoid repeated row-list expansion during these proofs.
`BufferRender` now proves every local constraint on every buffered trace row,
including arbitrary entry counts, all entry boundaries, physical last rows and
padding. Its generated-trace theorem requires sized entries, count<2^24 and
4+24*n≤2^log; these remain explicit assembly obligations.
`EmptyPaddedRender` extends empty-index validity to every fitting trace height,
with all padding and the executable row-generator bridge. Thus all three
standalone modes have complete honest local-constraint proofs over any
commutative ring, with explicit fit/encoding premises.
Candidate audit totals twenty-eight axiom guards and eleven fixtures checked in both
integer and BabyBear arithmetic. Record concatenation, read orchestration, sound extraction, actual capacity and
full field traffic remain open.

Rows parse three modes: empty 16-byte index pairs, a four-byte buffered vector
header followed by 24-byte entries, and uninterpreted raw values. Eight byte
registers compare indices; buffered shard IDs stay as eight separate bytes.
The fourth count byte is zero; the completeness premise is derivable from an
authenticated value-byte bound below 2^24 (`main_group_count_bound`), but that
budget still needs its actual view-to-domain connection.

Candidate bus63 is QVC `(vid,tau,mode,user-count)`, a chained parser provider.
Candidate QSH29 is `(tau,entry,byte-position,byte)`, with byte-position8 reserved
for the buffer count. This deliberately differs from the old unused vector
schema; final assembly must update both ends coherently. Neither registry nor
an active table was silently changed.

The main read order is delayed, buffered, yield, then every listed group in
serialized order. Implicit chunks read delayed only. Queue walk IDs retain
`W_QV + tau + 64*slot`; checked injectivity requires tau<64, and an explicit
buffer-byte bound below2^24 implies every main request ID is below2^26.

Remaining work: field-level parser extraction and honest local/traffic proofs;
queue read orchestration and KEYNIB/FINAL authentication; QVC/QSH balance and
uniqueness; actual value/row/walk capacity; integration into the complete AIR.
A combined parser/read table is preferred for size. Isolated source partition
shape estimates leave only75,006 bytes after a provisional48-column queue
shape; separate parser/read tables leave18,845 bytes. These estimates omit
remaining source wiring and are not admission/security proofs.

## Generated record placement

`RecordGlue` proves local transfer for terminal and interior rows and validity
of padding. `Records` packages the three executable generators with exact,
positive row counts and only their existing byte-size/count preconditions.
`RecordMarkers` derives every endpoint marker from generated rows;
`RecordPlaced` proves local validity when a record is placed at a fitting offset,
with arbitrary unrelated next-record payload and explicit physical boundary
flags. Seven permanent axiom guards pass in `test/QvRecordCandidate.lean`.
Full list concatenation, read orchestration and capacity are still pending.

`RecordConcat.recordsTrace_local` now proves all local constraints of the actual
flat-mapped list of generated records, including cross-record transitions,
empty lists, padding, and physical wraparound. Its only sizing premise is the
explicit sum of generated row counts fitting the trace. That sum is proved
exactly equal to the executable row-list length. The record audit now has ten
axiom guards and three fixtures in each arithmetic model, including a rejected
corrupted boundary marker. Global accepted-witness capacity is still open.

`RecordLocal.records_table_local` packages concatenated generator validity into
the shared field-level `TableLocal` interface, including multiplicity bits.
`RecordTraffic` proves the exact byte-message concatenation and exact row cost:
serialized value bytes plus one marker for each empty record. Six additional
axiom guards pass (record audit total16, with six behavior guards). These are
compositional results; global native ownership/budgets and the complete
field-valued bus contract remain to be assembled.

## Canonical field traffic checkpoint

`RecordTrafficContract.records_canonical_traffic` now proves the shared
field-valued `TableTraffic` contract for the actual concatenated trace. It
provides exactly the numbered value bytes, one QVC provider start/end pair per
record, and the buffered shard bytes and count. All other buses are silent.
The proof handles arbitrary public inputs, padding, and field multiplicity bits;
its premises are record validity and the explicit total row-fit bound.
`NaturalEval`, `NaturalTraffic`, and `NaturalBits` justify the natural-message
bridge rather than assuming field and natural traffic coincide.

The record audit passes 35 exact axiom guards and six behavior guards. The
separate parser audit remains 28 axiom guards and 22 behavior guards. This closes
the generated parser traffic obligation, not authentication or extraction from
arbitrary accepting traces. Native value ownership, total capacity, read
orchestration, and global bus balance remain open. In particular, a raw empty
marker does not establish that the authenticated value is empty; raw extraction
must use the value table.

The latest integrated source cost model uses the implemented combined
queue shape of 52/8/6/8 at log22. With the current source wiring and 200-column
Ups table it totals 8,359,074 bytes, leaving 29,534 bytes under 8 MiB. These
figures supersede the earlier provisional estimates above and are not protocol
admission or security proofs.

## Executable combined read/parser candidate

`CombinedTable` now implements the previously reserved52-column table with14
interactions. Its actual kernel-checked group2 shape is52/8/6/8/log22, exactly
matching the reserve. Static well-formedness passes at local degree6. Walk rows
precede parser rows, enforce the main delayed/buffered/yield/group read sequence,
then implicit delayed reads, and bind termination to the full public u32 K at26.
Group data and implicit delayed reads use raw mode, matching `ReadPlan`; only
main delayed/yield index values use empty mode. Byte bits bind KEYNIB messages.

Walk rows reuse raw-empty parser markers. Their otherwise unused length cell
holds the requested parse mode; `parserExpr` virtualizes that cell to zero for
base parser equations. `CombinedOverlay` proves this evaluation mapping and
unchanged evaluation on parser rows whose current/next walk flags are zero.
This keeps QVC message degree low enough to preserve the reserved quotient cost.

Five exact axiom guards and12 Fp local fixtures pass, including zero/one/two
implicit transitions, full-height termination, present delayed value parsing,
buffered group reads, and mutated key/order/mode/bit/termination rejection.
These are local regressions, not a proof of global traffic balance.

Remaining: generic honest walk rendering and traffic, transfer of full parser
local/traffic theorems, native ownership and height bounds, and extraction.
Extraction must derive exact walk lengths and implicit count using height<P,
exclude detached QVC counter cycles, and connect FINAL to value-ID semantics.
The static shape is now concrete; protocol admission and the 8 MiB end-to-end
certificate are still open.

`CombinedParser` now extracts original parser constraints on rows whose current
and next walk flags are zero. More importantly, it derives all added read gates
as zero from the combined local constraints whenever walk=0, then proves exact
field-valued row traffic equality with the standalone parser. Combined audit
now passes10 exact axiom guards and12 field fixtures. Physical wraparound,
whole-prefix composition and honest walk construction still need their own
proofs; this row-level transfer does not assume they have been established.

The public implicit-count binding is now checked end to end: the native prep
tag plus Borsh prefix has length26, header bytes26–29 are exactly u32 K, and
`CombinedPublic.kPublic_prepared` proves the actual AIR expression evaluates
to that prepared K in the field. The standard explicit u32 range premise is
preserved. Combined audit now has15 axiom guards and12 field regressions.


## Native walk generation and conditional capacity

`CombinedWalkGen` constructs actual 52-cell rows for the native main and implicit
read plans. Its request projection preserves order and duplicates exactly;
`applyNewChunk_plan_reads` derives main read validity from successful native
execution. The exact walk row count is `3 + 9 * groups.length + implicit.length`.
`CombinedWalkCells` and `CombinedWalkBits` prove byte reconstruction in both
natural and field evaluation, and that emitted high/low symbols equal the
native trie key's nibble sequence.

`CombinedCapacity` proves the walks plus parser records fit log22 under the
existing 3,000,000-byte buffered-value bound, at most31 implicit transitions,
2MiB record bytes and134,028 records. Actual allocator ownership must still
supply those record premises; this is conditional capacity arithmetic, not a
completed honest-trace certificate or a new native acceptance restriction.

The combined audit now passes33 exact axiom guards and15 field regressions,
including three cases built by the production walk generator. Generic whole
walk local constraints, exact bus traffic, parser wraparound, arbitrary-trace
extraction and global ownership remain open.


`CombinedWalkTraffic` proves generated walk rows emit no parser-provider traffic,
including VBYTES and parser QSH. It also proves exact field KEYNIB traffic per
row: the walk ID, byte-symbol positions, high/low nibbles, start/end markers and
multiplicity all match the explicit natural message list. The positive-expression
bridge is applied only to the KEYNIB interaction subset; the combined table's
subtractions are not incorrectly interpreted as natural expressions.
The audit now passes39 exact axiom guards and15 regressions. QVC/QSH walk
traffic, complete word/plan message composition and generic local constraints
remain open; this result does not assume those properties or global balance.


`CombinedTerminalTraffic` adds exact FINAL receives and both directions of the
QVC counter step. Missing reads use value ID0 and send no QVC requests; present
reads use the supplied value ID and advance the counter once on the final row.
`CombinedShardTraffic` proves exact QSH shard-byte/count receives. Its natural
subtractions are justified by bounds, with the group slot bound derived from
membership in the generated native plan (`plan_group_slot`). No global bus
balance or local-acceptance premise is used in these row traffic theorems.

All four walk message families now have exact row-level field traffic results;
this does not yet establish their whole-word/plan composition, full constraints,
provider ownership or global balance. The combined audit passes49 exact axiom
guards and15 regressions; the shard target's211 dependency jobs pass.


`CombinedWordTraffic` composes each complete native key word. Its actual field
traffic is exactly one FINAL receive, one QVC step iff present, a START marker
followed by the numbered native nibbles and END marker, and the expected eight
shard bytes or buffered count. Arbitrary trace offsets and public inputs are
supported; the hypotheses specify generated cells and the established group
slot bound. This is whole-word traffic, not global provider balance or complete
local constraints. The combined audit now passes57 exact axiom guards and15
regressions. Whole-plan composition, local constraints and ownership remain.


`CombinedBoundary` closes parser-expression preservation at physical wraparound:
the actual first delayed walk has mode0, so the length overlay is unchanged even
though its walk flag is1. This is expression preservation, not an assumption that
the original parser constraints already hold at that boundary.
`CombinedWalkBase` proves every generated walk marker satisfies every transformed
base-parser constraint over any commutative ring. Its sole neighbor condition is
inactive-next or next-record-start; generated next walks and padding discharge it.
The independent extra read-sequence constraints and multiplicity-bit obligations
still require proofs. The combined audit now passes64 exact axiom guards and15
regressions; the base target's154 dependency jobs pass.


`CombinedBoolean` proves all generated control flags and byte registers are bits,
then derives their actual AIR equations over any commutative ring. It also proves
every interaction multiplicity equation in `CombinedTable.table.bitConstraints`
and every inactive-row gate. These use generated cells, with no local-acceptance
premise. Thus the protocol-added multiplicity bits are covered explicitly.
The combined audit passes71 exact axiom guards and15 regressions; the boolean
target's155 jobs pass. Remaining local work is the read algebra and sequencing,
plus complete parser/walk composition; ownership and extraction remain separate.


`CombinedInside` proves exact preservation of all ten carried metadata cells
and the three inside-word clock equations from adjacent generated rows.
`CombinedReadAlgebra` proves the actual byte reconstruction and mode equations,
including implicit raw mode, over arbitrary commutative rings. These results
require generated current/next cells, not local acceptance. The combined audit
passes76 exact axiom guards and15 regressions;213 dependency jobs pass.
Remaining equations concern terminal/read gates, endpoints and between-word
sequencing, followed by full constraint and trace composition.


`CombinedReadGates` proves nine actual candidate equations for raw-marker flags,
end-implies-last, absent-value ID0, present/group/count request gates and first
position0. Membership in the actual table constraints is checked explicitly.
`CombinedKeyEndpoints` proves final position0/8 and the native key's first byte
7/13/10/16 from generated key data. All are generic field equations without
local-acceptance assumptions. Audit80 exact axiom guards+15 regressions and215
dependency jobs pass. Last-main/count rules, implicit metadata, public termination,
physical endpoints and between-word sequencing remain before full composition.


`CombinedPlanMetadata` derives last-main source/type/count facts, implicit
kind/slot metadata, final instance index and absent-buffer count0 from membership
in the generated native plan. Only the absent-buffer result needs the existing
native `MainValues.Valid` predicate. `CombinedTermination` uses the final-index
fact to prove the actual public termination equation, with the public K binding
supplied through the existing prepared-public interface. Audit86 exact axiom
guards+15 regressions and217 dependency jobs pass. The remaining metadata field
equations, physical boundary conditions and between-word sequencing still need
composition into full local acceptance; this is not an end-to-end certificate.


`CombinedMetadataEquations` derives six main/implicit metadata equations from
actual plan membership, plus the last-main count, end-main and absent-buffer
count equations. The last-main subtraction is justified by slot≥2 before its
natural-to-field conversion. No accepted-trace premise is introduced. Audit91
exact axiom guards+15 regressions and218 dependency jobs pass. Physical endpoint
conditions and between-word transitions remain before full local composition.


`CombinedPhysical` proves actual first-main row constraints, their inactivity
after row0, no-restart on walk rows, and the two next-word start equations.
It proves final-row and exit equations under explicit layout premises (physical
last implies completed final word; a completed final word exits to non-walk or
physical wrap). These layout premises must still be discharged by full trace
construction. Audit97 exact axiom guards+15 regressions and219 dependency jobs
pass. Between-word metadata sequencing and full layout/local composition remain.


`CombinedMainOrder` proves exact indexed main-plan metadata and flags, and the
successor low/high-bit recurrence, slot increment, stable count and nonfinal
status directly from adjacent native plan entries. Duplicate shard IDs remain
preserved. This is the natural sequencing theorem; its field translation and
main-to-implicit/implicit successor composition remain. Audit101 exact axiom
guards+15 regressions passes; the focused main-order target has77 dependencies.

Capacity clarification: frozen `NearSpecV3.ChunkValidationV0a.B0` is2,000,000
bytes, not2MiB. Active `ValWf.rows` allows2^22 rows; the combined queue parser's
2^21-byte premise is a separate conditional bound. No constants were changed.
The oversized duplicate-buffer example does not establish an accepted-input
counterexample because its revealed pre-value exceeds frozen A7/B0. Actual
retained/QV capacity must still be derived from the accepted-input bounds.


`CombinedImplicitOrder` gives exact indexed implicit metadata/flags, successor
indices, and the main-to-implicit boundary from the native lists. The matching
`CombinedImplicitSteps` field equations establish entering tau1 and subsequent
tau+1 steps from generated neighboring cells. Those natural premises are derived
by the indexed plan lemmas; whole-list layout still needs composition. Audit108
exact axiom guards+15 regressions and222 dependency jobs pass. Main-step field
translation and complete local trace construction remain.


`CombinedMainSteps` proves all five main successor AIR equations from adjacent
indexed native plan entries, preserving duplicates. It also proves every
between-word gate vanishes on nonterminal byte rows or final words. Membership
of the five equations in the actual table is checked. Audit113 exact axiom
guards+15 regressions and223 dependency jobs pass. Full case/layout composition,
parser suffix composition and ownership remain; individual equations are not
yet a whole-trace acceptance theorem.


`CombinedStepCases` composes all nine between-word equations for main successors,
main-to-implicit transitions and implicit successors, and proves they all vanish
inside a word or on a final word. All nine are proved members of the actual AIR
constraint list. The generated-cell and natural metadata premises remain explicit;
whole physical layout and parser suffix composition are still required. The
224-job target and121 exact axiom guards+15 regressions pass. This is a component
composition checkpoint, not whole-trace acceptance or an end-to-end certificate.


`CombinedNeighborEquations` composes the13 inside-word equations, two next-word
start equations and nine transition equations. Internal byte neighbors and final
word endpoints satisfy all24; terminal-to-next-word rows satisfy the first15,
ready to combine with the step cases. Membership of all24 in the actual AIR is
checked. The generated-cell/position premises still require physical layout;
this does not assert arbitrary neighbors or whole-trace local acceptance. Target
225 jobs and129 exact axiom guards+15 regressions pass.


`CombinedPlanOrder` classifies every adjacent entry of the full native plan into
one of the three step cases, and proves final=true exactly at its last entry.
It derives all24 neighbor equations at actual indexed native word boundaries,
with only generated-cell/terminal-position premises remaining. Duplicate shard
requests are preserved. The226-job target and138 exact axiom guards+15
regressions pass. Flattened physical row addressing and full local acceptance
remain to be composed; this does not close the end-to-end certificate.


`CombinedRowLayout` derives coordinates for every row of the flattened walk
list and proves exact generated-row lookup at those offsets. Consecutive word
offsets and terminal-to-next-word lookup are checked, without trace-acceptance
premises. This discharges the list-addressing layer; casting into the physical
trace, cyclic boundary behavior, parser suffix and full constraint composition
remain. The227-job target and147 exact axiom guards+15 regressions pass.


`CombinedTraceNeighbors` proves all24 neighbor equations at every physical row
of the generated native walk prefix, from generated prefix cells and prefix
length≤trace height. Cyclic indexing is handled explicitly. Exact prefix endpoint
coordinates imply the physical-last equation; exit holds when the first suffix
row has walk=0 (or at physical wrap). Prefix cells are obtained from an appended
row encoding by `PrefixCells.of_append`. No local acceptance or balance premise
is used. Target228 jobs and156 exact axiom guards+15 regressions pass. Full walk
constraint composition, parser suffix acceptance, provider/global traffic and
end-to-end extraction/certification remain.


`CombinedLocalCompose` and `CombinedPrefixLocal` now prove every constraint in
`CombinedTable.table.allConstraints` on every physical row of the generated
native walk prefix, including parser overlay and interaction-bit constraints.
The theorem derives row membership, neighboring cases, first/last boundaries
and physical cyclic indexing. Its ordinary inputs are MainValues.Valid, generated
prefix cells, prefix≤height, the public K binding, and first-suffix-row marker
cells (act=0 or vf=1, walk=0) when a suffix exists. No local-acceptance premise
remains in `plan_prefix_all_constraints`. The parser suffix itself, exact traffic
ownership and arbitrary accepted-trace extraction still require composition.
Target230 jobs and162 exact axiom guards+15 regressions pass. This is whole walk
prefix local acceptance, not whole combined table or end-to-end certification.


`CombinedParserLift` lifts original parser acceptance to combined constraints
when the extra columns are zero, including interaction bits and physical wrap.
`CombinedRecordPlacement.records_suffix_local` derives original parser validity
for executable valid records after a nonempty prefix, across records, padding
and cyclic wrap. Parser evaluation is independent of public input.
`combined_records_suffix_local` composes both and proves every combined equation
for each suffix row. Premises are generated record cells, zero extra columns,
row fit, and first-prefix parser marker/zero-mode cells; no local acceptance
premise remains. The260-job target and167 exact axiom guards+15 regressions pass.
The complete mixed trace constructor must still discharge these ordinary cell
premises and combine suffix with prefix, then exact traffic and extraction.
