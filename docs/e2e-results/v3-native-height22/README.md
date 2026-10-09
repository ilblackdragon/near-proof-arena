# Native log-22 renderer checkpoint

All modules below compile strictly with Lean 4.34.1, one thread, explicit
implicit-binding options disabled, and 16 GiB virtual-memory limit.
They are additive candidates; active/frozen tables and caps are unchanged.

## SHA: actual 512-column stream and exact traffic

Dependency order: `Candidates/ShaHeight/{Families,Current,Steps}` → `Trace`
→ `Traffic` → `Packed`.

The previous native `shaBinTrace` used minimal `honestLog`, so it did not already
provide the fusion clock. `fixedTrace` now uses the actual honest cell stream at
an explicit log. `step_at_height` checks every transition including the changed
cyclic last edge. All eight SHA constraint families and multiplicity bits hold
at any fitting log1..22. Extra pad rows have zero traffic; exact tableBusCount
matches the previous honest trace.

`packedTrace` applies the checked 512-column encoding at log22.
`packed_local` and `packed_traffic` require only existing `MsgsOk`, including its
unchanged row-cap premise. They preserve exactly the original byte and digest
inventory. This covers each of the four selected SHA slots once its assigned
message batch is proved MsgsOk; it does not establish the full four-bin allocation.

18 exact guards: `test/AuditShaHeight.lean`, SHA256
`78f6a7aaab488bf445a5a5578ca0002e37fab1dcdf623b47f9f5723e0ac5fa98`.
Logs `/tmp/shaheight-{families,current,steps,trace,traffic,packed}.log` and
`/tmp/shaheight-exact-audit.log`.

## Trie and SIZE count columns

Dependency order: `TrieHeight` and `CountLift` → `TrieCountHeight`;
`CountLiftTraffic` → `TrieCountTraffic`.

NodeGen3, ValGen and UniqGen already expose checked completeness at an explicit
physical height. `TrieHeight` builds those native streams at2^22, including their
native SUM placement and cyclic successor logic, with original local legality
and exact traffic. This does not copy a short physical trace.

`CountLift` constructs the added counter as the field prefix sum of the native
increment stream. It proves old expression preservation, first-row zero and
all transition increments. `TrieCountHeight` instantiates the actual candidate
node/value SIZE tables, deriving column bounds by kernel checks. No new counter
or local-constraint premise is required beyond existing NodeOk/ValOk.

`CountLiftTraffic` and `TrieCountTraffic` prove the exact amended message formula
(the SIZE tuple appends the constructed prefix counter) and preserve every
non-SIZE bus count. Simplifying the final counter to the intended native distinct
record count and connecting final semantic view allocation remain open.

21 exact guards: `test/AuditTrieHeight.lean`, SHA256
`6cae6417c09fafd5a01ee9aa4f0123e8dd62da06220fe41ef1da7e9797768f77`.
Logs `/tmp/{trieheight,countlift,triecounth,countlifttraffic,triecounttraffic}.log`
and `/tmp/trieheight-exact-audit.log`.

## Compact UPS from accepted input

`Candidates/CompactHeight` constructs the integer-cell trace directly atlog22.
It translates all compact constraints to physical evaluation and derives every
multiplicity bit from the compact row rules. `accepted_trace` composes the
existing accepted-input constructor, preserving the SAME scheduler upsert and
allocated-instance witnesses and the proved compact row cap. It returns actual
TableLocal and log=22, without a separate constraint/bit assumption.
Global provider/balance assembly is still distinct.

6 exact guards: `test/AuditCompactHeight.lean`, SHA256
`e49103f348e4a3402ba88f658ffd7898a10906771e90f2e782fd0ea6a7ff5382`.
Logs `/tmp/compactheight.log` and `/tmp/compactheight-exact-audit.log`.

All 45 guards allow only propext, Classical.choice, and Quot.sound.
Olean overlay: `/tmp/ups-proof` (existing read-only baseline dependencies).

## Remaining native clocks

These checkpoints supply renderer-level log22 coverage for SHA4, node/value/uniq3,
and UPS1: eight of the19 fused slots. The remaining selected slots are codec,
scan/distribution, process, memory, compare, receipt, source0..3, and queue.
Existing component input well-formedness, final view allocation, source/receipt/
scheduler semantics, all-family SHA capacity, and global traffic composition
must still be discharged together. No complete native witness is claimed here.

Scheduler comparator and memory checkpoint (2026-10-08): `SchedHeight`,
`CmpHeight`, `MemHeight`, `MemHeightTraffic`, `SchedLocalHeight` compile under
strict implicit settings, one Lean thread and 16 GiB. They generate native rows
at log22 directly. Comparator constraints and multiplicity bits hold, and fitting
comparison lists have exact expected traffic. Memory constraints explicitly use
one padding row after the native segments, check the physical last row and cyclic
successor, and preserve exact traffic on every bus and direction. Segment semantics
(`SegOk`) and the native row capacity remain explicit, pending whole accepted-run
assembly. `test/AuditSchedHeight.lean` passes eleven exact standard-axiom guards.
Logs: `/tmp/cmpheight.log`, `/tmp/memheight.log`, `/tmp/memheighttraffic.log`,
`/tmp/schedheight-exact-audit.log`. Compiled modules are in `/tmp/ups-proof`.

This advances selected native renderer coverage to ten of nineteen components.
Codec, scan/distribution, and processing still lack full generator-local
completeness; they are being proved separately. Root owns queue/source height
composition, and the receipt lane owns its native local renderer. No arbitrary
padding closure is assumed.

Further scheduler row prerequisites, strict checked:

- `SchedField`, `CodecZeroTest`: native modular subtraction/inverse and codec zero-test constraints.
- `CodecPadding`, `ScanPadding`: all padding constraints and zero multiplicity gates, including the actual physical last-row wrap with an arbitrary successor. `AuditSchedRows` has 14 exact guards.
- `ProcBits`, `ProcHeightBits`, `ProcKeyInverse`: every native process Boolean flag and interaction gate on active keys/headers/entries, first tail row, and later padding; native key-position inverse arithmetic. `AuditProcRows` has 19 exact guards.
- `ProcNativeRows`, `ProcKindHeight`: exact native row lookup and complete process `cKind`, including first/last and inactive-suffix rules. `AuditProcKind` has nine exact guards. Initial instance tau zero and row capacity are explicit; whole multi-instance concatenation remains to be assembled.

These are not yet full codec/scan/process local completeness. The remaining process key/header/entry constraints and codec/scan active rows remain required. `ProcKeyRows`, `ProcKeyTests`, `ProcKeyStep`, `ProcKeyRotate`, `ProcKeyScalar`, and `ProcKeyInterior` now prove the entire process `cKey` family on native key rows 0 through 14; `AuditProcKey` passes twenty exact guards. The last key row and header/entry families remain open. An initial defeq expansion hit the existing memory ceiling; factoring scalar evaluation and normalizing native record fields reduced subsequent checks to under one second without raising resource limits.


UPS provider packaging repair: `Render/Ups/NativeTerminalId`,
`ForestTerminalExact`, `ForestNativeWalkExact`, `SchedulerExactInstances`, and
`AcceptedExactTrafficList` preserve the actual terminal source node ID alongside
the BMAP provider. The accepted theorem retains the same allocated native
instances, SHA families, and byte budgets, while adding
`ExactNativeWalkProviders`; forgetting this extra fact recovers the old provider
predicate. This closes a lost equality in the old existential packaging, without
changing native execution or assuming a provider ID. Seven exact guards pass in
`AuditUpsTerminalId`; logs `/tmp/upsterminalid-exact-audit.log` and the individual
lowercase module logs in `/tmp`. Compiled modules remain in `/tmp/ups-proof`.


Process continuation checkpoint:

- `ProcKeyBoundary`, `ProcKeyLast`: native key row 15 and its real header/tail successor; seven exact guards in `AuditProcKeyLast`.
- `ProcOtherRows`, `ProcNonKeyEval`, `ProcNonKey`, `ProcKeyComplete`: complete `cKey` on every physical native row, including carried tail, padding, and wrap; eleven exact guards in `AuditProcKeyComplete`.
- `ProcEntryScalar`, `ProcEntryAdjacent`, `ProcHeader`, `ProcNonEntry`: all fifteen entry constraints on entry records from ordinary replay decisions, integer bounds, index/length, and adjacent x/ts cells; all entry constraints unconditionally on native key/header/tail/padding records; all header constraints on header-to-entry0 from the ordinary zero-key round ordinal rule. Eight exact guards in `AuditProcEntry`. These are row-level lemmas: generator-loop invariants, complete physical adjacency, remaining non-header `cHdr`, and multi-instance concatenation are still required. They do not assume polynomial evaluations vanish.

The additive UPS dispatch repair now retains `I.ci = u.run.terminal.ix` and
`DispatchNativeWalkProviders`, including the positive BV/BI-to-bitmap implication.
`ExactNativeWalkProviders` remains unchanged for existing consumers. The accepted
package carries both predicates; `dispatchProviders_forget` recovers the old
one. `AuditUpsTerminalId` now passes eight exact guards.


`ProcEntryPosition`, `ProcEntryNative`, and `ProcHeaderNative` now remove the
adjacent-cell premises from the native entry/header applications: exact positions
come from the generated key prefix and round-list blocks, and the successor uses
the actual modulo clock under the unchanged row cap. `AuditProcPosition` passes
seven exact guards. The ordinary per-entry replay decisions, index/length facts,
nonempty rounds, and zero-key ordinal sequencing still need extraction from
`Gen.run` success; no full process-local completeness claim is made yet.

`ProcHeaderContinue`, `ProcHeaderKeys`, and `ProcHeaderPadding` cover every header
constraint case, including native padding wrap (`AuditProcHeaderCases`: nine
exact guards). `ProcRoundBoundary`, `ProcEntryHeaderNative`,
`ProcKeyHeaderNative`, and `ProcPositionCases` derive actual physical round and
instance positions. `ProcData.RunData` states ordinary replay data laws only.
`ProcComplete.proc_local` now proves the complete single-instance native
`Proc.table` is `TableLocal` at log22 under RunData, tau0, and the unchanged row
cap (`AuditProcComplete`: eleven exact guards). This is a conditional native
renderer result, not yet a derivation of RunData from Gen.run success nor a
multi-instance concatenation theorem.

Process multi-instance boundary repair (isolated candidate):

- `ProcEmptyBoundaryRegression` proves the old rotation constraint evaluates to one when an empty-round key block is followed by a different seed. `ProcEmptyRunRegression` kernel-checks actual `Gen.run` success for two different seeds, both with zero shards and with one shard and the actual PV86 calculated parameters. This is not a full accepted `checkD0a` fixture. `AuditProcEmptyBoundary`: nine exact guards.
- `ProcBoundaryRepair` changes only the sixteen rotation gates from `kK` to `kK - kl * next(kK)`. Exact `shapeOf 2`, maximum all-constraint degree, and protocol wf checks show unchanged shape and degree; there are no new columns or interactions. `ProcBoundaryLocal` preserves old local completeness and recovers old key constraints away from instance boundaries. `AuditProcBoundaryRepair`: eleven exact guards. The active family is not changed.
- `ProcSound/{Entry,Row,Block,Round,Msg,Inst,Rows,Bridge}` is the additive sound-extraction port, in dependency order. The last-key rotation conclusion is conditional on the next row not beginning a new key block. Actual header seed binding is preserved; `physical_instance` yields the existing `Sched.Proc.Inst` from candidate `TableLocal`. `AuditProcSound`: 91 exact guards, standard axioms only. Whole scheduler Link/ownership proofs still hard-code the original table/local predicate and require adaptation.
- `ProcBoundaryKeys` checks every repaired key constraint at an arbitrary differing-seed empty-instance boundary, assuming consecutive native tau values. `ProcBoundaryRegressionRepair` applies this to the same concrete row regression. `ProcRowTransport` transports the non-selector groups between actual current/next row pairs for concatenation. `AuditProcBoundaryJoin`: five exact guards. Full multi-instance trace assembly and `Gen.run` to `RunData` remain open.

All checks above used strict auto-implicit settings, one Lean thread, the existing
16 GiB virtual-memory ceiling, and single-file bounded commands. Candidate
oleans are under `/tmp/ups-proof`; each module's log is `/tmp/` followed by its
lowercase basename (sound-port modules use `procsound-<name>.log`). Exact audit
logs use `procrepair-exact-audit`, `procempty-exact-audit`,
`procsound-exact-audit`, and `procboundaryjoin-exact-audit` respectively.

`ProcBoundaryEntries`, `ProcBoundaryGroups`, `ProcConcatGeometry`, `ProcLastRow`,
`ProcConcatRows`, `ProcConcatKind`, `ProcNativeGroups`, `ProcConcatActive`,
`ProcConcatPadding`, and `ProcConcatLocal` now complete the multi-instance native
process trace at log22. `proc_local` includes actual modulo-clock wrap and arbitrary
empty-round instances with distinct seeds, under ordinary RunData, consecutive
tau values, and the unchanged capacity. `AuditProcConcat`: 36 exact guards.

The next checked generator linkage is additive:

- `ProcGeneratedEmpty`, `ProcRunProjection`, `ProcEmptyReplay` (dependency order):
  actual Gen.run success gives exact instance fields, parameter bounds and eight
  seed words. Arbitrary empty raw requests imply empty rounds. Successful native
  empty-request lists therefore render legally from their ordinary clock and exact
  `16 * instanceCount + 1` capacity, without a RunData premise. Two actual one-shard
  PV86 runs with different seeds reach complete TableLocal. These remain generator
  examples, not full checkD0a fixtures. `AuditProcNativeReplay`: 13 exact guards.
- `ExceptLoop`, `ProcConverted`, `ProcReplayChain`, `ProcReplayMetadata`:
  successful native loop invariants derive the at-most-40-increases property of
  every actual converted request and exact cursor stamping of the replay rounds.
  `run_metadata` discharges both Initial and every adjacent Follows clause of
  RunData directly from Gen.run success. `AuditProcReplayInvariant`: 12 exact guards.
  Nonempty per-round entry/index/length bounds and zero-ordinal sequencing still
  require their inner-loop/model invariants; full native RunData is not yet claimed.

All these new checks used strict auto-implicit settings and the same bounded
single-file environment. Exact logs are `/tmp/procconcat-exact-audit.log`,
`/tmp/procnativereplay-exact-audit.log`, and
`/tmp/procreplayinvariant-exact-audit.log`; source modules use their lowercase
basename as the corresponding `/tmp/<basename>.log`.

The nonempty replay invariant is now fully derived. `ExceptRange`,
`ProcReplayShape`, `ProcReplayDecisions`, `ProcReplayAllowance`, and
`ProcReplayEntries` discharge every actual entry/count/index obligation from
Gen.run under PV86 (`AuditProcReplayEntries`: 15 guards). `ExceptSummary`,
`ProcModelRounds`, `ExceptVisited`, and `ProcRoundBounds` preserve the exact native
model round sequence and derive field-sized keys from checked decreases
(`AuditProcRoundBridge`: eight guards).

`ProcModelStep`, `ProcModelValid`, `ProcZeroPending`, `ProcZeroTransition`,
`ProcZeroTrace`, `ProcRoundOrder`, and `ProcNativeComplete` close zero-round
sequencing and full replay-data derivation (`AuditProcNativeComplete`: 27 exact
guards, standard axioms only). The native model is factored definitionally:
`process_eq` is proved by rfl. The pending-zero invariant tracks actual initial
pushes, removed buckets, and re-pushes. No stronger native input assumption or
validation check is introduced. `ProcRoundOrder.runData` now follows from actual
Gen.run success and actual PV86 parameter calculation. `ProcNativeComplete`
provides complete single- and multi-instance repaired process TableLocal at log22;
only the global tau allocation and row capacity remain explicit in the list
renderer. This does not yet prove accepted checkD0a inputs yield successful Gen.run
instances or complete codec/scan/memory/comparator local traces and global traffic.

The model-factor and zero-order checks use the same 16 GiB ceiling and one thread;
all final single-file checks finish below one second locally. Their exact audit is
`/tmp/procnativecomplete-exact-audit.log`. The earlier scratch proof that hit a
simplifier-step limit was replaced by the checked definitional factoring rather
than a larger validation budget.

## Actual native replay budget and ordinal allocation

`ProcConvertedFacts`, `ProcSenderPotential`, `ExceptArrayCount`,
`ProcSpendBudget`, and `ProcNativeBudget` prove the actual successful `Gen.run`
entry count is at most `C + 43*n`. The proof charges each actual re-push to a
sender quotient potential and uses the generator's checked sorted push/bucket
identity. It does not assume the old aggregate A7 premise or abstract Replay.
Each rendered process instance has at most `16 + 2*(C + 43*n)` rows.
`AuditProcNativeBudget` checks 19 exact axiom guards.

`ProcRequestCount` proves actual conversion never increases the input request
count and binds it to prepared A8 request uniqueness. `ProcNativeSequence`
executes native generators with increasing ordinals; its successful result
supplies exact length, native-run provenance, first tau and adjacency.
`AuditProcNativeSequence` checks 10 exact guards. `ProcPreparedSequence` builds
the inputs from `SchedPub` and actual previous scheduler states. Its
`prepared_local` derives the complete repaired process TableLocal at log22 for
at most 33 prepared instances, with no independent capacity, tau, or RunData
premise (`AuditProcPreparedSequence`: two exact guards).

All eight modules and 31 guards passed strict single-file checking with one
thread and a 16 GiB ceiling. Oleans are in `/tmp/ups-proof`; logs are
`/tmp/procspendbudget.log`, `/tmp/procnativebudget.log`,
`/tmp/procrequestcount.log`, `/tmp/procnativesequence.log`, and
`/tmp/procpreparedsequence.log`, with corresponding exact-audit logs.
Successful `runInputs` remains explicit: accepted native execution must still
be connected to successful generator replay and its normalized request input.
Other scheduler tables and global traffic remain separate obligations.

`ProcPrepBudget` obtains prepared count/public facts from actual `prepD0`
success and indexes previous scheduler states by instance position.
`ProcConversionSuccess` proves the first native loop succeeds for valid shard
indices and five-byte bitmaps (six exact guards together). `ProcConversionExact`
proves this loop's result equals `convRaw`; `ProcCoreReplay` discharges the
duplicate model-round comparisons (seven exact guards together).
`ProcModelEntrySuccess` proves the model entry's re-push check succeeds from a
positive increment and the pending-key/current-allowance invariant, including
zero allowance (two exact guards). Propagation of that invariant across the
whole native model, decoder bitmap-width linkage, shuffle replay, and successful
full `Gen.run` from accepted execution remain open. These are checked component
lemmas, not a completed accepted-witness scheduler constructor.

`ProcPendingCurrent`, `ProcPendingTransition`, and `ProcPreparedLinks` add the
actual prepared A8 unique-link and initial current-allowance invariants, with
checked per-entry preservation (11 exact guards). `ProcBitmapShape`,
`ProcPreparedBitmaps`, and `ProcPreparedConversion` now derive five-byte bitmaps
from actual wire decoding through `prepD0`. Every actual prepared input's
conversion loop, convRaw equality check, and request-count check succeed, with
at most 4096 output requests (11 exact guards). Thus bitmap width is no longer
an extra premise in the prepared conversion theorem. Whole model/replay and
shuffle success remain open beyond this conversion phase.

`ProcShuffleReplay` now proves that any successful native shuffle at
`rngAt key k` has a successful exact generator `replayShuffle`, with the same
permutation and final stream position (three exact guards). It relates the
native descending recursive shuffle to the generator's forward range loop.
This removes a separate replay-fuel assumption; propagating the actual stream
position through all model rounds and constructing the full generator result
remain to be composed.

`ProcModelRng` propagates the actual RNG stream position through every
successful model round and proves entry processing leaves RNG untouched.
`ProcReplayRounds.model_replay` executes all generator shuffle replays and their
output-equality checks successfully, starting at position zero and ending at
the exact native model RNG (seven exact guards). Full `Gen.run` still needs
non-shuffle replay checks, memory record construction, and the event model's
existence/refinement from accepted native scheduler execution.

`ProcModelEntryShape`, `ProcModelRoundShape`, and `ProcModelClock` derive exact
native model bucket/step counts and the flattened model timestamp
`requestCount + globalIndex` (11 exact guards). `ProcReplayBoundaryGuards`
derives the prepared seed-length guard and final RNG position guard from actual
preparation/model execution (three exact guards). No requested native cap is
strengthened.

RNG capacity is a separate unresolved obligation. The prior
`Sched.Spec.Draws`/`Complete.Height` analysis gives a worst-case 9,887,936 RNG
words under its stated old aggregate hypotheses, already above 2^22. It is not
an accepted-witness bound proved by the present process-row construction, and
average rejection behavior cannot justify a sound capacity proof. Splitting
RNG/ChaCha tables or a genuinely tighter accepted bound must be checked against
the actual candidate family and proof-size budget after native replay closure.

`ProcGrantAgreement` proves exact native/generator grant-state agreement,
including denied grants and unconditional self-writes (four exact guards).
`ProcConvertedLinks.selected_grant` derives its coordinate equality from the
actual conversion loop at the selected valid request ID, and proves exact
indexed model request correspondence (five exact guards). Lifting this through
all replay entries and authenticated push/memory logs is still required.

`ProcEntryEvent` identifies every checked model entry field with the generator
formula at valid converted indices (four guards). `ProcPushPerm`,
`ProcPushEntries`, and `ProcPushConservation` prove exact initial/generated versus
popped push multiset conservation, including the generator timestamp translation
(11 guards). The existing `Array.qsort` equality guard is not inferred from this
multiset fact: its implementation correctness/canonical ordering remains open.

`ProcRequestPointers`, `ProcEntryPointers`, `ProcModelPointers`, and
`ProcConvertedPointers` derive valid request IDs and increase indices for every
entry in every successful model round (11 guards). The invariant starts from
actual initial requests, survives native shuffle and exact re-push semantics,
and uses the existing unconditional at-most-40-increases conversion theorem.
No per-entry bounds are supplied. Accepted native execution to event-model
existence/refinement, state/log replay composition, and full generator success
remain open; RNG capacity remains separately unresolved.

`ProcNativeGrant` and `ProcNativeState` connect model grant arithmetic to actual
native `tryGrant`, whose granted counter uses saturating u64 addition. The
existing shard-budget invariant starts from the actual link pass, survives all
model entries/rounds, and bounds granted totals by 4,500,000 under PV86. An
executable fold of native grants equals each complete successful model entry
loop (nine exact guards). Native bucket selection/refinement and existence of
the complete accepted event-model run remain separate obligations.

`ProcNativeBucket`, `ProcNativePush`, and `ProcNativeBucketReplay` complete the
local native bucket comparison (seven exact guards): actual `processBucket`
returns both the model's exact state and the exact bucket dictionary reconstructed
from its pending push log. Request tails are derived from valid encoded pointers;
re-push conditions and timestamps agree exactly. Selecting the next maximal
native bucket, all model guard-success invariants, and lifting accepted native
execution to model existence remain open.

`ProcPendingTime`, `ProcMaxBucket`, and `ProcModelTime` prove that pending and
popped push timestamps are strictly increasing and earlier than processing time,
starting from actual initial requests (11 guards). Native pop-last selects the
same maximal-key bucket and filtered remainder as the event model; timestamp
sorting is proved to be the identity on these lists. This closes local bucket
selection/order correspondence. Forward model existence still requires the
current-allowance/distinct-link and ordinal guard invariants across native runs.

`ProcLiveLinks`, `ProcBatchSuccess`, `ProcInitialLinks`, `ProcPoppedSuccess`,
and `ProcPreparedRequestGood` construct successful complete model entry loops
(12 guards). Current allowance bindings and live-link uniqueness survive every
entry, and a successful selected-bucket shuffle yields a successful batch.
Initial invariants and positive, less-than-64 increase lists come from actual
prepared requests, A8, and PV86; they are not added accepted-domain premises.
The outer model's ordinal/order guards and final native-loop existence
composition remain open.

`ProcRoundGuards`, `ProcTagTransition`, and `ProcRoundSuccess` construct a
successful whole model round from a successful native-index shuffle (nine exact
guards). Mixed-ordinal, positive/zero ordinal, round-order, and entry checks are
all derived; the actual prepared initial state satisfies the invariant, and each
constructed round preserves it. Whole native-loop shuffle/fuel composition is
still required for accepted model existence. This is not yet full Gen.run success.

`ProcNativeRound`, `ProcNativeRoundExistence`, `ProcNativeLoopExistence`, and
`ProcNativeInitial` close full native-process to event-model existence (12 guards).
Successful native `processRequests`, prepared request facts, and the ordinary
allowed-array shape construct a successful complete `ProcCoreReplay.process`
with identical final state/RNG and the same fuel. The proof pulls native shuffle
success back to encoded request IDs and composes exact bucket refinement.
Next integration must derive that native process premise and allowed shape from
actual accepted scheduler execution. Full generator replay, qsort/log checks,
and RNG capacity are not claimed closed.

**Previous-state coverage regression:** `ProcPreviousStateRegression` (12 exact
guards) checks an actual successful native `Scheduler.run` with PV86, shard IDs
[0,1], no requests/congestion, and four decoded previous-state records. The
first record uses foreign sender 99 and allowance 7. Native lookup ignores it;
the existing `a0Canon`/`a0Src` positional model treats its allowance as slot zero.
Exact serialized output prefixes differ: native first allowance 2,250,000 versus
model 2,250,007. This is not a complete accepted `checkD0a` witness. A prior-state
canonicality restriction cannot be added to cover it; actual ID lookup and
last-write-wins semantics must be retained when repairing the model/codec path.

**Isolated native prior-state repair:** `ProcActualInput`, `ProcActualCore`, and
`ProcActualPublic` (15 exact guards) derive successful model processing from
actual `schedPub` and `runCore`. Initial allowances use native first-ID lookup
and last-record overwrites; the theorem retains decoding of the same original
prior bytes. Public allowed-array shape and request values are derived from
actual `schedPub`, rather than supplied as extra assumptions. This does not yet
replace the active generator or authenticate these allowances in the AIR.

`ProcPriorLookup`, `ProcPriorDecode`, and `ProcPriorBytes` (18 exact guards) prove
first-ID selection, recognized destination bounds, exact last-write/default
semantics, complete decoded-field bounds, and equality of the original bytes to
the decoded state's encoding. Original record `k` occupies exactly bytes
`5+24*k .. 5+24*k+23`; total prior length is `37+24*recordCount`, independently of
the current layout. A kernel regression covers duplicate layout IDs, an ignored
unknown sender, and an overwritten earlier allowance. `ProcPriorWinner` (five
exact guards) identifies the last matching original record and proves there is
no later matching record; absence means no original match.

Remaining Codec repair is material: current header constraints require previous
record count to be `n²`, previous sender/receiver bytes are copied from canonical
post-state IDs, and internal `B_SA0` routing comes from layout-only `srcOf`.
A repaired raw-prior parser must preserve authenticated original bytes and
supply exact first-ID / last-record lookup traffic to a canonical post codec.
Combining the independent 2,000,000-byte prior-value bound and roughly
3,150,000 canonical output bytes in one byte-row table exceeds log22; separate
raw/post components or a proved tighter common bound are required. No candidate
AIR change, revised budget admission, full Gen.run success, or RNG capacity
closure is claimed by these semantic repair modules.

**Executable prior-lookup witnesses:** `ProcPriorSummary` (four guards) proves
low24/high-nonzero is sufficient for the exact native capped increase, including
the maximal u64. `ProcPriorEvents` constructs recognized original-ordinal writes
and canonical link queries and uses checked merge sort. `ProcPriorBudget`
proves row counts from actual decoded byte lengths (combined 15 guards): with
2M authenticated prior bytes, at most 33 instances and 64 IDs, write/query events
are at most 218,501 and ID events at most 168,778; all isolated streams fit log22.
The accepted aggregate prior-byte premise still needs its native read binding.

`ProcPriorIds` constructs the actual original sender/receiver queries plus public
layout IDs (ten guards), retaining first-ID results and unknown-ID absence.
`ProcPriorEventOrder` (four guards) proves sorting preserves the exact write/query
list for each link. `ProcPriorIdOrder` (five guards) proves sorting preserves the
exact per-ID public-then-query list, including original public index order.
These are executable semantic witnesses, not completed AIR tables: sorted-row
carry constraints, authenticated traffic linkage, column layouts and revised
whole-family proof-size admission remain open. ID keys are still semantic u64
naturals here; the AIR must use limbs rather than a single field element.

**Prior memory AIR and gate transport:** `ProcPriorValues` and
`ProcPriorIdValue` (three guards each) bind queries to the last original write
and first public ID respectively. `ProcPriorCarry`, `ProcPriorCarryValue`, and
`ProcPriorCarryRead` (12 guards) prove actual query reads for a linear-time
segmented carry. `ProcPriorRows` (five guards) implements the linear annotation
pass and derives every emitted query's read equation from that proof.

`ProcPriorMemoryTable` is an isolated actual 11-column, four-interaction AIR;
its standalone shape is `(11,3,7,3,22)` and its wf8 check passes (two guards).
`ProcPriorCanonical` (three guards) derives event ranges from decoded input
bytes and proves packed-address field injectivity under the native bounds.
Those range facts still need the complete parser/read ownership connection in
sound extraction. `ProcPriorMemoryGated` adds one Boolean gate column with an
explicit product equality; its shape is `(12,3,7,3,22)` (five guards). It does
not split one product into multiple multiplicity bits, which would change the
encoded multiplicity.

The four `ProcPriorMemory{Transport,Lift,LiftLocal,LiftTraffic}` modules
(12 guards) prove gated-to-baseline local extraction, an executable one-column
honest lift, baseline-to-gated local legality, and exact whole physical bus
counts for the lift. The complete native memory renderer is now checked below. Original-byte
parser authentication, first-ID table extraction/local correctness, revised
Codec, and full multi-instance assembly remain unfinished; no full
prior-repair admission is claimed here.


**Native prior-memory renderer:** `ProcPriorRowNext` and `ProcPriorEventNext`
(eight exact guards) derive adjacent carry values, unique event ordering,
query group termination, and strictly increasing same-key ordinals.
`ProcPriorCells`, `ProcPriorActive`, `ProcPriorBoundary`, `ProcPriorCellBits`,
and `ProcPriorIndexed` (14 guards) check every actual field constraint and
multiplicity bit for active, final-active, and padding rows. The four modules
`ProcPriorTrace`, `ProcPriorTraceConstraints`, `ProcPriorTraceLocal`, and
`ProcPriorDecodedLocal` (11 guards) construct the executable log22 trace,
including physical wrap, and prove baseline and gated `TableLocal`. The
`decoded_local` theorem derives capacity from successful decoding of the
original prior bytes, byte length at most 2,000,000, and at most 64 public IDs.
It does not assume AIR equations or a proposed query result. The byte bound
still needs the whole native provider connection for multi-instance assembly.

**First-ID table and carry:** `ProcPriorIdTable` (two guards) is a concrete
20-column candidate with seven interactions and measured shape `(20,4,7,4,22)`.
It compares u64 IDs as 24/24/16-bit limbs, carries the first public occurrence,
and preserves original unknown-ID requests. The four modules
`ProcPriorIdCarry`, `ProcPriorIdCarryValue`, `ProcPriorIdCarryRead`, and
`ProcPriorIdRows` (15 guards) prove executable annotation gives the exact
native first-public-index result, including duplicates and unknown IDs.
The table's renderer and sound extraction are not yet proved.

Root measured the actual memory-plus-ID fusion at 8,359,892 bytes, leaving
28,716 bytes before raw parser and revised Codec costs. The old Codec's eight
prior-byte bit columns are a concrete potential saving once original parsing
moves to an authenticated separate parser; no such saving is counted yet.

### Original prior-state parser: checked physical renderers

The candidate repair now has complete single-instance log22 `TableLocal`
constructors for all three stages: original-byte framing, first-public-ID
lookup, and last-record-wins memory. These are isolated candidates; the active
Codec definition is unchanged.

- `ProcPriorRawLocal.decoded_local` constructs the actual 23-column framing
  trace from successful `State.decode` and original bytes of length at most
  2,000,000. `absent_local` handles the virtual initial state. Header, record,
  sanity hash, padding, and physical wrap constraints are checked.
- `ProcPriorIdLocal.decoded_local` constructs the actual 20-column sorted-ID
  trace. It derives key and row bounds from successful decoding, public IDs
  below u64, at most 64 public IDs, and the same source-byte bound. Duplicate
  public IDs and arbitrary original record order remain permitted.
- Existing `ProcPriorDecodedLocal.decoded_local` constructs the degree-reduced
  memory trace from those original records.

Strict Lean checks use `autoImplicit=false`, `relaxedAutoImplicit=false`, one
thread, and a 16GiB address-space limit. Exact audits are
`AuditProcPriorRawCases` (9 guards), `AuditProcPriorRawLocal` (7 guards), and
`AuditProcPriorIdLocal` (28 guards), all passing with only standard axioms.
Local logs are `/tmp/procpriorrawcases-exact-audit.log`,
`/tmp/procpriorrawlocal-exact-audit.log`, and
`/tmp/procprioridlocal-exact-audit.log`; checked oleans are in `/tmp/ups-proof`.

Dependency order after the previously checked raw generator/header package:
`ProcPriorRawPadding`, `ProcPriorRawStart`, `ProcPriorRawHeaderInner`,
`ProcPriorRawHeaderEnd`, `ProcPriorRawRecordInner`, `ProcPriorRawRecordEnd`,
`ProcPriorRawHashInner`, `ProcPriorRawHashEnd`, `ProcPriorRawActive`,
`ProcPriorRawPhysical`, `ProcPriorRawLocal`.
The ID package order is `ProcPriorIdNext`, `ProcPriorIdCells`,
`ProcPriorIdCarryFields`, `ProcPriorIdGateFields`, `ProcPriorIdActive`,
`ProcPriorIdBoundary`, `ProcPriorIdPadding`, `ProcPriorIdBits`,
`ProcPriorIdTrace`, `ProcPriorIdTraceConstraints`, `ProcPriorIdLocal`.

The authenticated-length relay and three-stage vertical overlay are separate
checked candidates. Parent integration measures their actual reordered fused
profile; earlier independent-table totals are not final admission evidence.
Record-byte limb assembly, lookup request/result joins, whole multi-instance
stage assembly/extraction, authenticated length-consumer ownership, and the
Codec replacement remain open. A fourth shared stage is being evaluated;
its width and traffic costs have not yet been included in an admitted family.

### Four-stage prior parser: certified three-way grouping budget

`ProcPriorTripleAdmission` is a structural candidate certificate for the actual
four-stage prior parser family: raw framing, first-ID lookup, sorted last-write
memory and original-record join, plus the Codec parameter relay and empty-value
repair. It retains four SHA tables and all native domain and row-height caps.
`InteractionTriples` only inserts zero-multiplicity interactions and reorders
existing interactions. Its checked `local_iff` and `table_traffic` preserve local
legality and every natural bus count on the same physical trace.

The frozen grouped protocol permits `pg 3` (`NpOkG` accepts group sizes 1–3).
The actual candidate's checked maximal header has fused shape
`3402/89/7/89/log22`, grouped degree 8, multiplicity bound 1,034,526,724 and
fingerprint bound 67,967,730,360, both below the existing 2^36 bus budget.
`ProcPriorTripleSize.model_exact` proves the full `sizeMaxDedup` equals
**8,231,316 bytes**, leaving **157,292 bytes** below 8 MiB. The earlier two-way
four-stage measurement was 8,414,100 bytes and exceeded the cap by 25,492.

`AuditProcPriorTriple.lean` checks 42 exact axiom reports, in addition to the
13 generic interaction-transport guards. All use only standard Lean axioms.
This is not an end-to-end admission or honest-witness theorem: installation of
all four native stages, their canonical parser/lookup links, corrected Codec
input semantics, new-bus ownership and whole-family honest balance remain to
be composed. Existing active tables and the frozen native relation are unchanged.

The original-record join now has actual log22 `TableLocal` theorems in
`ProcPriorRecordLocal`: decoded input supplies the u64 and row bounds; the empty
record list is covered. `AuditProcPriorRecordLocal` has 31 exact guards. This is
one instance with tau zero, including all active, padding and wrap rows.

`ProcPriorVertical4NativeClock` constructs four physical stage windows from the
same explicit native row inventories and proves all 21 window constraints at
every row. `ProcPriorVertical4DataEval` proves component expressions read the
unchanged 23-column data prefix with the installed window flags. Audits:
`AuditProcPriorVertical4` (10), `AuditProcPriorVertical4Clock` (13), and
`AuditProcPriorVertical4Data` (3). Full multi-instance component installation and
authenticated cross-stage messages remain outstanding.

The pg3 certificate's fingerprint margin is **751,746,376** below 2^36. Its
maximum message length is 57; an additional padded triple at log22 would cost
729,808,896 fingerprint units. Future Codec joins must therefore be checked
against the fingerprint budget as well as the proof-byte budget. Obsolete
lockstep VBYTES/SA0 interactions are candidates for replacement, not assumed
free capacity. The current Codec still needs its actual prior-input repair.

### Native prior-state Codec repair: executable rows and factored additions

The isolated `ProcPriorCodecActual` table now gates the receiver-zero flag's
outside-record constraint by `kR`. The same column is a digest/header register
outside records, so an unconditional off-gate zero would reject valid rows.
This correction changes neither columns nor interactions; its concrete family
certificate must be rebuilt against the corrected source.

New checked dependency order (all under `Candidates`):

- `ProcPriorCodecGen`, then `ProcPriorCodecRegression`;
- `ProcPriorCodecQueries`, then `ProcPriorCodecGrid`;
- `ProcPriorCodecGridField`, then `ProcPriorCodecGridCells`;
- `ProcPriorCodecNonrecord` (independent of the grid proofs);
- `SchedSetAll` (generic imperative-row lookup bridge).

`AuditProcPriorCodecGen` checks 15 exact axiom guards;
`AuditProcPriorCodecGridField` checks 7; `AuditProcPriorCodecGridCells` checks 10;
`AuditProcPriorCodecNonrecord` checks 1; `AuditSchedSetAll` checks 7.
All compile with strict implicit settings, one Lean worker, and a 16 GiB virtual
memory bound, using the existing `/tmp/ups-proof` overlay.

The generator preserves original prior-state serialization and uses native
first-ID/last-record lookup for allowance reads. Kernel regressions establish
that the old generator rejects the noncanonical-prior fixture while the new
one succeeds and preserves native bytes. An executable diagnostic evaluates
all 165 fixture rows against every corrected constraint and finds no failures.
A direct kernel reduction of that whole diagnostic exceeded the memory bound;
there is deliberately no theorem asserting it.

The factored proofs establish all nineteen added constraints on the computed
record projection, and on nonrecord rows with the ordinary phase flags and
next-counter initialization. They do not yet establish the original Codec
constraint groups, full imperative-array indexing, authenticated whole-parser
joins, or the complete multi-instance `TableLocal`. The successful-generator
byte contract concerns returned metadata; its equality to physical row bytes
remains an installation obligation. Native query inventories already match
the last-record memory inventory, including the absent empty dictionary.

The follow-up helper extraction is definitionally checked by
`ProcPriorCodecGen.core_refactor` against `ProcPriorCodecCoreLegacy.core`.
`ProcPriorCodecAssignments` contains the four pure row builders, and the
executable core still returns exactly the same rows, errors, comparisons and
SHA input. `AuditProcPriorCodecRefactor` has one exact guard. The native fixture
was rebuilt after this refactor.

`SchedSetAllRange` adds three guards for contiguous register lookup. The
`ProcPriorCodecNonrecordPhase` variant removes the next-counter-zero premise
when `ehp=0`; this is essential for hash rows, whose sender-counter column is
part of the digest overlay. `ProcPriorCodecAssignmentReads.record_id` proves
actual sender-register array reads with an explicit no-later-overwrite premise.
These two modules have three guards in `AuditProcPriorCodecAssignments`.

The chain `ProcPriorCodecRegisterMiss → ProcPriorCodecHeaderReads →
ProcPriorCodecHashReads → ProcPriorCodecNativeHash` has sixteen exact guards in
`AuditProcPriorCodecNativeHash`. It proves header/hash array byte reads,
register non-clobbering, and all nineteen added constraints on actual native
hash-row helpers without phase or next-row assumptions.
`ProcPriorCodecNativeSides` adds three guards for actual ash-row additions and
header additions. The latter retains only the concrete boundary condition
`p=4 → next sender=0 ∧ next receiver=0`.

Remaining: derive that header boundary from the first actual record; bind the
record projection to the imperative record helper and its accumulated extra
assignments; prove original Codec constraint groups, generated-array traversal,
concatenation and authenticated parser/global joins. These checkpoints are
components of native completeness, not an end-to-end certificate.

### Executable Codec record linkage (2026-10-08)

`ProcPriorCodecRecordStep` factors the actual inner iteration without changing
`ProcPriorCodecGen.core_refactor` (still `rfl` against the preserved executable).
`ProcPriorCodecStepRows.successful` proves every successful iteration yields,
appends exactly its native record row, and derives the suffix assignment support.
`ProcPriorCodecExtraColumns.extra_avoids_dgg` excludes DIGEST activation from that
actual suffix. `AuditProcPriorCodecRecordStep` passes 16 exact axiom guards.

`ProcPriorCodecRecordBase` derives the actual sender/receiver/wrap/start/allowance/
grant fields and eight sender-ID register bytes from this support.
`ProcPriorCodecRecordReads` derives actual record phase, byte, and instance reads
for 19 columns. Their two audits pass three exact guards each, with strict implicit
settings, one Lean worker, and the 16 GiB virtual-memory limit. Logs are
`/tmp/codecrecordbase-audit.log` and `/tmp/codecrecordreads-audit.log`; checked
artifacts are in `/tmp/ups-proof`. No table or family definition changed.

This is executable array linkage, not yet a complete generated Codec `TableLocal`.
The original Codec constraint groups, cross-row composition, and authenticated
whole-family joins remain to be assembled. Enclosing loop/DIGEST placement is
being composed independently from the successful-step interface.

### Prepared native timestamp envelope (2026-10-09)

The new `ProcReplayTimestampPotential`, `ProcReplayTimestampRounds`,
`ProcReplayTimestampBounds`, and `ProcReplayTimestampActual` modules prove a
noncircular timestamp bound. A pending pointer pays `64 - (v % 64)` units; every
entry consumes at least one unit, including failed grants, while re-pushes retain
only the remaining units. Therefore the model processes at most 64 times the
converted request count, independently of fuel and round count. This avoids the
insufficient coarse product of fuel and maximum bucket size.

For prepared inputs with at most 4096 requests, actual successful replay ends at
most at 1,310,720. `prepared_replay_bound` also derives `2 * finalTime + 1 < 2^29`
and every emitted round's `T < 2^29`, using the actual conversion, same model run,
and actual replay. It does not assume full `ActualRun` success or comparator
checks. Root's `ProcActualReplayTimeEnvelope` supplies the emitted-round transport.

All four new modules strictly compile; `AuditProcReplayTimestamp` passes 18 exact
axiom guards. Logs `/tmp/replaytimestamp{potential,rounds,bounds,actual}.log` and
`/tmp/replaytimestamp-audit.log`; oleans `/tmp/ups-proof`. This closes the timestamp
component of operand bounds; memory values and full generator completion remain
separate obligations.
