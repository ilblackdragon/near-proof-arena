# Exact native witness overhead and candidate accounting gap

The checked `Rcpt/Candidates/NativeWitnessCharge.lean` proves, for ordinary
32-byte epoch/hash/transition-root fields and the already-derived source
dictionary size identity:

```
encodeSW(w).length = payloadBytes + sourceSize + 4 * recordCount
                  + 224 + innerBytes.length + 44 * sourceCount + 69 * implicitCount
```

Here `payloadBytes` sums the bytes in actual stored records in every native
transition, and `recordCount` sums their actual vector lengths. The dictionary
vector includes fresh unused fillers needed by the unchanged native distinct-key
count. Their entire encoded size is included in the existing exact source charge.
The four bytes per stored record are native Borsh `Vec<u8>` length prefixes.
Empty byte records still cost four bytes. Each transition additionally costs 69
bytes (32-byte block hash, variant byte, store vector length, 32-byte post root).

Current Node SIZE increments by `act * (1-dup)`; current Val SIZE increments by
`act * (1-vz) * (1-dup)`. These authenticate payload bytes, not these record
prefixes. Public `preparedBytes p overhead` serializes an arbitrary overhead u32;
existing public-binding theorems alone do not prove its intended witness meaning.
Consequently this report does not claim the existing complete witness-size bound
or a complete AIR soundness attack. It identifies an exact unpaid accounting
obligation in the assembly proof.

A valid candidate repair must retain the unchanged native payload cap:
`SizeWf.base_le` currently checks `x0+x1 <= 3,000,000`. Adding four per record to
Node/Val's existing SIZE values would change that gate to an encoded-size cap and
could narrow the native domain. Instead the candidate must separately authenticate
record counts or encoded totals while preserving the old payload-base check.
A concrete option is to add count components to the SIZE messages/size-table
state, then check total payload + source charge + four times authenticated unique
record count + deterministic claim overhead. Empty values must contribute one
count even though they contribute zero payload bytes. Accounting must match the
actual per-transition deduplicated `ExtV3.store`; cross-table duplicate ownership
and transition-instance allocation remain part of that binding.

The checked `authenticated_witness_paid` theorem shows that a public overhead
literally equal to the actual required value yields the desired 8 MiB encoded
witness bound, under the existing explicit payload/source/no-wrap bindings. This
is a conditional integration theorem, not an assertion that the current AIR
authenticates that private count. A separate count/overhead binding is still
required. Four exact axiom guards pass under strict bounded Lean; no frozen
constraints, public pins, or native acceptance rules were changed.

## Implemented isolated count candidate

`SizeCountTables.lean` extends SIZE messages to `(tag,payload,count)` while leaving
other interactions and multiplicities identical. Node and Val each receive one
new running-count column, incremented by first-record-row times `(1-dup)`.
Val uses `vf`, not the nonempty-byte gate, so empty unique values count. Source
SIZE gains a literal zero count. Size receives two new columns (current count and
running count total), keeps the exact old three-million-byte payload constraint,
and changes only the total bound to include four times the count total.

The actual candidate shapes are kernel checked at grouping two:

- Node: `(187,11,6,11,22)`.
- Val: `(16,4,5,4,22)`.
- Size: `(33,1,3,1,2)`.

The tuple notation is `(width,aux,quot,fin,maxLog)`. All three candidate tables pass
the executable local wellformedness check with maximum local degree four. Source
partition shapes are unchanged. `SizeCountBudget` proves the existing wired-source
plus actual combined-QV model becomes 8,361,570 bytes: +2,496, leaving 27,038.
This baseline does NOT incorporate separately pending UPS-height/walk capacity
changes or constitute full protocol admission. SIZE fingerprint arity is now three
and must be reflected in the eventual integrated public/protocol descriptors.

`SizeCountTraffic.rowTraffic_withCount` proves exact row traffic transformation,
including multiplicity and all unaffected buses. `SizeCountSound.final_total_bound`
extracts the charged natural bound from the actual candidate final constraint,
with explicit slack/range/no-wrap hypotheses. `counted_witness_paid` combines it
with the exact native encoding formula. Thirteen exact axiom guards pass in
`test/AuditRcptSizeCountCandidate.lean` (receipt scratch total 130).

Still open: full extracted count-prefix facts and bounds, binding duplicate-owned
node/value counts to the per-transition deduplicated witness stores, honest count
renderers, full SIZE bus assembly and arity-aware protocol admission. The candidate
does not claim those bindings merely by defining counters. Active/frozen tables
and native acceptance remain untouched.

## Arbitrary-trace prefix extraction and native count reduction

`SizeCountPrefix.lean` now derives every Node/Val counter's natural value from
arbitrary candidate-local constraints: it is exactly the number of preceding
physical first-record rows whose duplicate flag is false. The proof extracts the
actual boolean fields, telescopes the count constraints, and derives count≤row
and the no-wrap bound from the unchanged height cap. It does not assume honest
rendering. It also recovers the original Node/Val `TableLocal` facts because the
candidate preserves constraints and multiplicity expressions.

`RetainedStoreCount.lean` proves the actual native witness record count equals the
sum of `ExtV3.store` lengths over precisely instances 0 through K. Covering each
raw-store byte by an instance-tagged counted representative yields count domination
after per-instance byte deduplication. Equal bytes in different instances remain
separate records, and empty bytes are counted. The remaining global premise is
that tagged coverage (and its representative cardinality) follows from the real
Uniq/DUP/ENT and physical counter views; it has not been silently assumed solved.
Eleven exact guards pass in `test/AuditRcptSizeCountPrefix.lean`, bringing receipt
scratch total to 141. No active table or descriptor was changed.

## Representative coverage and cardinality derived from buses

`UniqRepresentatives.lean` follows the actual adjacent duplicate edges to an
`eq=0` uniqueness row with the SAME instance tag and exact bytes. The duplicate
byte equality comes from actual DUP/ENT balance, including the empty-value marker.
Combined with existing SHA/parent store coverage, this derives tagged coverage
rather than assuming it.

`UniqCount.lean` derives exact `uniq.length = nodes.length + values.length` from
DIGS/PARENT/VPARENT multiplicities. DUP multiplicities then give the exact number
of skipped node/value records; subtracting these from total counts yields
`nonduplicate uniq count = nonduplicate node count + nonduplicate value count`.
No hash collision assumption is introduced, and byte equality across different
transition instances does not collapse their counts.

`NativeCountOwnership.native_count_from_uniqueness` now derives the actual native
witness-record count bound from these real views/balances and SHA hypotheses,
plus head coverage for native instances 0..K. The earlier explicit tagged-byte
coverage premise is gone. Six exact axiom guards pass in
`test/AuditRcptNativeCountOwnership.lean` (receipt scratch total 147).

Remaining count wiring: identify physical first-record prefixes with the SAME
extracted Node/Val views' nonduplicate filter counts, connect their SUM messages
to the candidate size table, and complete honest count rendering/admission. Native
instance head coverage and existing payload/root/SHA hypotheses remain explicit
assembly inputs.

### Physical same-view record count checkpoint

`SizeCountSegments` proves exact prefix counting over consecutive positive-length
segments. `SizeCountViews.node_count_view` binds the candidate node counter at the
actual SUM row to the nonduplicate count of the exact `NodeProof3.viewOf`.
`node_count_view_exists` derives segmentation and NodeWf from candidate local
constraints. `val_count_view` binds the value counter to the exact `valOf` map;
`val_count_view_exists` derives a complete segmentation from candidate local
constraints, handling both an empty table and zero-byte value records.

`PhysicalNativeCount.native_count_from_physical_prefixes` composes actual
uniqueness/SHA/parent coverage with these physical counters. Its node/value view
equalities explicitly require the SAME extracted views used by the native witness.
It preserves cross-transition tags and does not discard empty byte strings.
Remaining assembly obligations include synchronizing value segmentation with the
full ValWf/traffic extraction, and deriving the final SIZE count accumulator from
the candidate arity-3 SIZE global balance. No advertised overhead or arbitrary
counter is assumed to cover dictionary/store costs automatically.

Strict bounded Lean checks passed for all three new modules. Exact tests
`AuditRcptSizeCountViews` (6 guards) and `AuditRcptPhysicalNativeCount` (1 guard)
passed; receipt scratch checkpoint now has 154 guards. Only standard logical
axioms occur. Active tables, frozen descriptors, and accepted native domain are
unchanged. Files are durable in the main workspace; Git is read-only in this
sandbox, so this checkpoint is not committed.

### Candidate SIZE receiver and final accumulator authentication

`SizeCountControl.layout` derives the exact four-row table (three active receives,
one padding) from candidate-local constraints, without assuming the removed old
payload-only total bound. `SizeCountAccumulator.received_counts` extracts exact
arity-3 traffic. `authenticate_counts` uses message-count equality and distinct
SIZE tags to authenticate every received payload and record-count cell; source
contributes an explicit zero count. The physical count and payload accumulators
are exact sums of those three cells.

`authenticated_total_bound` derives the natural 8 MiB inequality from the actual
24-bit slack, authenticated traffic, correctly bound public overhead, and an
explicit global no-wrap bound. `authenticated_witness_paid` composes exact native
encoding charges, retained payload/count domination, and dictionary encoded size
to prove complete native witness length at most 8 MiB. It does NOT silently infer
that the advertised overhead is the actual native overhead.

Two new modules and seven exact axiom guards passed strict bounded Lean checks
(`test/AuditRcptSizeCountAccumulator.lean`); receipt scratch now 161 guards.
Still open: deriving the aggregate candidate supplier message-count equality from
all physical Node/Val/source sender tables using the SAME extracted views;
composing actual prepared overhead/no-wrap with the final assembly. The current
receiver theorem takes that exact count equality as a named premise, not a full
AIR balance claim. Candidate bus arity-3 descriptor/admission integration remains
explicit and frozen tables are unchanged.

### Physical SIZE supplier bridge

`SizeCountNodeSender.node_size_sender` now extracts the unique physical candidate
node message `[0, nodePayload(view), nondupCount(view)]` for exactly the same
`NodeProof3.viewOf`. `SizeCountValSender.val_size_sender` extracts the analogous
value message from a complete physical segmentation. Its existential variant
derives the segmentation from local constraints, including empty tables and
zero-byte records. Value payload excludes empty bytes; value record count includes
empty records. `SizeCountDecorate.decorate_singleton` preserves unique physical
supplier ownership while attaching a row-dependent count; no equality of counters
on unrelated rows is assumed.

`SizeCountSourceSender.source_size_traffic` transforms complete source traffic by
appending zero record counts, also usable per source partition. Its singleton
specialization retains the explicit original source coverage theorem.
`SizeCountProviderBalance.count_balance_from_physical` composes the actual physical
sender lists and receive-count balance into the exact three authenticated SIZE
messages required by `authenticated_witness_paid`. No arbitrary advertised count
is left in this local provider composition.

All five modules passed strict bounded checking. Six sender guards and one
provider-balance guard passed (`AuditRcptSizeCountSenders`,
`AuditRcptSizeCountProviderBalance`); receipt scratch total is now 168.
The physical balance still needs the global no-extraneous-SIZE-provider assembly,
and original source partition traffic coverage must be supplied. Value segmentation
must coincide with the full ValWf/other-bus extraction used elsewhere. These are
explicit remaining composition obligations, not claimed solved by local sender
extraction. No active table, descriptor, native domain, or proof-size model changed.

### Synchronized value extraction, physical source coverage, and public overhead

`SizeCountValView.val_view_from_segments` exposes the existing full value proof
for a caller-owned segmentation. `SizeCountValComplete.val_candidate_view` now
produces ONE view satisfying ValWf and every candidate bus equation, including
arity-3 SIZE. The previous value-view synchronization obligation is closed.

`SizeCountSourcePartitions.partition_size_sender` reconstructs the SAME logical
BlockChain from the two actual extended physical partitions and their carry
balance, then proves they jointly emit exactly one `[2, sourceCharge, 0]` message.
No independent source-SIZE-coverage premise remains in that theorem.
`SizeCountSourceBounds.source_lengths_bound` uses exact physical RCL multiplicities
to bound the SUM of list lengths by receipt rows. Path charges are bounded by
source rows. `SizeCountNoWrap.source_charge_cap` consequently gives
`sourceCharge <= 2^24 + 2^22`; node/value payload and record counts each have their
actual 2^22 bounds. These physical bounds imply no wrap once fixed overhead is at
most 8 MiB. The SIZE inequality itself is not used to establish no wrap.

Candidate-only `countedPreparedBytes p chunkInner` computes
`224 + chunkInner.length + 44*p.lists.length + 69*p.hdr.K` and admits it only when
at most 8 MiB. Successful construction binds public overhead naturally and supplies
the no-wrap premise. This is a new isolated public constructor, not a change to
frozen preprocessing, descriptors, or accepted native domain.
`SizeCountAcceptedOverhead.accepted_fixed_overhead` proves that the actual unchanged
native checker plus successful preprocessing always satisfies this bound. It uses
actual decoded-witness size, native distinct-key cardinality, exact prepared source
occurrence count, and `SizeCountPreparedK.prepD0_implicit_count`. Repeated source
keys and arbitrary unused filler entries are retained. Note that D0Shape alone has
a broader codec cap; the proof explicitly uses the native 8 MiB raw-size guarantee
and canonical encoder coverage rather than confusing those bounds.

`SizeCountPreparedPaid.prepared_witness_paid` proves the complete witness size
bound for that prepared candidate with no separate overhead-meaning or no-wrap
premise. Remaining assembly inputs are actual global SIZE balance/isolation,
retained payload domination, existing exact dictionary charge binding, and native
field identities. Retained COUNT domination is already derived from uniqueness.
The concrete whole candidate protocol family/descriptors remain unassembled; no
claim of automatic no-extraneous-provider isolation is made.

Strict bounded checks and exact guards passed for the new checkpoints:
`AuditRcptSizeCountComplete` (6), `AuditRcptSizeCountBounds` (7),
`AuditRcptSizeCountOverhead` (5), `AuditRcptSizeCountAccepted` (6).
Receipt scratch total: 192 guards. Main workspace sources are durable; Git remains
read-only in this sandbox.

### Weighted retained payload closure

`UniqWeightedTraffic` transports arbitrary natural EID weights through the actual
DIGS/PARENT/VPARENT balances. `UniqWeightedNondup` subtracts the actual DUP weights;
`UniqPayload.nondup_payload_exact` instantiates byte lengths and proves the exact
nonduplicate representative total equals the same Node/Val SIZE payload.
`RetainedStorePayload` proves weighted tagged-store subset domination, retaining
separate transition instances and allowing zero-length bytes.
`NativePayloadOwnership.native_payload_from_uniqueness` combines this with the
existing actual uniqueness/SHA store coverage: no independent weighted coverage
or retained payload premise remains.

`SizeCountNativePaid.prepared_native_witness_paid` now pays the executable native
witness from these same views, removing both payload and record-count domination
premises. Remaining composition inputs are native fixed-field identities, exact
dictionary charge instantiated to the same source/receipt chains, head coverage,
and assembled provider SIZE balance. The existing source charge/no-wrap/public
constructor results remain applicable; no active table or descriptor changes.
Six additive modules passed strict bounded Lean checks. The durable
`test/AuditRcptWeightedPayload.lean` passes 18 exact axiom guards, using only the
standard axioms. Receipt scratch total: 210 guards.

`SizeCountWitnessFields` derives the executable witness's post-root widths from
actual HeadWf plus the already-needed per-transition head coverage; missing heads
are not assumed valid. The applied-receipts hash width follows from SHA256.
`SizeCountSourcePaid.authenticated_dictionary_witness_paid` now combines the
actual same source/receipt chains, SRC34/RCL/SHA authentication, and constructed
native dictionary with weighted ownership and final SIZE payment. It derives
source charge capacity from physical rows and K equality from successful prep/walk;
there is no independent dictionary-size, source-size-cap, payload, count, implicit
count, or transition-hash-width premise. Claim epochId width remains explicit.
Public ownership/SHA isolation, same dictionary, head coverage, and the final
assembled provider balance still require full candidate family composition.
The proof uses a logical source table of height at most 2^24; the physical cap22
four-partition adapter under development is a separate step.
`test/AuditRcptSizeCountSourcePaid.lean` passes four additional exact guards.
Receipt scratch total: 214 guards. No active/frozen files changed.

### Native claim and ROOT-chain closure

`SizeCountClaimFields.decoded_claim_epoch_length` derives epochId length32 from
actual `decodeClaimE` success and its `pHash` read. `walk_claim_epoch_length`
transfers that fact through the actual successful native walk, without assuming
native witness acceptance. `prepared_head_coverage` uses the existing
`RootChain.head_mem` and exact prepared/native implicit-count equality.
`SizeCountChainPaid.chain_authenticated_witness_paid` composes these facts with
source authentication and SIZE payment: no independent epoch-width or per-index
head-coverage premise remains. The same actual ROOT chain is an explicit input,
as required for the rest of the state-transition semantics.
Strict bounded checks and `test/AuditRcptSizeCountChainPaid.lean` pass four more
exact axiom guards. Receipt scratch total: 218. Remaining integration is the
physical partition/provider family, actual public/SHA isolation contracts, and
candidate admission; no complete certificate claim is made.

### Honest cap22 source endpoints

`SourceLog22Endpoints` proves first-partition local validity without the old
two-partition capacity restriction. Its shifted last-partition proof uses actual
padding at the physical cyclic endpoint. `honest_four_local` combines these with
`SourceLog22Local.middle_local`: all four actual SIZE-wrapped tables are locally
valid at log22, with explicit honest cell placement at offsets 0, H-1, 2(H-1),
3(H-1), for H=2^22 and the existing source envelope R≤16334272. The proof preserves
overlap transitions and introduces no path-depth or native domain restriction.
`test/AuditSourceLog22Endpoints.lean` passes five exact axiom guards after a strict
bounded single-module check. Physical extraction/carry/global traffic assembly is
owned separately by the root agent. Receipt lane scratch guards now total223
(including these five source endpoint guards).
