# Source-proof budget candidate (not active)

The current source renderer and SHA linker are checked. Their completeness contract still
requires the existing `srcpRows ≤ 2^20` cap. The actual D0a relation has an 8 MiB witness
limit but no Merkle path depth cap. This document proposes an architectural repair;
no active table cap, frozen parameter, domain condition or admission theorem is changed.

## Encoding and reuse

Each decoded path item consumes a 32-byte sibling and one direction byte. Thus a witness
can contain at most `floor(8,388,608 / 33) = 254,200` distinct encoded path items. This
ignores all other serialization overhead and is deliberately conservative. `RawWitnessBudget.relD0a_selected_path_budget` now proves this directly from successful
unchanged `RelD0a`: actual parser consumption charges 33 raw bytes per path item and
last-wins computational selection is a sublist. No re-encoding-coverage premise is needed.
Likewise, `1984 = 31*64` uses the existing source
occurrence envelope and still needs its successful-preprocessing derivation.

`lookupLast` can select one encoded proof at many source occurrences. A2 and distinct
applied receipt IDs force a repeated selected proof's receipt list empty, but do not
bound its path length. Replaying that path at every occurrence incurs up to 1984 times
the encoded path cost. The following are conservative upper envelopes, not exhibited
fully accepted adversarial witnesses:

| Quantity | Per-occurrence replay | Each selected proof computed once |
|---|---:|---:|
| Path items processed | 504,332,800 | 254,200 |
| Source rows (`33L + 64D`) | 32,277,364,672 | 16,334,272 |
| K_SRC SHA input bytes (`32L + 64D`) | 32,277,362,688 | 16,332,288 |
| Source SHA rows (`18L + 35D`) | 17,651,683,712 | 8,932,712 |

For replay, both row envelopes require log35 tables; the largest source message number
can reach 504,334,784, making `16*q + K_SRC` exceed the base field. A cap increase alone
cannot support this envelope. The deduplicated envelopes require log24 if kept in one
table. At blowup16 that means LDE log28, beyond Fp's two-adicity27.

## Candidate architecture

1. Select each used last-wins witness proof once. Keep an occurrence-to-proof reference
   for every prepared source list. Do not deduplicate receipt application order.
2. Check public key/root/reference consistency. Equal-key roots follow from the actual
   shared lookup and successful receipt verification; no hash injectivity assumption is
   needed. In soundness, this relation must be enforced, not assumed from arbitrary roots.
3. Enforce empty duplicate receipt lists using A2 and distinct IDs. The unique selected
   proof and all duplicate occurrences must share the same receipt list, leaf and path.
   Merely skipping duplicate path verification without this linkage is unsound.
4. Preserve the spec dictionary cardinality: `distinctKeys entries.length == used` counts
   source occurrences, not unique selected keys. The witness encoder must retain the
   existing unused filler-entry mechanism. Deduplicating hash computation does not permit
   deleting those dictionary entries.
5. Partition source computation into at least two log23 tables (splitting a long path
   needs an authenticated accumulator/counter continuation). Partition SHA computation
   similarly, with explicit ownership and global ID routing. Whole-message allocation
   requires a proved bin-packing bound, not just a total-row inequality.

With the existing A1 receipt envelope and `B0=1,998,836`, non-source receipt SHA work is
1,243,407 rows and trie SHA work is 2,498,545. Adding unique source work gives **12,674,664
SHA rows**, below two log23 tables' 16,777,216 combined rows. This does not include new
wiring overhead or a proof of partition placement.

## Proof-size model and limitations

The isolated candidate shape model duplicates the existing SHA and source table shapes,
sets each copy to log23, raises only the model's `maxLogLde` to27, and leaves other shapes
unchanged. The g2 result is kernel checked:

| Auxiliary grouping | Modeled proof bytes | Status |
|---|---:|---|
| g1 | 8,524,225 | exploratory `#eval`, exceeds 8 MiB |
| g2 | **8,190,337** | updated for Ups200, margin **198,271** bytes |
| g3 | 8,232,097 | exploratory `#eval`, margin 156,511 bytes |

The model excludes added reference/continuation columns and interactions, queue tables,
and any further assembly additions. It is not an AIR admission or security theorem.
LDE27 reaches the field limit and needs revised verifier parameter/security validation.
The small g2 margin makes unmeasured additions material. Existing frozen proof-size
claims remain about their original shapes and parameters.

Checked candidate modules: `Rcpt/Candidates/SourceBudget.lean`, `SourceSize.lean`,
`SourceSizeCheck.lean`, `RawWitnessBudget.lean`, and `SourceCount.lean`. The existing complete source renderer is
`Rcpt/Render/Srcp/ProofComplete.lean`; its row-budget premise remains explicit.

## Checked repetition semantics and remaining integration

`PreparedSourceCount.prepD0_source_count` now derives the 1,984 occurrence bound
from successful real preprocessing, including the source slice and shuffle loops.
`RawWitnessBudget.relD0a_selected_path_budget` derives the 254,200 selected-path-item
bound directly from actual raw decoding and the unchanged 8 MiB check; no canonical
re-encoding size premise remains.

A lower-overhead candidate reuses the existing later-duplicate flag for deciding which
occurrences compute a proof, and adds an all-occurrence repetition bit computed from
prepared keys. The latter marks the first occurrence too. `SourceRepetition` proves
that every marked occurrence has raw receipt-list length 12 under the routed distinct-ID
condition, and that later duplicates are marked. It also defines the native equal-key
root consistency check and proves it follows from shared last-wins verified entries.
Representative verification then transfers to all occurrences under that check.

These are isolated semantic APIs. The active SRC payload remains width33; adding the
repetition bit requires a coordinated width34 public descriptor and AIR transition
change. The current source header cannot be terminal or skip directly to another header,
so header-only duplicate rows need new constraints and checked rendering. Deriving all
semantic API premises from the complete successful validator/preparation paths remains
an explicit integration obligation. No extra native check may narrow RelD0a.

Root's provisional combined queue shape (48 main columns, 8 auxiliary terms, degree5,
8 interactions, log22) gives an exploratory 8,313,602-byte total with the partitioned g2
model, leaving only 75,006 bytes for all additional wiring. This is a planning estimate,
not a checked final queue AIR shape or admission result. Continuations, public repetition
metadata, proof partition ownership, and existing walk-table capacity must all fit the
final accounting before any active cap or frozen pin is changed.

The source authentication premise has now been extracted from the real validator:
`Link.CheckedSources.checkD0_sources_verified` connects successful `checkD0` to its
actual walk/witness decoder outputs and proves every new source slot's last-wins
lookup, from/to shards, and Merkle-root verification. `Link.RelSources` derives those
outputs and raw routing directly from `RelD0a`, and proves equal actual source keys
have equal roots. `Candidates.PreparedVerified` preserves those authentications through
the exact prepared slot/shuffle loops. Connecting the full `prepClaim` output to that
same source-block slice is the remaining prepared-record bridge; no native consistency
check has yet been added to active preprocessing.

## Active log22 restriction and candidate protocol scope

The active verifier does **not** admit the two-log23 model. `Air/Basic.lean:Table.wf`
hardcodes `T.maxLog ≤ 22`; `V2/Air.lean:AirP.wf` directly reuses that predicate.
`Candidates.SourceSize22.log23_not_wf` proves rejection for every table with maxLog23,
independent of expression validity or a larger `Params.maxLogLde`. This is a protocol
implementation restriction, not an additional restriction to impose on the NEAR domain.

An alternative using four source partitions and four SHA partitions at log22 retains
maxLDE26 but fails the proof-size target before new wiring. Exploratory evaluation of
`Candidates.SourceSize22` gives:

| log22 model | Proof bytes | Excess over 8 MiB |
|---|---:|---:|
| g1, no queue | 9,708,997 | 1,320,389 |
| g2, no queue | 9,278,437 | 889,829 |
| g3, no queue | 9,345,765 | 957,157 |
| g2 + actual candidate parser shape (37,3,6,3,22) | 9,375,462 | 986,854 |
| g2 + provisional combined queue shape (48,8,5,8,22) | 9,413,766 | 1,025,158 |

These are shape-model `#eval` results, not kernel-checked admission claims. They still
exclude new source repetition/continuation wiring. They make a separately reviewed
log23 protocol generalization the preferred candidate over simply adding log22 tables.

The candidate parameter record now sets both `maxLogLde=27` **and `posBits=27`**.
Setting only maxLogLde leaves 26-bit query positions unable to sample the full largest
LDE domain. Nine 27-bit positions still fit a 256-bit oracle answer (243 bits). The size
model does not read posBits, so this necessary correction does not change its byte count.
It does not establish protocol security or admission.

Before active assembly can adopt log23, a separate candidate protocol must close:

1. A parameterized or candidate-specific table-height well-formedness predicate and its
   extraction facts (`Air/Basic`, `V2/Air`, `Udr/Np/Early`). Preserve the existing log22
   predicate and deployed challenge pins while developing the candidate.
2. Header/layout/subgroup bounds through log23 traces and log27 LDEs (`Udr/Np/Msg4`,
   `Msg8`, `V2/Np/Early`, `V2/G/Early`, `V2/G/Groups`, `V2/G/V1`). The field's actual
   two-adicity27 is the limit. Do not reuse default maxLDE26 facts by coercion.
3. DEEP and FRI bad-challenge bounds (`Udr/Np/Chal7`, `Udr/Np/Late`, `V2/G/Late`,
   `V2/G/Main`). Chal7 currently uses `T≤2^22`; Late currently bounds only logs≤26.
   Recheck the `2^36` bad-event budget for the larger domains, and recompute actual
   bus multiplicity/fingerprint bounds for every new partition and continuation.
4. Query coverage and ROM soundness (`V2/G/Defs`, `Query`, `RomFull`): introduce an
   explicit candidate parameter family, prove queryLog≤27, 9×27≤256, the required
   agreement/dominance and QueryOk inequalities, verifier query count, and the final
   128-bit numerical security inequality. `NpOkPg` currently forces the deployed
   `pg g` family and is not a certificate for the candidate parameters.
5. Honest-prover completeness and proof-byte accounting (`V2/PG/Np*`, `V2Prover`,
   `V2/PG/Admission`), including hints, record descriptors, all AIR shapes, and the
   8 MiB encoded proof cap. The active admission theorem is tied to deployed `pg`;
   a new candidate admission theorem must compose the rebuilt semantic and crypto facts.

No active protocol, challenge definition, or frozen pin has been changed by these
candidate calculations. Current executable `DedupRender` has checked row accounting
and header-only duplicate behavior, but still has no new AIR local/traffic or partition
continuation theorem. Those obligations and the protocol work above remain open.

## Actual-input candidate capacity closure

`Candidates.DedupCompile` now compiles every actual prepared occurrence, preserving
its root, index, and existing duplicate flag, while advancing source message counters
only for first-occurrence leaf/path computation. `FirstSources` proves that retaining
indices with the actual public duplicate flag false gives distinct keys. The selected
entries are a permutation of their last-wins dictionary representatives, so their path
sum is bounded directly by raw decoding.

For successful unchanged `RelD0a`, successful actual `prepD0`, and the actual raw witness
decoder outputs, the executable candidate now has checked bounds:

- source renderer rows ≤16,334,272;
- source hash-preimage bytes ≤16,332,288;
- source SHA work (18-row leaf messages, 35-row path messages) ≤8,932,712;
- source messages ≤256,184; next-message counter ≤256,185, with canonical field IDs.

These bounds no longer take a path-depth or computed-path-sum premise. They do not
assert that the new rows satisfy a yet-to-be-defined dedup AIR or that new SHA traces
have been rendered and connected on the buses.

`PartitionCapacity` checks exact logical-row reconstruction and two log23 physical
source capacities with one carried boundary row. It also checks greedy whole-message
SHA packing: the source-only envelope fits when each message has at most35 rows.
The full 12,674,664-row SHA envelope fits two log23 partitions when each message has
at most2,228,242 rows; an 8 MiB preimage has that row bound. Proving the largest-message
premise for every non-source SHA input is still open. Likewise the carried boundary
state must be authenticated and local/traffic soundness proved across the split; list
placement lemmas alone do not establish those AIR contracts.

## Concrete payloads and repeated-source semantics

`DedupSha` proves that every actually decoded source leaf preimage has 32 bytes and
all path preimages have 64 bytes. Their actual `msgRows` weights agree with the
18/35-row accounting above, and the actual source payload sequence admits the checked
two-log23 whole-message packing. This still does not prove SHA table rendering or bus
balance.

`PreparedReceipts` proves that actual preparation's shuffled source-list order, mapped
through last-wins witness lookup and receipt routing, gives exactly native
`appliedReceipts`. `PreparedRouting` transfers D0a's A2 routing guarantee to every
prepared selected source. Combined with the native successful-check distinct receipt-ID
guard (`Assembly.SourceResult`), `PreparedRepeated` proves that **every occurrence** of a
repeated prepared key has an empty raw receipt list, including its first occurrence.
Consequently the concrete candidate block has `L = 12`. This is derived from unchanged
`RelD0a`, actual successful preparation, and actual witness decoding; there is no new
receipt emptiness or key-distinctness assumption.

`DedupTable` is an isolated concrete 57-column candidate with 122 constraints and five
bus interactions. Kernel checks establish column bounds and degree at most four.
Executable integer fixtures cover both path directions, duplicate-to-computed transitions,
a physically full trace ending on a duplicate, and rejection of inconsistent repetition
metadata/length. Its new public SRC payload is `[j, dup, repeated] ++ root`, so adopting it
still requires coordinated public descriptor and binding changes. The active public SRC
schema remains unchanged. General local, traffic, continuation, and candidate protocol
admission proofs are tracked separately; these checks do not certify a succinct protocol.

The candidate now has checked all-constraint local theorems for duplicate-to-root,
duplicate-to-padding, and a duplicate physical last row. `DedupComputedLocal` transfers
all original constraints on non-duplicate rows to the patched table, with exactly the
new repetition metadata conditions. `DedupTraffic` connects actual candidate field bus
traffic to natural row records and proves complete root-header messages. Complete
rendered-trace locality, aggregate traffic, and authenticated partition continuation
remain open. Seven executable fixtures and twelve transitive axiom guards check this
isolated checkpoint; all dependencies use only Lean's standard logical axioms.

## Current concrete source and reserved queue budget

`SourceCurrentSize` replaces both synthetic 56-column source entries with the actual
57-column `DedupTable` shape. At grouping2 its kernel-checked shape is
`(w, aux, quot, fin, maxLog) = (57, 3, 5, 3, 23)`. Executable model evaluations give:

| Included candidate components | Model bytes | Remaining below8MiB |
| --- | ---: | ---: |
| Actual source57/Ups200, two source/two SHA partitions | 8,192,193 | 196,415 |
| Above plus actual parser37/3/6/3/log22 | 8,289,218 | 99,390 |
| Above with combined queue52/8/6/8/log22 reserve | 8,338,178 | 50,430 |
| Combined queue reserve plus explicit source carry-table shapes | 8,359,074 | 29,534 |

The parser37 shape is now derived from the actual merged ValueTable.table; its original kernel check was at
8463ced1/9f596fd8. The combined52 shape is a **provisional reserve**, including fifteen
additional base columns for unimplemented queue walk/control and additional auxiliary,
quotient, and final columns. It is not an implemented table or a proved capacity bound.
The last row's exact model equality and29,534-byte margin are kernel checked. This is
now the relevant source/queue estimate, replacing the earlier210,335-byte spare margin.
Other unimplemented wiring must fit the remaining margin, and the final admitted AIR
must be measured again; the table is not a final encoded-proof guarantee.

`DedupPartitionTable` makes source continuation costs explicit. Its first partition
suppresses all constraints and normal message multiplicities on its physical last row,
which carries a complete57-field state to the second partition's first row. The second
partition suppresses only global-first source constraints. Carry send/receive are
unconditional endpoint selectors. Multiplicity digits are individually gated (they are
binary digits, not a list of multiplicative factors). The first table has degree5 base
constraints and shape57/4/7/4/log23; the second has shape57/3/5/3/log23. These extra
interactions and gating cost20,896 modeled bytes. Source carry reserves bus64, distinct from QVC63 and QSH29; the integrated AIR needs
at least65 buses. Separation from every other bus, a distinct namespace for any SHA
continuation, and fingerprint/multiset soundness for the full57-field carry record
must still be proved.

The quotient cost is per table: `Stark/Protocol.lean` defines `Table.degree` from that
table's base/multiplicity and generated auxiliary constraints, `Table.quotCount` as its
degree minus one, and `layout` reads that count separately for each table. The source
carry total degrees are8 and6, both below the unchanged blowup16 ceiling. `NpOkPg`
and `headerOk` use that ceiling, so this change does not require a larger global blowup
or larger quotient commitments for other tables. Candidate maxLog23/maxLde27 admission
and the protocol security numerics still require the separate rebuilding described above.

The overlap now has exact traffic-once and carry-count lemmas below. Global bus
soundness integration and complete local soundness/completeness across the boundary
remain obligations; syntactic size/degree checks alone do not establish them.

The logical renderer's full five-bus contract is now checked by
`DedupTrafficProof.table_traffic`: every root/leaf/path message is accounted for,
duplicate computation is omitted, padding is silent, and SIZE is emitted exactly
once with `sum (L + nonduplicatePathCharge)`. It needs only nonempty source blocks,
32-byte root/leaf/sibling/accumulator widths, and the trace-to-renderer cell equality;
it does not assume old source row caps or old `SrcpWf`. This closes logical aggregate
traffic. Logical local completeness is now closed by the later TableLocal checkpoint below.

`PreparedNonempty` now composes the actual `walkD0` decoder/lookup success with B2's
new-slot membership and proves exact preservation of source-slot counts through
preparation's shuffle loop. Thus actual successful `prepD0` with that native walk
has a nonempty prepared source list. `DedupActualTraffic` derives all source block
widths and nonemptiness from unchanged `RelD0a`, real preparation, and real witness
decoding, then instantiates the complete five-bus logical `TableTraffic` theorem.

`DedupCarry` checks carry messages against the actual partition interactions and
`tableBusCount_eq`: exactly one left send and one right receive occur; the opposite
sides emit none on64. Ideal carry-bus balance for this pair forces equality of the
complete57-field tuple, hence all57 individual row cells. This is a conditional
soundness lemma using exact bus counts, not a fixture comparison. Global assembly
must still prove every other table/public segment is absent from64 and obtain that
ideal balance from the existing cryptographic bus theorem. Full partition local legality is now checked below.

`DedupPartitionTraffic.pair_messages` and `pair_counts` now prove that the two
actual partition tables jointly emit exactly the logical renderer traffic on every
non-carry bus, including the single terminal SIZE record. The common overlap row
is suppressed only in the left table. The theorem uses equal physical heights,
logical row coverage, and exact renderer cell bindings; it does not assume traffic
equality. Honest overlap bindings also imply carry equality and exact carry-bus
balance. The partition audit now checks26 theorem axiom closures.

The merged Ups width increase187→200 adds12,064 modeled bytes. The updated
source/carry model is8,359,074 bytes with29,534 bytes remaining. It uses the actual
QV parser shape and still reserves an unimplemented combined52-column queue table.
Earlier exploratory g1/g3 and four-log22 figures above predate this Ups repair.

The candidate's complete SIZE budget now follows from actual accepted input:
`prepD0_dictionary_count` in `Candidates/DictionaryCount.lean` extracts
native `distinctKeys entries` cardinality equal to prepared source **occurrences**,
and `prepD0_sources_le_entries` bounds those occurrences by encoded entries. It
preserves unused filler entries and makes no selected-key distinctness assumption.
`SourceSizeEncoding` proves each encoded entry pays its unique computation charge
plus at least12 bytes of overhead. `DedupCompile.relD0a_size_bound` composes unique
last-wins selection, actual repeated-source emptiness, native dictionary cardinality,
and the decoder's canonical encoding non-expansion theorem to bound the full
candidate SIZE by the unchanged8MiB raw witness budget. The candidate audit now
checks98 axiom closures. This closes SIZE coverage; candidate AIR admission remains separate.

The candidate now has checked all122-polynomial local cases for computed and
initial roots, every internal leaf/path byte, the path-window boundary, leaf/path
segment transitions, computed source-to-source transitions (including a following
duplicate), terminal-to-padding transitions, physical terminal segments, and padding.
These supplement the existing duplicate-header cases. `DedupAdjacency.adjAt`
(the theorem is in the DedupRender namespace) proves the exact candidate descriptor
succession, and `DedupRender.mult_bits` proves actual field-valued multiplicity bits.
Whole logical-renderer composition is now checked below; physical partition TableLocal is now checked below.

Physical terminal segments need cyclic successor `sg=0`: several inherited segment
successor polynomials are not gated by `isTransition`. The logical trace wraps to
its first root, which supplies this fact. The right partition instead has physical
last padding on actual inputs:16,334,272 rows is strictly below the16,777,215-row
pair capacity. `padding_physical_last` permits any cyclic successor, including a
segment carry row. Partition completeness must use this actual capacity slack.
No protocol height, cap, source domain, or candidate shape changed in this checkpoint.

`DedupCompile.relD0a_table_local` now derives the complete logical candidate
`TableLocal` from actual unchanged RelD0a, preparation, decoding, and renderer cell
bindings. `TableFacts` contains only concrete semantic counter/index/repetition facts;
its actual-input constructor proves each field. No AIR-satisfaction premise, old
SrcpWf cap, or new path-depth premise is assumed. The proof covers all physical
endpoints, internal/cross-source transitions, terminal SIZE, arbitrary padding, and
field-valued multiplicity bits. Its log24 bound is an intermediate logical trace,
not an admitted deployed table. Actual deployment still needs candidate extraction/soundness, final integrated
bus disjointness/security, and the separate protocol admission family. The source AIR
audit now checks77 transitive axiom closures and seven fixtures.

`DedupCompile.relD0a_partition_local` now proves actual accepted input renders
into **both physical log23 source tables** with all local constraints and
multiplicity bits, from their concrete cell bindings. The only partition row
condition, `R ≤ 2*2^23−2`, follows from the existing16,334,272-row bound; it
ensures right-endpoint padding. Left constraints are suppressed only on the
carried endpoint, preserving the preceding transition; the right first row omits
exactly four global-first equations. A syntactic theorem checks every remaining
right expression is independent of `isFirst` and is an original constraint or
zero. Carry send/receive multiplicities are bits on every physical row. Together
with the already checked exact five-bus traffic and full-row carry equality, this
closes renderer local completeness for the physical source pair. The partition
audit now checks41 transitive axiom closures (standard Lean axioms only). Frozen
maxLog22 admission is unchanged: the separate candidate protocol family, source
extraction, and integrated bus security remain explicit obligations.

The right candidate table now explicitly enforces `isLast*(rt+sg)=0`. Honest
renderer padding alone was insufficient for soundness: the old last-row
constraints could follow a cyclic path carry (`next.sg=1`) and suppress terminal
`q=qe`/length checks. `AuditSourceEndpoint.lean` gives a kernel-checked local
regression with `qe=le=999`: all old right equations hold on the terminal row,
and the new endpoint equation rejects it. This is a local counterexample to the
missing endpoint invariant, not a claimed complete forged AIR trace.

Both actual-input partition TableLocal proofs still pass from the already proved
row slack. Direct field-valued reverse transfer now recovers all logical equations
from nonterminal left rows and all non-first equations from arbitrary right rows;
it does not infer integer polynomial equality from field equality. The added
endpoint equation plus root/segment disjointness proves both endpoint activity
flags individually zero for arbitrary accepting field traces. Rebuilding the
exact shape/cost target preserves the source right shape57/3/5/3/log23 and total
8,359,074-byte model with29,534 bytes reserved. The partition audit now checks49
axiom closures; four kernel regression assertions pass. Frozen admission and
active source tables remain unchanged.

`DedupPartitionTable.joined_sound` now closes sound partition reconstruction from
**arbitrary accepting field traces**, not just honest renderer cells. It takes
both physical `TableLocal` predicates, equal heights, and exact isolated carry-bus
balance. The carry theorem authenticates all57 source columns; evaluation
congruence explicitly uses the constraints'57-column bound. The reconstruction
keepsH−1 left rows, allH right rows, and clones the final inactive right row once,
producing logical height2H (log≤24). Checked inactive-row lemmas permit both the
new padding transition and the changed cyclic successor. All logical local
constraints and multiplicity-bit checks follow from the physical predicates.

`joined_messages` and `joined_counts` preserve every external message/count
exactly, including terminal SIZE. The cloned padding row emits no base traffic;
this property is derived from arbitrary source constraints, not a renderer
assumption. `AuditSourceJoined.lean` checks24 transitive axiom closures and three
physical-pair/logical-trace fixtures (leaf overlap, both path directions, duplicate
header). This is the source partition soundness bridge; candidate source semantic
extraction, global isolation of bus64, and the separate protocol security and
admission certificate remain unfinished.

Candidate semantic extraction now proves `DedupProof.extract_units`: every
accepting logical source trace has a nonempty consecutive decomposition into
one-row roots and32/64-row leaf/path segments, followed only by padding. It uses
the candidate logical log24 bound below the actual field modulus, not the old
source table's log20 cap. `old_row_of_nodup` recovers every original source
constraint on computed roots, segments, and padding. Skipped roots are treated
separately: they force repeated=1, L=12, qe=q, le=0, and no digest request; a
nonterminal skip advances j by one while preserving q. The all-occurrence
repetition bit also forces L=12 on the first computed occurrence. Segment
metadata, window counters, and register shifts are derived from arbitrary field
constraints. `AuditDedupExtract.lean` checks33 axiom closures. Grouping these units
into complete source views and closing their exact semantic traffic remains next.

`DedupProof.extract_blocks` now groups arbitrary accepting logical source rows
into a finite nonempty `BlockChain` of computed proof blocks and one-row skipped
headers. Natural source/SHA counters and identifiers are bounded using the
logical log24 height below the field modulus. Every computed block has its full
32-row leaf and finite sequence of 64-row path items, with consecutive hash
indices, matching root endpoints, canonical field representatives, and exact
vector lengths. Skips have L=12 and preserve the hash counter. The chain ends at
exactly `DedupRender.R bs`, and every remaining row is inactive. This is an
extraction theorem, not an assumption that accepting traces are honest renders.
`AuditDedupBlocks.lean` checks 44 transitive axiom closures. Cross-block numbering,
exact semantic traffic, byte/SHA linkage, and prepared repetition metadata remain
the next source extraction obligations; skipped roots still require linkage to
the earlier same-key computed proof.

Cross-block extraction now proves consecutive natural source indices and the
correct hash-counter link `next.ql = previous.qe + 1`; a skipped block has
`qe + 1 = ql`, so no nonexistent duplicate computation is counted. Every block
has either computed `BlockWf` or the exact empty skip shape. Root traffic now
matches `DedupRender.rootMsgs` on all non-SIZE buses directly from arbitrary
accepting rows, including the actual repetition bit and absence of a digest
receive for skips. `BlockSpan.repeated_empty` derives L=12 from that root's actual
bit. `AuditDedupBlockLinks.lean` checks 17 transitive axiom closures. Leaf/path
traffic and chain SIZE composition remain separate obligations.

`BlockChain.full_traffic` now proves exact whole-trace traffic on every non-SIZE
bus and both directions. The proof recovers leaf digest bytes in order, both
64-byte path concatenation orders, one predecessor digest request per path item,
and the exact root/leaf/path message concatenation for every extracted block.
Skipped headers emit no private proof traffic, and trailing inactive rows emit
nothing on any bus. The semantic `chainMsgs` reads only each root's repetition
bit from the trace; all root positions follow from extracted block lengths.
Consequently this is not an honest-renderer assumption or a restatement of raw
row traffic. Prepared public SRC balance must still authenticate those bits.
Seven modules compile and `AuditDedupPayloadTraffic.lean` checks 26 transitive
axiom closures. Final SIZE traffic, SHA-bus semantic linkage, and candidate
AIR-to-Good assembly remain unfinished.

`DedupProof.extract_source` now packages complete combinatorial extraction and
exact traffic on all five source buses from arbitrary accepting logical traces.
The SIZE gate is uniquely the final active row even when the final block is a
one-row duplicate skip. Its payload is exactly the field cast of the natural
sum of L plus 33 per computed path item, with no local no-wrap assumption.
The extracted sequence is nonempty, has exact natural j indices starting at 0,
starts its hash numbering at 1, and obeys every consecutive endpoint link.
`AuditDedupExtractProof.lean` checks 20 transitive axiom closures. Together with
`joined_sound`, the physical pair can now be linked to this extraction without
assuming an honest renderer. Remaining source obligations are global bus
isolation and size no-wrap, byte/SHA semantics, prepared SRC repetition/key/root
matching, and source semantics within the complete AIR-to-Good assembly.

Candidate SHA semantic linking now closes for every computed source block.
`BlockChain.payload_wf` derives canonical source IDs and disjoint computed
intervals directly from arbitrary candidate rows; skipped intervals are empty.
`payload_field_unique` and `payload_bytes_isolate` prove exact message isolation
without the old per-occurrence computation model or log20 source cap. The existing
closed `ShaFacts`/`sha_core` contract then supplies byte ranges and source digest
values. `source_hashes_of_sha` reconstructs every predecessor and final digest;
`BlockChain.verifyReceiptProof` concludes the unchanged native receipt-proof
verifier from exact SHA bus contracts and the linked RC leaf digest/path.
Seven modules compile and `AuditDedupSourceSha.lean` checks 30 transitive axiom
closures. No collision assumption is introduced. Global bus-to-contract assembly,
RC leaf binding, prepared source metadata/root consistency, skipped-occurrence
same-key reuse, and size no-wrap remain explicit premises/obligations.

Candidate public source binding and skipped-proof reuse are now checked.
`SourcePublic.plan` has 34 payload bytes (dup, repeated, root32), giving 35 field
limbs after the record index. It is additive; active SRC33 and frozen descriptors
are unchanged. Exact descriptor-record evaluation, canonical record decoding,
and field-count equality authenticate the extracted occurrence count, source
indices, both bits and roots. `BlockChain.bind_prepared` discharges the public
index bound using actual prepD0's at-most-1984 source count. It also derives L=12
for every publicly repeated occurrence, including the first computed one.

`prepSourceD0` is a candidate-only executable preparation wrapper that checks
equal-key roots/from-shards. Its soundness and completeness are kernel checked:
unchanged RelD0a plus successful prepD0 implies wrapper success, so this introduces
no new accepted-input assumption. `first_source_cover` proves every prepared key
has a nonduplicate first occurrence using the actual sourceDup computation.
`BlockChain.sources_authenticated` combines these facts with SHA authentication
of computed blocks to authenticate every last-wins source entry, including
skips. RC leaf/dictionary/path binding and global exact bus contracts remain
explicit premises. Six modules compile; `AuditDedupSourcePublic.lean` checks
26 axiom closures and seven kernel fixtures. Candidate final assembly must still
select SRC34 and the preparation wrapper and rebuild the complete statement
layout/admission certificate; neither is silently installed in the frozen family.

`DedupPartitionTable.physical_source_extract` now packages the complete physical
source bridge: arbitrary accepting left/right tables plus exact isolated carry
balance produce a logical block chain, a nonempty bounded semantic sequence and
exact external message multiplicities on all buses except the carry namespace.
`AuditDedupPhysicalExtract.lean` checks its transitive axiom closure. This directly
composes the checked partition, extraction, SHA and public-source interfaces;
global carry isolation remains a final assembly obligation.

The next receipt-side blocker is now explicit: `RcptV3ViewStmt` is defined but no
whole-table theorem constructs `RcptV3Wf`. Existing `Extract/V` proofs cover
per-receipt field layout, bytes, basic bus traffic, characters and keys. Whole
list/header decomposition, encoded-length no-wrap, receipt arithmetic/system/
routing facts and table traffic composition still need proof. In particular,
RCL equality alone is a field equality; deriving repeated L=12 implies an empty
receipt list requires the actual list encoded length below P. This must come from
receipt row/span bounds, not an extra domain premise or an assumed extracted view.

### Actual receipt list decomposition and length bound

`Rcpt/Extract/V/ListBlocks`, `ListChain`, and `ListLengths` now derive complete
physical receipt-list blocks from the unchanged `RcptV3.table` local constraints.
Every block has its actual twelve-row header, a possibly empty consecutive list
of receipt layouts, and a next-header or padding boundary. Row-zero extraction
produces a nonempty chain with exact physical row sum; padding cannot resume
active rows after its end. This is extraction, not an assumed `RcptV3Wf` view.
For each extracted receipt, the exact encoding length is `123 + Vt`, bounded by
its physical receipt interval. Consequently every extracted list's full encoding
length is below the actual table height and therefore below `P`. Length twelve
is equivalent to an empty extracted receipt list. These bounds impose no new
receipt-list or domain restriction.

Validation: three modules build; `AuditRcptListExtraction.lean` checks nineteen
exact transitive axiom outputs (only the standard Lean axioms). Still open:
header count/index and encoded-offset reconstruction, complete receipt traffic,
and the remaining system/routing/arithmetic obligations needed to construct
`RcptV3Wf` and bind source RCL/dictionary/leaf data. The no-wrap bound alone does
not establish that RCL traffic contains the extracted encoding length.

`ReceiptOffsets`, `HeaderOffsets`, and `EncodedOffsets` additionally reconstruct
the actual offset cells: receipt starts have `rf=1`; a header starts the next
receipt at offset twelve and count one; each receipt's `oEnd` adds its exact
extracted encoding length; adjacent layouts preserve that end offset. The
whole block's terminal `oEnd` now equals its natural `lOffs` length cast into
`Fp`, including empty lists. Thus the earlier physical bound applies to the
actual terminal offset, not merely an unrelated semantic encoding. Ten exact
transitive axiom guards pass. Terminal `le`/RCL traffic, global list indices,
and full semantic receipt extraction remain separate outstanding obligations.

`ListTerminal` closes the positive terminal RCL direction: a block boundary has
`rf=0`, its preceding row is a real break, and therefore `le=1`. The actual
terminal row's RCL traffic is exactly one message carrying its list-index cell
and the extracted full encoding length. Five exact axiom guards pass. This
does not yet exclude RCL messages elsewhere or reconstruct the global index
sequence; those are the next whole-traffic obligations.

`ListInterior`, `ListGate`, `ListConstants`, and `ListIndices` exclude every
interior list-end gate, prove all block rows active, preserve every `lconsts`
column inside the block, and reconstruct the global list-index sequence.
For a chain starting at physical row zero, header `k` has index `k` in `Fp`;
the terminal row has the same index. The gate is exactly `q+1=block.stop` on
all block rows. Thirteen exact axiom guards pass. Remaining RCL composition
work is the full row-traffic multiset and padding exclusion, followed by the
source/receipt bus binding; full receipt semantic extraction remains open.

`RclTraffic` and `RclProof` now close whole receipt-table RCL traffic exactly:
the ordered sends are the extracted blocks' records, one per list, carrying the
header's preserved index and its nonwrapping encoded length. No inactive row,
including the cyclic physical last row, emits RCL; the table has no RCL receives.
Eight exact axiom guards pass. The source-to-receipt global bus ownership/balance
composition and full semantic receipt extraction remain explicit work.

`RclDecode` and `DedupReceiptLengths` connect the channels semantically. Twelve
header rows per list bound the natural list count below `P`; exact RCL record
matching uniquely decodes both index and encoded length. Under the actual source
and receipt local constraints, extracted chains, and explicit equality of their
physical RCL counts, a source block of length twelve has an actually empty
extracted receipt list at that exact index. Duplicate and all-occurrence repeated
flags derive this length from their existing local source constraints, including
the first computed occurrence. Ten exact axiom guards pass. No `RcptV3Wf`, new
encoding bound, or restricted domain is assumed. Global RCL ownership and balance
must still be supplied by assembly; receipt bytes, header count, system/routing,
and arithmetic semantics remain open parts of whole receipt-view extraction.

`ListCounts` and `ListView` reconstruct the actual per-list receipt counter:
every receipt increments it; terminal `cj` and header `nj` equal the extracted
receipt count in `Fp`. Header registers 8/9 hold its low two count bytes, and
registers 10/11 are forced zero. The view is now defined from those actual
registers and extracted receipt layouts. Under range checking of the two emitted
count bytes, its natural `n0+256*n1` equals the actual receipt count, using the
physical row bound to rule out modular aliasing. Nine exact axiom guards pass.
The range checks remain an explicit BYTES/SHA obligation, not an added input
restriction or an already-proved semantic receipt-view assumption.

`HeaderRegisters` and `HeaderTraffic` prove the actual twelve header BYTES
messages, exactly `emitAt RC(j) 0 (hdrBytes pub view)`. Active-field register
shifting supplies each byte; public loads fix the first eight own-shard bytes;
the count registers and forced zero high bytes supply the remaining four. The
other two header emission slots are disabled. Seven exact axiom guards pass.
No byte-range claim is hidden in this equality: range checking must still be
linked to the BYTES/SHA channel before using the natural header-count theorem.

`GlobalCounters` and `GlobalListCounters` reconstruct global receipt numbering:
headers preserve `r` and body offset, the first receipt inherits them, receipts
increment `r`, and the next list header inherits the previous terminal `r+rl`.
Header `k` therefore has the natural prefix receipt count cast into `Fp`, with
initial counter zero; receipt `i` within the list adds `i`. Empty lists are
included. Ten exact axiom guards pass. These are actual physical counters, not
extra witnesses or assumptions. Global refund-body offset reconstruction is
still needed to assemble existing per-receipt byte traffic.

`BodyOffsets`, `ListBodyOffsets`, `GlobalBodyOffsets`, and `PrefixOffsets` now
reconstruct both offset families completely at receipt starts: RC offsets are
12 plus preceding receipt encoding lengths in the list; body offsets are 8 plus
all preceding enabled refund lengths, across headers and receipts. Actual
`o2End` adds exactly `rfLen`, with refund encoding length `129+2*Ls+32*kt`;
non-refund receipts add zero. The additive prefix theorem is proved over the
actual consecutive physical layouts. Thirteen exact axiom guards pass. Whole
BYTES traffic composition and the remaining semantic receipt Wf obligations
remain open; no new external counter or range assumption was introduced here.

`BlockBytes`, `ListByteTraffic`, and `ChainBytes` now prove complete physical
receipt-table BYTES send extraction. The result is a permutation of ordinary
`chainByteMsgs` starting at list index zero, receipt index zero, and body offset
eight. Each list contains its concrete public/count header and all existing V3
receipt byte views (RC encodings, refunds, PEO, LEAF, and RID preimages), positioned
by exact natural prefix lengths. The physical padding, including the cyclic last
row, emits no bytes. Six exact axiom guards pass. The final theorem has no
external counter, offset, or semantic-view assumptions: only TableLocal and the
extracted chain. Pure reformatting to the existing `rcptSends3` API and the
remaining whole receipt Wf/other-bus obligations are still open.
