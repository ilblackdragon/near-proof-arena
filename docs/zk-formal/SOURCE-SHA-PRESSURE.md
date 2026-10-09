# Source SHA capacity review

The present source upper bound cannot safely be reduced to two log22 SHA tables
using only path-byte accounting or removal of equal SHA preimages. A checked
structural fixture already exceeds their combined 8,388,608 rows before adding
any receipt, trie, scheduler, or upsert hashing.

## Checked evidence

`ZkFormal/NearV3/Rcpt/Candidates/SourceShaPressure.lean` constructs one receipt
proof entry with empty receipts, shard IDs zero, and 240,000 path steps. Step i
uses the distinct32-byte sibling `leN 32 i` and native direction zero. Its claimed
root is the actual native `rootFromPath` result.

- Native `verifyReceiptProof` returns true, without any SHA assumptions.
- Exact encoded entry length is 7,920,056 bytes, leaving468,552 bytes below8MiB.
- Its actual path preimages are pairwise distinct. Taking their first32 bytes
  recovers the distinct sibling encodings, regardless of hash collisions.
- Each path preimage is64 bytes and costs35 rows in the existing SHA renderer.
  Including the32-byte leaf rehash costs8,400,018 rows:11,410 over two tables.
- The fixture is symbolic and kernel checked; it does not allocate or evaluate
  240,000 real SHA calls to establish these facts.

This is a verified native receipt-proof/encoding fixture, **not** a complete
accepted `checkD0a` claim. Header, signature, state-transition, and whole witness
assembly have not been constructed for it. Consequently it rules out a two-table
argument based only on the established local proof conditions and byte envelope;
it does not prove that no deeper accepted-domain correlation exists.

## Slack in the old bound

The8,932,712 source-row envelope independently maximizes1984 computed lists and
254200 path items. Correlating56 bytes per empty dictionary entry and224 fixed
witness bytes gives the checked conditional arithmetic:

`1 ≤ L` and `56*L + 33*d + 224 ≤ 8388608`
imply `18*L + 35*d ≤ 8896703`.

This improves the bound by36,009 rows, but is still508,095 above two tables before
other families. The correlated premise is a proposed tighter accounting input,
not a new theorem of complete native coverage. Even perfect removal of all but
one of1984 leaf rehashes saves only35,694 rows in that coarse envelope.

## Reuse and remaining options

Repeated source-key work is already removed by the existing first-occurrence
candidate. Equal receipt-list leaf hashes, equal complete proof payloads, and
shared path suffixes may offer instance-dependent savings. None guarantees a
reduction for the single long distinct-prefix fixture. There is no native
path-depth check in `verifyReceiptProof`; a depth-six argument from a nominal
64-shard layout would narrow the accepted model unless derived elsewhere.

The other SHA-family maxima share witness resources, so their independent sum
may be loose. That correlation alone cannot resolve a source-only bound already
above two tables. Further work must either derive a stronger unchanged-checker
invariant excluding such long proofs, find a semantics-preserving compression of
these distinct computations, or change the SHA/proof architecture and reprove
its soundness and size. No active/frozen cap or accepted-domain change was made.

Strict bounded Lean compilation and `test/AuditSourceShaPressure.lean` pass eight
exact axiom guards, with only the standard axioms.

## Complete-family inventory and three-bin checkpoint

`SourceShaResidualPacking.lean` and `SourceSchedulerThreePacking.lean` now prove
whole-message packing for the **actual accepted source + scheduler upsert +
scheduler sanity subset** in three log22 bins. No message is split: the scheduler
batch is placed in bin zero and greedy source prefixes fill its residual capacity
and the other bins. Flattening the bins recovers the entire original weight list
in order. Source weights are at most35; the generic residual theorem needs only
70 rows of aggregate slack. Strict compilation and
`test/AuditSourceShaThreePacking.lean` pass six exact axiom guards.

This does not establish complete-family three-bin capacity. The inventory is:

| SHA jobs | Concrete source | Capacity evidence / gap |
| --- | --- | --- |
| Source leaf rehash and path jobs | `DedupCompile`, `SourceSchedulerShaLog22` | Actual native accepted bound8,932,712, each job≤35; packed above. |
| Scheduler upsert output values and node parts | `Assembly/UpsertShaCapacity` | Actual accepted jobs≤1,662,140 rows. |
| Scheduler root sanity | `Assembly/SchedulerSanityJobs` | At most32 jobs of64 bytes,1,120 rows. Combined scheduler batch≤1,663,260. |
| Pre and post node serializations | `Extract/NodeView.nodeSends3` | Both NPRE and NPOST emitted for every occurrence, including duplicate occurrences. `Assembly/ForestNodeBytes` bounds seeded pre-node bytes by native `preBytes`; this is not a complete SHA row bound for final V3 views. |
| Nonempty prestate value blobs | `Extract/ValProof.valSends` | VPRE emitted per nonempty occurrence, including duplicates. Empty values produce no VPRE bytes. A concrete all-job row bound is still required; do not charge only retained dictionary representatives. |
| Receipt-list RC encoding | `Rcpt/Extract/RcptView.rcptSends3` | One header plus ordered receipt encodings per computed list; RC hashing is separate from the32-byte source leaf rehash and must not be omitted. Complete native job/row accounting remains open. |
| Outcome partial encoding and leaf | `Rcpt/Extract/RcptView.rSends` | PEO and LEAF jobs per applied receipt. Existing `Rcpt/ShaRows` models lengths133 and68; requires constructor-to-native coverage for final inventory. |
| Refund receipt ID | `Rcpt/Extract/RcptView.rSends` | Conditional RID48-byte job. Refund body bytes use the public RF record, not an extra SHA job. |
| Updated account value | `Rcpt/Extract/AcctProof.acctV3Sends` | VPOST72-byte job per account record. Requires native count and alias/occurrence accounting. |
| Outcome Merkle internal nodes | native `NearSpec/Outcome.merkleLevel` and Merkle AIR | Pair hashes64 bytes, odd leaf promoted. Expected n−1 jobs for n positive leaves; final concrete inventory/cardinality proof still needed. |

The historical12,674,664 scalar sum consists of source8,932,712,
`trieShaRows 1998836 = 2,498,545`, and receipt remainder1,243,407. It does **not** include
the separately constructed scheduler batch. Appending its proved maximum yields
14,337,924, exceeding three bins by1,755,012. Even replacing the source term by
the conditional correlated8,896,703 gives14,301,915, excess1,719,003. These are
checked arithmetic diagnostics, **not proved global upper bounds**: the trie
scalar lacks a full current-V3 coverage theorem. In particular the older
`Near/Render/Proof/ShaFit2.node_rows` includes an extra144-times-dead-node term
before division by4, and does not itself account for the V3 value blob jobs.

The proved subset leaves1,986,940 aggregate rows for all remaining jobs before
packing slack. Independent maxima cannot show they fit. A valid tighter result
must correlate actual source/dictionary bytes, retained and duplicated native
node/value encodings, receipt count/bytes, and scheduler writes, or change the
hash/proof architecture. Deduplicating stored bytes alone does not suppress the
current per-occurrence SHA traffic.

Whole-message packing adds a separate obligation. The residual theorem allows
large non-source jobs to be assigned first, then fills their residual capacities
with small source jobs at a70-row slack cost. The final proof must construct that
large-job assignment and bound every assigned bin; a total row sum alone does not
imply packability. The new accepted-subset theorem supplies this assignment only
for the scheduler batch. No complete three-bin certificate, reduced frozen cap,
new native-domain restriction, or active table change is claimed.

## Native occurrence-byte correlation now checked

`NativeOccurrenceSha.lean` proves `forest_occurrence_bytes`: the sum of actual
`forestStoreViews` node pre-serialization lengths plus actual value payload
lengths is **exactly** `preBytes` of the native forest, with every occurrence
retained. `accepted_occurrence_bytes` derives their joint bound≤B from successful
unchanged `checkD0a B`, its native main execution and implicit execution trace.
It neither assumes uniqueness nor pays node and value totals independently from
B. Thus duplicated unfolded subtrees are charged correctly.

The companion SHA inequality is deliberately honest about short-message costs:

`8 * (2 * nodeHashRows + valueHashRows)`
`≤ 10 * preBytes + 288 * shortNodes + 144 * shortValues`,

where short means length<43. It conservatively charges empty values too, although
actual VPRE omits them. The duplicated node term covers the store-only seed, whose
pre/post serializations coincide; it is not yet a bound for final updated post
views. This is a checked correlated intermediate inequality, not a complete
numeric three-bin bound. Native short-value counts, dead-node overhead, updated
post serialization coverage, and the other inventory families remain to compose.

Strict compilation and `test/AuditNativeOccurrenceSha.lean` pass five exact axiom
guards, standard axioms only.

`NativeShortValues.lean` further proves the actual same forest allocates at most
134,028 value occurrences:133,966 in the main transition and at most two in each
of31 implicit transitions. `accepted_short_values` obtains these native guards
from successful `checkD0a`, without adding a restricted domain. Therefore the
short-value correction144*shortValues is at most19,300,032 in the scaled-by8
inequality (2,412,504 rows). This is intentionally conservative and does not solve
the full three-bin budget. Three exact axiom guards pass.

A tighter remaining route is structural amortization: value references already
occupy36 bytes of their node encoding, and a revealed nonroot node's hash consumes
32 bytes in its parent. These bytes can potentially pay short-message overhead
jointly. That amortized inequality is not yet proved. Final updated node
serialization and witness-byte correlation remain independent obligations; the
store-only seed lemmas do not establish either automatically.

## Structural overhead amortization now checked

`NativeShaAmortization.lean` closes the structural payment proposed above.
For each well-formed native tree it proves

`43 * nodeOccurrences + 36 * valueOccurrences ≤ unfoldedBytesT + 32`.

The mutual tree/children induction uses actual32-byte child hashes and36-byte
value references. No uniqueness or balanced-tree assumption is needed. Combining
this with `16*rowsOf(n) ≤ 5*n+288` gives

`344 * forestShaRows ≤ 503 * preBytes + 9216 * rootCount`.

Here `forestShaRows` hashes each pre-node encoding twice and every revealed value
once. It conservatively includes empty values, which actual VPRE omits. This pays
all short-message overhead without the separate short-node or short-value count
premises. `accepted_forest_sha_bound` obtains≤2,925,275 rows directly from the
unchanged accepted checker, whose actual B0 is2,000,000, and at most32 transition
roots. The historical scalar used1,998,836 bytes; substituting it for B0 would
require a separate derived overhead deduction.

Eight exact axiom guards and strict compilation pass. This bound applies to the
native prestate occurrences and store-only seed's identical pre/post encodings.
It does not yet authenticate or bound final updated post-node encodings, nor
prove the complete job family fits three bins. The remaining receipt families,
source/witness-resource correlation, and whole-message placement remain explicit.

## Final node digest updates preserve SHA lengths

`NativePostShaLength.lean` proves for **arbitrary** `NodeV3.wf` views that
`(v.ser true).length = (v.ser false).length`. The updated child and value digest
windows are32 bytes on both sides; all other serialization components are shared.
`node_pair_rows` consequently rewrites the complete NPRE+NPOST row count to twice
the pre-serialization row count under actual `NodeWf3`, without assuming the
post bytes equal the pre bytes. Four strict exact axiom guards pass.

Thus final NPOST hashing does not need a separate increased-length allowance.
Applying the numeric native forest bound to a final assembled view still requires
its same-occurrence pre-encoding and value-byte correspondence and NodeWf3. Newly
created upsert nodes are accounted separately in scheduler upsert jobs. This
length proof does not itself establish those assembly correspondences or full
three-bin capacity.

## Concrete native execution-view correspondence

`NativeViewShaRows.native_view_sha_rows` now identifies the exact node/value
length workload of `nativeExecutionViews` with the native forest occurrence sum.
`accepted_native_view_sha_bound` derives≤2,925,275 for those concrete allocated
views directly from successful `checkD0a`, with no separately assumed occurrence
correspondence. It remains a workload theorem, not a claim that the semantic seed
already satisfies all AIR constraints. `updated_native_rows` transfers it to
arbitrary `NodeWf3` views preserving the native pre-length and value-length lists;
updated digest contents need not match the seed. Three exact guards pass.

## Actual receipt payload batches, preserving byte correlation

`ReceiptShaPayloads.lean` defines the actual per-list RC preimages (header plus
ordered encodings, including empty lists) and per-receipt PEO/LEAF/conditional RID
preimages. `RcptE.Wf` proves their concrete length bounds347/133/68/48, and the
non-RC batch costs at most105 rows per receipt. More usefully for correlation,
with C the **actual total encoded receipt bytes**, n the flattened occurrence
count, and L the list count, the checked batch inequality is

`64 * (RCrows + PEO/LEAF/RIDrows) ≤ 17*C + 6720*n + 1492*L`.

No fixed path-depth premise or nonempty-list exclusion is introduced. Seven exact
axiom guards pass. This establishes concrete payload workload bounds from receipt
view well-formedness; a complete native receipt renderer/traffic job assembly is
still separate. Account VPOST and outcome Merkle preimages are not included in
this batch theorem. Their concrete native count/coverage proofs remain open, so
the historical receipt remainder is still not a complete proved job inventory.

## Concrete Merkle/account jobs and native touched accounts

`MerkleShaCount` proves the actual `mrkShape n` contains exactly n−1 hashed nodes,
including n=0 and n=1. `MerkleShaJobs` supplies reusable `levelsFromLeaves` and
`levelTable` constructors from actual leaf preimages, without v1 Info. The
shape-ordered jobs have exact cardinality n−1, all preimages64 bytes, and exact
cost35*(n−1). Odd nodes retain the child's identifier and digest. Native root
semantic correspondence is a separate root-agent proof.

`AccountShaJobs` defines exactly the V3 account VPOST payload `post++pre.drop16`.
Under existing `AcctWf`, every payload is72 bytes and total rows are35*A. VPRE
already belongs to Val and is not duplicated through the old v1 account job
constructor. The combined concrete receipt/account/Merkle workload satisfies

`64*rows ≤ 17*C + 6720*n + 1492*L + 2240*A + 2240*(n−1)`.

These three modules pass twelve exact axiom guards.

`NativeAccountTouches` extracts an actual sequence of successful `PTrie.set`
operations from `applyReceipts`, including system receipts. It proves exactly one
write per input receipt and exact receiver-key order. `newchunk_touched` extracts
this same run from the actual internal receipt stage of successful
`applyNewChunk`. Canonical last-occurrence touched keys are unique, cover exactly
the runtime account writes, and have cardinality≤n. Six exact guards pass.
Connecting those canonical keys to the eventual concrete account AIR records is
still required; arbitrary AcctWf records do not automatically have cardinality≤n.

The independent proved source/scheduler/native-prestate maxima already sum to
13,521,247 rows, before receipt jobs, exceeding three bins by938,335. This is not
an impossibility result: the maxima need not be simultaneously attainable.
A complete three-bin allocator still needs stronger shared witness/native byte
correlations, particularly scheduler state/update demand, and the remaining
constructor/traffic bindings. No acceptance guard or frozen cap was tightened.

## Four-bin fallback: checked whole-job allocation

The candidate fusion budget retains four SHA tables, so the unproved temporal
correlation needed for three bins is no longer required for this allocation.
`SourceShaFourPacking` proves residual greedy packing with three cut losses,
requiring only source messages of at most 35 rows. `FourShaJobAllocator` operates
on complete job objects, proves flattened permutation preservation, and fits
four log22 bins using the following separate bounds:

| Batch | Rows |
| --- | ---: |
| Source | 8,932,712 |
| Scheduler upserts and sanity | 1,663,260 |
| Native NPRE/NPOST/VPRE occurrences | 2,925,275 |
| Receipt, account VPOST, outcome Merkle | 1,373,299 |
| Total | 14,894,546 |

The first three non-source batches occupy dedicated bins before source jobs fill
the residual capacities; therefore a large native or scheduler message is never
split, and only the source maximum-message bound is needed for packing slack.
The 105-row maximum cut loss fits below the four-bin capacity 16,777,216.

`ReceiptShaCapacity` proves the last bound from actual payload definitions,
receipt count at most 4481, source-list count at most 1984, and account count at
most 8192. The account bound is the existing log17/16-row account-table capacity;
it does not assume the still-unassembled account constructor has A≤n.
It permits an empty account list explicitly. `ReceiptShaJobs` constructs complete
RC, PEO, LEAF, conditional RID, account VPOST, and Merkle jobs with their actual
message identifiers, proves their exact weight list, and instantiates the
whole-job allocator. RC jobs include the header for empty source lists. Fourteen
exact axiom guards cover these four modules, with strict auto-implicit settings.

This closes the numerical allocator, not the final all-table SHA admission.
`allocate_receipt_batch` still takes the scheduler/native/source batch bounds as
explicit premises; the independently proved native occurrence bound must be
connected to the same updated node/value views, and all batch byte/digest
traffic and identifier ownership must be assembled. The generic permutation
proof preserves complete objects, including any multiplicity field supplied by
the eventual SHA job type. No accepted native input was excluded.

## Empty account table candidate

`AccountEmpty`, `AccountEmptySound`, and `AccountEmptyTraffic` replace only the
first-row account constraint `isFirst*(1-af)` with `isFirst*(act-af)`. Width,
height, interaction list, and constraint count are unchanged. Every old valid
trace remains valid. A candidate trace either satisfies the entire old local
predicate or has zero act/af/gS gates throughout; the latter branch has no
messages on any bus. An explicit two-row all-zero trace is locally valid and
has empty traffic. Thirteen exact axiom guards pass. This additive candidate
restores the empty-account case without weakening the nonempty extraction or
changing the native domain; it is not yet installed in the final table family.

`NativeShaJobs` now constructs physical-order NPRE/NPOST jobs and nonempty VPRE
jobs. Its actual rows are bounded by `nodeValueShaRows`. The theorem
`accepted_updated_nativeShaJobs` derives 2,925,275 from the same successful native
execution, ordinary NodeWf3, and exact prestate-node/value length-list
correspondence. Updated post digest windows are arbitrary: their serialization
length invariance is proved, not assumed. Four exact guards pass. The length-list
correspondence is still a constructor obligation, and this new theorem does not
assert that a native seed already satisfies final node AIR constraints.

## Exact view-to-job byte traffic

Twenty further exact guards now cover six additive modules:

- `NativeShaTraffic`: complete native NPRE/NPOST/VPRE jobs emit exactly
  `nodeSends3 ++ valSends` on BYTES. Ordinary ValWf proves that precisely empty
  values suppress VPRE jobs; no uniqueness premise is used.
- `ReceiptShaTraffic`: account VPOST bytes agree exactly, and every positioned
  RC fragment reassembles into its complete header-plus-receipts preimage.
- `ReceiptJobOrder`: located source-list enumeration has exactly the global
  receipt order of `flatR.zipIdx`, retaining repeated/empty source occurrences.
- `ReceiptByteBatch`: whole receipt BYTES traffic is a permutation of the
  concrete RC/PEO/LEAF/RID job bytes plus the exact public refund fragments.
  This is multiset equality, not merely membership or prefix agreement.
- `SourceJobTraffic`: nonduplicate source jobs emit exactly the dedup candidate
  source view's BYTES traffic, for arbitrary repetition metadata.
- `ShaJobBridge`: source-job conversion is exactly the existing accepted-source
  compiler's `sourceShaMessages`; generic Render.Msg conversion preserves exact
  physical SHA row weights. `fourSha_physical_fit` produces four actual
  `Sha.Gen.Msg` bins with `honestRows.length≤2^22` and flattened permutation.

These are view-level traffic theorems. The physical table extraction/renderer
bridges must instantiate them with the same views; byte bounds, digest traffic,
global ownership, and native updated-constructor correspondence remain distinct
obligations. Refund fragments intentionally remain public-body traffic.

`ShaAllocationTraffic` adds four exact guards: Render.Msg conversion has exactly
`jobBytes` as the SHA generator's expected bytes, and arbitrary full-job
permutation preserves both expected BYTES and DIGEST multisets across bins.
This includes the actual digest multiplicity flags. It does not replace the
separate proof that the digests consumed by each application view are these
computed digests. The new traffic series totals twenty-four guarded theorems.

The trie lane currently has no final updated-node constructor beyond the forest
seed and provider/window interfaces. Thus final constructor length correspondence
is not yet derivable from an existing implementation; the explicit premise in
`accepted_updated_nativeShaJobs` remains a recorded assembly obligation.

## Implemented final node-window update

`NodePostUpdate` now supplies an executable update, instead of leaving final
windows wholly abstract: it hashes concrete child/value byte payloads, replaces
revealed child post windows, and marks selected value post windows written.
Keys, length bytes, node/value IDs, pre digests, memory bytes, and all NodeS3
metadata stay exact. `NodePostFacts` and `NodePostWf` prove unchanged pre
serialization, unchanged edges/walk targets, canonical raw data, child-ID
placement, and preservation of the complete NodeWf3 predicate. Nineteen exact
axiom guards pass.

`NodePostNative` connects the selected slot and leaf to the actual native
same-length `PTrie.set` result: final serialization equals the native post-node
encoding. It also proves updated node/value SHA rows exactly equal the initial
allocated view's rows, eliminating a separate final-view length assumption for
this concrete constructor. Four additional exact guards pass.

Remaining native correspondence: extend the leaf proof through extensions and
branches, instantiate child/value payload lookup from the same receipt-write
execution, and compose sequential writes. Structural scheduler upserts remain
separate. Existing `TrieOps.set_upsert_comm` is the intended proof for commuting
native scheduler-before-receipts order into the AIR receipt-writes-before-UPS
order. The initial allocated forest's complete counters/NodeWf3 validity still
needs construction; preservation does not assert that the old seed had it.

## Native recursive pairing and ordered writes

The native extension case now constructs its replacement child payload directly
from successful `PTrie.set`, and proves exact serialization (including the
actual child hash). `NativeWriteLookup` composes an entire native account-write
run into a concrete array replay at the initial trie's stable preorder slots.
Removing absent slots gives exactly V3 `valsOf` of the actual final tree. Repeated
writes preserve order and overwrite the same slot. These modules pass ten exact
guards (`AuditNativeNodeWrite`).

`NativeWriteSkeleton` proves the recursive same-shape relation from actual
successful `PTrie.set`/`Kids.set`, then composes it across sequential account
writes. Hidden hashes, keys, branch child presence, memory fields, and slot
kinds remain identical. `NodePairedViews` is a second concrete constructor that
takes the native pre/post trees directly, rather than requiring arbitrary hash
callbacks. Its post serialization equals the actual post node encoding for
leaves, extensions, and branches; its pre serialization remains exactly the
original view. The post theorem retains the native same-length root-value
obligation. `NodePairedWf` proves recursive slot/child/node well-formedness from
the original shallow view's well-formedness. These three modules pass twenty-five
exact guards (`AuditNativePairedViews`).

Remaining work is to allocate the paired views through the whole native forest,
prove exact compact value and child IDs, instantiate same-length account writes,
and fill initial global counters/metadata so complete NodeWf3 holds. The shallow
paired-node theorem does not assert this unfinished global allocation.
