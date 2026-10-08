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
`trieShaRows B0 = 2,498,545`, and receipt remainder1,243,407. It does **not** include
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
