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
| g2 | **8,178,273** | kernel checked, margin **210,335** bytes |
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
