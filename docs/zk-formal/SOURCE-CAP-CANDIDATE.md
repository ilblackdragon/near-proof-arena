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
