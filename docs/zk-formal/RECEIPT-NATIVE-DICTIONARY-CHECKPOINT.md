# Receipt-to-native dictionary checkpoint

This additive checkpoint is checked in the writable main workspace against the
read-only AIR compiled dependency tree after receipt commit `94a32ac9`. It is not
an end-to-end succinct transition certificate.

`Rcpt/Candidates/NativeSourceDictionary.lean` proves
`DedupProof.BlockChain.native_dictionary_facts`: actual source and receipt local
constraints, their physical chains, successful candidate preparation, real source
public-message binding, physical RCL balance, and the explicit SHA contracts yield
an executable dictionary satisfying native source selection, shuffle success and
the frozen occurrence-based dictionary cardinality. Repeated keys select the same
first authenticated source entry; all included native slots are covered through
an exact permutation of prepared source descriptors. Prepared/native owner
identity is derived from successful `prepD0` and `walkD0`.

The dictionary includes executable fresh fillers: enumerate twice the actual
prepared-source count as canonical 32-byte keys, exclude prepared keys, then take
exactly `source count - first occurrence count`. Successful preparation gives
source count at most 1984. Distinctness and capacity are proved without a hash
collision assumption or fresh-key oracle. Every filler uses zero from/to shard
IDs and empty receipt/path vectors; its native `entryWf`, decoder round trip and
56-byte encoded cost are proved. Total filler cost is exactly
`56 * (source count - first occurrence count)`, at most 111104 bytes. This cost
must be charged in the final witness-overhead/SIZE accounting; the checkpoint
does not assert it fits unused space in an arbitrary 8 MiB witness.

Remaining obligations are substantive: authenticate the global SHA and bus
ownership premises, bind candidate source public metadata in the final admitted
protocol, prove receipt routing and exact applied-receipt assembly, and charge
all constructed dictionary bytes in the whole native witness budget. The source
facts do not claim these missing fields of `SourceSemanticsV3`.

Validation: direct Lean 4.34.1, 16 GiB virtual-memory limit, explicit `-j1`,
`-DautoImplicit=false -DrelaxedAutoImplicit=false`, read-only AIR dependencies
plus `/tmp/nearproof-receipt-check` overlay. Ten additive modules and eight audit
files contain 37 exact axiom guards, only `propext`, `Classical.choice`, and
`Quot.sound` where required. Main-source order:

1. NativeDictionary
2. NativeDictionaryVerified
3. PreparedCoverage
4. PreparedNativeOwner
5. NativeSlotSelection
6. NativeDictionaryCount
7. PreparedShuffle
8. NativeFillers
9. PreparedKeyCount
10. NativeSourceDictionary

No active table, frozen domain, public descriptor or protocol pin was changed.
Git and external-worktree mutation are unavailable under the current sandbox;
these sources and audits remain main-workspace additions for later integration.

## Exact source SIZE binding

`NativeDictionarySizeBinding.BlockChain.native_dictionary_size` now proves the
actual constructed dictionary-vector byte length is exactly
`DedupRender.size bs + 44 * p.lists.length + 4`, using actual source/receipt local
constraints, physical chains, native prep/walk, RC SHA byte authentication, and
RCL/public metadata balances. Key/path widths and per-entry native byte lengths
are derived; they are not final premises. This closes the source contribution
needed by the global size proof. Each skipped occurrence already contributes
12 bytes to the source SIZE total, explaining why the remaining overhead is
44 bytes per occurrence even though each complete filler encodes to 56 bytes.

The following six additive modules extend the checkpoint to sixteen modules:
`NativeDictionarySize`, `Link/NativeListSize`, `NativeSourceSize`,
`NativeSizePartition`, `NativeEntryShape`, and `NativeDictionarySizeBinding`.
`AuditRcptNativeDictionarySize` and `AuditRcptNativeDictionarySizeBinding` add
nine exact guards, for 46 total. These use the same strict bounded checker.

`Public.bindPrepared` still accepts an externally provided natural
`witnessOverhead`; it explicitly does not authenticate its witness-size meaning.
For example preparation alone cannot imply overhead is at least `44*N+4`,
because this argument can be zero. Final assembly must bind that public number
to the computed non-SIZE witness remainder including this deterministic source
contribution, while retaining natural no-wrap bounds. No such binding is claimed
by the current checkpoint and no active public gate was silently introduced.

## Routing and ordered-application bridge

`Candidates/NativeDictionaryRouting.lean` transports physical receipt routing to
all computational dictionary entries, and then to every native `usedProofs`
receipt using actual `SourceDictionaryFacts.selected`. This handles repeated
source keys and excludes unused fillers by the existing selected-inl invariant.
`NativeAppliedBinding.lean` composes successful actual preparation/shuffle with
those facts into `SourceSemanticsV3`, leaving the precise ordered
prepared-occurrence/dictionary-to-physical-receipt equality explicit.

That equality is not yet proved from AIR. In particular, repeated representatives
must be shown empty using authenticated repetition metadata and the twelve-byte
source charge, and skipped physical lists must likewise be empty. The checked
`NativeEmptyList.lean` closes the encoding step: an exact twelve-byte native
shard/receipt-list preimage forces the physical receipt list empty, without a
receipt-wellformedness premise. It does not itself assert the repetition metadata
or SIZE connection for every physical occurrence.

The new seven dictionary-routing/application guards and three native-empty-list
guards pass under strict bounded Lean. Durable tests are in `zk-formal/test/`.
Receipt scratch checkpoint totals 103 exact guards. Native source semantics and
full certificate soundness are not claimed complete.

## Full native source semantics from candidate AIR

`Candidates/CandidateSourceSemantics.lean` now proves
`DedupProof.BlockChain.candidate_source_semantics`, closing both previously
explicit native routing and applied-receipt equality obligations. Its conclusion
is the actual `Assembly.SourceSemanticsV3` for the concrete first-occurrence
`nativeDictionary`, fresh unused fillers, and the SAME complete physical receipt
view. The theorem retains actual source/receipt local AIR and chain hypotheses,
RCL/SRC balance, SHA facts and byte ownership, exact normalized BNDP public records
and boundary counter balance, actual preparation and native walk success, and
public owner/range bindings. These are genuine global assembly inputs, not hidden
native source-semantics premises.

`PhysicalRepeatedOccurrence` derives empty lists at every repeated prepared
index directly from public repetition metadata and existing physical RCL
extraction. `PhysicalSourceCount` derives exact source/receipt list cardinality
from whole RCL balance. `NativeOccurrence` proves first-key dictionary lookup
matches each occurrence list; duplicate reuse is valid because BOTH the original
and repeated occurrence lists are empty. `PhysicalOrderedReceipts` then proves
exact ordered flattening, not merely a permutation. `PhysicalSourceSemantics`
composes this with the actual prepared shuffle, dictionary selection/count and
routing. The final candidate theorem supplies routing using normalized boundary
records and exact original-layout routing equivalence.

Eight additional exact transitive axiom guards pass in
`zk-formal/test/AuditRcptCandidateSourceSemantics.lean`, using only the standard
three axioms. Receipt scratch total: 113 guards. All modules checked with strict
implicit-variable settings, `-j1`, and a 16 GiB virtual-memory cap. Source semantics
is now closed under the explicit candidate AIR/global-bus hypotheses; complete
certificate soundness, protocol admission, and global encoded-witness/WOVH
composition remain separate work. Frozen native acceptance was not narrowed.
