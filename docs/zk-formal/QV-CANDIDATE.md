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
