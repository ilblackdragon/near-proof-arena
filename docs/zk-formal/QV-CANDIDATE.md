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
indices, mismatched buffer counts, truncated headers and mixed segments. These
examples do not replace general extraction and honest-renderer proofs.

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
