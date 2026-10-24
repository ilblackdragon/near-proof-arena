# Reusable hash templates: corpus geometry

2026-10-24. `hash_capacity.py` exported all **64/64 D0a fixtures** successfully.
Evidence: `evidence/hash-capacity.json`, with claim/witness/exporter hashes.
This is a geometry census, not proof verification or full NEAR coverage.

Receipt SHA maxima: 2,460 messages, 5,875 compressions, largest individual message
1,747 compressions (`00-h10035-s3`). That fixture contains 815 one-block messages,
1,640 two-block messages, two three-block messages, and one each of 7, 20 and
1,747 blocks. A uniform 1,747-block allocation per message costs 4,297,620 slots.

Candidate fixed receipt policy covering this corpus:

| Maximum blocks per message | Message slots |
|---:|---:|
| 1 | 1,024 |
| 2 | 2,048 |
| 4 | 8 |
| 8 | 4 |
| 16 | 2 |
| 32 | 1 |
| 2,048 | 1 |

Total: **7,296 compression slots, 3,088 message slots**, 24.2% more blocks than
the largest observed receipt workload. Transaction SHA has a separate candidate
304-block/142-message-slot policy. These policies were derived from the corpus;
freeze them before testing independently held-out chunks. Overflow must reject
or select a separately identified capacity class, never truncate a workload.

Implementation alternatives:

1. Use existing Binius `sha256_varlen` with public bucket capacities and private
   lengths. Bind active masks, IDs, lengths and computed digests in a canonical
   batch statement. Inactive slots must have a canonical encoding. The gadget
   already constructs padding and selects the length-dependent final digest.
   This is the shortest path to measuring setup reuse across different shapes.
2. Use a fixed stream of compression blocks (8,192 covers this receipt corpus),
   with constrained reset/last/active flags, initial IV, chaining state, padding,
   message byte positions and digest bus. It removes per-message worst-case
   capacity, but requires more new correctness and completeness arguments.

The bucket approach uses fewer compression slots here and more existing code;
test it first. Neither slot count includes the hash-batch root, masks, length
checks, byte bus, cross-field bridge, recursion or proof-size overhead. In
particular, `sha256_varlen` may have materially different per-block constraints
from the paired fixed-length gadget. Do not multiply the 1.084 s warm measurement
by 1.242 and present that as a latency prediction.

Source inspection found another concrete overhead in the current Binius gadget:
its block capacity derives from storage words, not the tight length range. A
b-block bucket permits 64b-9 bytes; rounding storage to eight-byte words allocates
64b-8 bytes, which makes `sha256_varlen` construct b+1 blocks. Across this policy
that is **10,384**, not 7,296 compression slots. A tighter helper can avoid the
extra block only if it explicitly enforces the tighter length bound; a metadata
annotation alone is not a constraint. Also construct `ByteVec::new` with private
length/data wires explicitly: the current `new_witness` constructor allocates a
public length and takes a word count despite its byte-oriented example.

Required experiment: one fixed circuit/setup, at least two actual chunks with
different lengths/counts, independent host digests, honest verification and
wrong-ID/length/digest/mask rejection. Report construction separately, but charge
it to cold startup; prove reusable keys depend only on the declared capacity
policy. Whole-chunk receipt binding remains a separate gate.
