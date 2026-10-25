# Reusable hash templates: corpus geometry

## Implemented experiment

One fixed bucket circuit and one PCS setup now prove two different real message
layouts, alternating large/small twice. The circuit binds active masks, private
IDs, multiplicity flags, private lengths and computed SHA digests through a fixed
SHA-512 batch root (64 public bytes). Inactive metadata must be zero. The root
does not yet bind to the NEAR receipt proof; this is still a component statement.

The copied Binius variable-length helper now uses an explicit upper byte bound,
checks it in constraints, and derives block capacity from that bound. Its 44
boundary checks compare against independent host SHA-256 and reject over-bound
lengths. This removes the extra block caused by rounded storage allocation.

| Case | Messages | Ready after exported batch, two runs | Verify | Analytical bytes |
|---|---:|---:|---:|---:|
| 00-h10035-s3 | 2,460 | 1.666 / 1.708 s | 0.712 / 0.721 s | 116,481 |
| 00-h10012-s1 | 12 | 1.720 / 1.745 s | 0.716 / 0.731 s | 116,460 |

All four honest proofs and 24 negative checks passed. Mutants change the public
root's active/ID/length/digest records, the proof tape and the opening norm. These
are rejection examples, not a soundness proof. The two fixtures are from the
capacity-training corpus, not held-out cases.

Construction 9.514 s + setup 3.321 s is amortized above. Cold first proof takes
about 14.50 s before input export; native export for the large case previously
took 0.261 s. Warm proof-ready includes batch reading, host reference hashes and
witness generation, but not that exporter. Fixed policy supports both shapes
without rebuilding; it makes small cases pay the large-case capacity cost.

The witness remains at log size 22. Measured on CPU 8 of Ryzen 9 9950X3D, with
no concurrent owned compilation in the tight run. The stock-gadget screen took
1.95/2.93 s while a compiler ran on other cores, so do not attribute the full
timing difference solely to this code change.

Evidence/source: `evidence/hash-template/`. To reproduce, restore the previously
recorded LaBinius private-session patch, copy the bin and its `support/tight_sha.rs`
module into `crates/binius/src/bin`, and build with `RUSTFLAGS='-C target-cpu=native'`.
Exact invocation and source/binary pins are in the logs/audit. Canonical proof
serialization, composed PQ security, receipt binding and recursion remain open.

## Capacity census

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
