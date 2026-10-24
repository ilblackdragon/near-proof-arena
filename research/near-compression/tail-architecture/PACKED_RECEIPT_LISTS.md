# Packed source-list and outcome proof

2026-10-24. **804 original receipts: 244,838 bytes / 4.543 s warm readiness.**
This fits the packet-size target but misses the 1–2 s deadline. It is one
source-list/outcome relation, **not full NEAR validity or PQ128 recursion**.

## Change and soundness obligations

`packed_concat.rs` replaces generic hinted concatenation/slicing with direct
word operations. It constrains each input length to its declared range, clears
bytes beyond that length, shifts the right operand by the left length, and XORs
the disjoint byte regions. Pairwise joins preserve zero suffixes. Length sums
are bounded by fixed capacities well below u64 overflow. Variable byte shifts
use bounded low-three-bit shifts; whole-word shifts cover the constrained range.
There is no random fingerprint or independently supplied hash-message witness.

The first packed-list attempt still exceeded the memory cap because outer
assembly cleared suffixes again at every tree level. The final version passes
all receipt vectors to one balanced packed concatenation, avoiding that repeated
work. The initial failed source/log remains under `failed-reclean` / evidence.

## Validation

- Short concat oracle: 625 length pairs, 4,378 rejected mutations including
  invalid full-word lengths, with nonzero bytes beyond declared lengths.
- Wider 129/513-byte capacities: 410 boundary pairs and 41,684 rejected output
  mutations, covering byte and multi-bit word-shift boundaries.
- Existing shared source/outcome oracle: 2,158 accepted / 12 rejected fixtures,
  56,108 rejected mutations; three in-memory proofs / 12 public mutations.
  Its witness log falls from 13 to 12.
- Six original 0/1/2/3/4/9-receipt lists prove in the 16-slot profile and verify
  freshly. Packets are 198,462 bytes; warm samples 0.271–0.283 s. This is not a
  demonstrated timing improvement over the old 0.256–0.296 s range.
- Reversing the original nine-receipt list rejects at the source-root assertions.
- Independent public-byte reconstruction matches all seven exported packets.

## Large original list

The fixed **1,024-slot** profile now constructs successfully under the same
16 GiB virtual memory cap. Witness log is **23**. The measured original list is
`00-h10035-s3-list2`: 804 receipts, 803 system, one refund, block gas price zero.
The circuit supports both refund branches and both key sizes; this corpus run
is not evidence of representative positive-gas performance or full semantics.

| Measurement | Observed |
|---|---:|
| Complete diagnostic packet | 244,838 B |
| Prepared-fixture read/fill | 0.063 s |
| Prover | 4.480 s |
| Read/fill/prove/export | 4.543 s |
| In-process verification | 1.531 s |
| Fresh decode + verification | 1.549 s |
| Cold circuit construction | 20.710 s |
| Cold setup, including duplicate public setup | 4.060 s |
| Whole proving/checking process peak RSS | 14,256,456 KiB |

One CPU core, no GPU; one large warm sample, not p95. Original witness/claim
preprocessing and cold setup are excluded from warm readiness. The earlier
geometry-only final run peaked at 11,270,132 KiB. The initial repeatedly-cleared
packed version failed; these are distinct attempts, not a retry attributed to
host availability.

The exported NPLIST02 packet verifies in a separate process without receipt
witnesses, with byte-identical backend re-encoding. Seven prover/public checks
and three fresh checks reject changed statements/tape. Expected public bytes are
independently generated from the original list fixtures; setup ranks come from
the fixed circuit's public parameters, not packet metadata.

## Remaining gates and next experiment

The expected source digest is not yet proved included in the chunk claim.
Before/locked balances, storage and context are unauthenticated. Other ten
receipts in the original chunk's other lists, complete outcome-root linkage,
remaining hashes/actions/state/Wasm semantics and bounded PQ history remain
outside this proof. Composed PQ128 and safe untrusted decoding are unestablished.
No full-target completion follows from the size result.

Next distinguish source packing cost from worst-case hash padding. The current
profile allocates source hashing for 12 + 347*1024 bytes, although this original
list is 111,780 bytes. A separately declared, circuit-enforced source-byte budget
could reduce SHA work without restricting key/name/refund shapes per receipt.
Such a profile must reject oversized sources, preserve a larger-capacity path,
and count every public selector/setup obligation. Measure it rather than assume
that fewer hash blocks meet the deadline. Source/state/recursion integration
remains required regardless of the next local timing.

## Reproduction

Use the existing `make_receipt_lists.py` and `receipt_list_public.py` fixtures.
Final source and logs: `evidence/packed-receipt-lists`. Build the three packed
binaries plus `near-packed-concat-wide` with explicit native RUSTFLAGS and the
isolated stronger-policy backend documented in RECEIPT_SOURCE.md.

```
NEAR_EXPORT_DIR=EXPORT_DIR near-receipt-list-packed 1024 ORIGINAL_LIST
NEAR_VERIFY_EXPORT=PACKET NEAR_EXPECTED_PUBLIC=PUBLIC near-receipt-list-packed 1024
```

Cap memory at 16 GiB and pin CPU 8 as in recorded runs. Small and large profiles
have different fixed circuits. The C decoder accepts trusted local exports only.
