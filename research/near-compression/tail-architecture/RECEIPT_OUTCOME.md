# Constrained arithmetic feeds the outcome hash

2026-10-24. Implemented local kernel, not a complete receipt/NEAR proof.

The circuit derives system-receipt status from predecessor length/bytes, computes
credit, storage coverage, burnt tokens and surplus through the checked arithmetic
kernel, and serializes the partial outcome using those exact computed wires.
The refund flag comes from nonzero computed surplus. If present, its refund ID is
SHA256(receipt ID || height_u64_le || zero8). The partial outcome contains the
fixed gas constant, computed burnt amount, receiver length/bytes and fixed success
status. SHA256 consumes this derived byte vector directly. No separately supplied
burnt amount or pre-encoded outcome witness can bypass those equalities.

The generic kernel supports receiver lengths 1–64 and both refund branches.
It computes a refund-ID hash plus up to three partial-outcome SHA compressions.
Unused encoded bytes are zeroed/ignored consistently with the constrained length.
This is the necessary local arithmetic-to-byte-to-hash connection; account-name
grammar, source receipt membership and state authentication are not implemented.
The arithmetic's u128 storage input also needs the actual account schema's bounds
when connected to state decoding. The hard-coded success outcome applies to this
D0a transfer kernel, not arbitrary actions or Wasm execution.

## Evidence

Independent Python expectations cover **2,305 unique cases**: all 2,138 real
receipt views, 160 synthetic length/gas/system-prefix cases, five invalid
arithmetic cases and two invalid lengths. The circuit accepts 2,268, rejects 37,
and rejects **27,216** output-limb/length mutations. There are 90 positive-burn
cases; these are synthetic, not accepted NEAR claim fixtures.

The combined circuit packs to witness log **11**, sufficient for the PCS (the
isolated arithmetic kernel's log 7 was too small). Three in-memory proofs verify
for representative system, positive-burn and maximum-length inputs. A focused
repeat adds two proofs for positive-burn refunds at short/maximum receiver lengths
and 24 mutation checks. All **five proofs** verify; changing an input, burnt value
or digest rejects in each (15 verifier mutations).

The harness exposes kernel inputs and outputs publicly to test the exact relation.
This is not a privacy claim or an authenticated connection to the batch/state
proof. No fresh-process serialization, batch size/latency result or PQ128 claim
is made for this tiny geometry. Existing NPSTRICT size/speed measurements remain
for the preceding hash component only. Inputs still need to originate from the
same authenticated receipt/state execution, and the local outputs must be linked
to the batch's public record vector.

## Next batch integration

Avoid expanding every receipt to the maximum encoding. Without a refund, the PEO
has `37 + receiver_length` bytes: <=18 bytes of receiver fit one SHA compression;
longer receivers fit two. With a refund it has `69 + receiver_length` bytes:
receivers <=50 fit two compressions, longer ones require three. These boundaries
include SHA padding. Typed capacity groups must constrain their own predicates,
not trust a host-assigned class.

The 64-case census sees maxima of 813 short non-refund receipts and six refund
receipts with receiver length <=50. It sees neither longer class. They are valid
kernel classes and cannot be silently excluded from a general NEAR claim. A batch
profile must state capacities and be checked on independent data.

Receipt IDs already appear in the public outcome-tree interface. Refund-ID hashing
could move to native verification too, but only after the proof binds the same
receipt ID, height and refund predicate. This reduction is not implemented. First
integrate the typed kernel with the batch's canonical job metadata/digests; then
bind source serialization, account/state inputs, execution ordering and history.

## Reproduction

[evidence/receipt-outcome](evidence/receipt-outcome) includes compiled source,
logs, vector/source/binary hashes and capacity census. Build
`near-receipt-outcome-check` with the preserved `receipt_arithmetic`,
`receipt_outcome` and `tight_sha` support modules on the prior stronger-policy
backend. Generate expectations with `make_receipt_outcomes.py RECEIPT_EXPORTS
OUTPUT --report REPORT`, then pass OUTPUT to the checker. The focused refund
file contains original records 2144 and 2288, with the same header and count 2.
`census_receipt_classes.py` reproduces the capacity report.
