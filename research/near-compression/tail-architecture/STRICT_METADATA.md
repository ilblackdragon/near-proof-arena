# Correct the hash template's metadata guards

2026-10-24. Correctness repair; earlier packets do not establish the intended
metadata relation. Full NEAR and composed PQ security remain unestablished.

## Bug and repair

The Binius frontend's `assert_false(x)` constrains **only bit 63** of `x`.
Our templates incorrectly used it for whole-word range/zero guards:
`active >> 1`, `flag >> 1`, `id >> 32`, and inactive ID/flag/length fields.
A right shift makes the top bit zero regardless of the remaining bits, so those
range checks were ineffective. The corresponding inactive guards checked only
the top bit rather than the complete selected word.

For example, public metadata `(id=3,length=10,flag=1)` has tag `(3<<32)|21`.
Private `(id=3,length=11,flag=3)` produces the identical XOR-composed tag.
Thus matching the public vector and digest did not establish the claimed private
message length. The honest harness only supplies flags 0/1, so positive proofs
and public-input mutations did not exercise this malformed-witness case.

The corrected template uses `assert_zero` for these six whole-word predicates.
`assert_false(icmp_ugt(length,max))` remains correct: comparisons intentionally
return top-bit booleans. The SHA gadget has only this latter length predicate;
it was checked for the same API misuse. New packets use `NPSTRICT` and the
corrected verifier/circuit; old packets remain historical evidence, not accepted
substitutes. Public record serialization is unchanged.

`near-metadata-guard-check` reproduces four malformed witnesses accepted by the
old predicates and rejected by the corrected predicates: length/flag alias,
ID beyond 32 bits, cancelling inactive length/flag, and non-bit activity.
The last case also changes public activity and is already rejected by canonical
transport; it tests the intended local guard, not a full-packet exploit. Honest
active/inactive inputs pass both circuits. These are constraint-evaluator checks,
not a claim that every case is an end-to-end forgery.

## Corrected packet results

Four warm readiness observations: **0.864 / 0.834 / 0.877 / 0.836 s**.
Large/small packets remain **266,607 / 206,889 B**. Cold circuit/setup adds
4.486 s; peak RSS 2,480,596 KiB. Original witness export remains excluded;
these four observations are not p95. Both serialized packets verify freshly
against the original claims and job roots in ~0.388 s, with public/tape mutations
rejected. Four proving runs pass 24 existing mutations. Independent public-wire
and backend audits pass; minimum backend scalar quantum model cost 139.92 bits,
not a composed PQ security result. The six predicate repairs do not complete a
soundness audit of the whole circuit/protocol.

## Receipt interface audit that exposed the issue

`receipt_interface.py` independently serializes RC/PEO/LEAF/RID records from native
receipt views, recomputes refund IDs and outcome digests, and checks deposit,
storage coverage, gas burn/surplus, previous-receiver ordering and arithmetic
bounds. It matches all 4,602 producer jobs / 540,197 bytes across 64 cases and
2,138 receipts. All 384 receipt-view mutations reject. This is a host oracle for
future circuit compilation, **not** a proof of valid execution or byte equality.
Routing, authenticated state/access-key reads and complete receipt semantics are
not covered by this oracle.

Coverage gap: all real cases have block gas price zero, with 2,080 system and 58
regular receipts; none burns tokens. Seven valid and six invalid synthetic
arithmetic cases cover positive gas prices, overflow, maximum balance and storage
thresholds. They are not accepted NEAR claim fixtures. We need representative
positive-gas execution cases before claiming broad semantic coverage.

## Remaining gates

Compile execution-emitted bytes and hash inputs into one authenticated relation,
then bind receipt sourcing, state, Wasm/runtime and history. Audit all constraints
against their actual API semantics; host-valid inputs are not adversarial witness
coverage. Composed PQ security and representative end-to-end latency remain open.

Evidence: [strict-metadata](evidence/strict-metadata) and
[receipt-interface](evidence/receipt-interface). Build the preserved
`near-hash-strict` / `near-metadata-guard-check` sources on the preceding isolated
stronger backend. Use original claims and job roots with the strict packets.
