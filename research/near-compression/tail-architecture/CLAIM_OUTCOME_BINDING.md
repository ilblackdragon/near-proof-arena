# Bind reconstructed outcomes to the caller's chunk claim

2026-10-24. A necessary application link, not complete NEAR validity.

The native leaf verifier now additionally reads the caller-supplied original
`claim.bin` and checks that its chunk-inner `prev_outcome_root` equals the outcome
tree derived from authenticated PEO digests and public receipt IDs. Empty trees
use 32 zero bytes; odd nodes promote unchanged. The same independently expected
complete job root remains required. No proof bytes change: this verifies the
existing 266,607 / 206,889-byte packets under an additional public predicate.

The field extractor checks claim/statement tags, protocol version 86, bounded
lengths and the V4/V5 chunk-header prefix. It deliberately does **not** decode or
validate the entire claim, chunk header, block signatures, layout or history.
The caller supplies the expected statement; a proof-supplied claim is not trusted
as the user's intended statement. All omitted claim predicates remain required
in the final protocol. This is a partial statement checker, not a general NEAR
claim acceptance API. The native backend decoder remains trusted-local only.

Independent Python reconstruction checks all 64 original claims against the SHA
source messages. The native checker consumes independently generated non-leaf
wire fixtures. Mutation tests alter the expected outcome, claim tags, protocol,
truncation and receipt IDs. A separate scope test alters `prev_state_root` while
leaving outcomes unchanged: this partial check still accepts. That records a
missing obligation explicitly rather than treating success as full validity.
Fresh proof verification uses no private witness and requires `NEAR_CLAIM` in
addition to `NEAR_VERIFY_EXPORT` and `NEAR_EXPECTED_ROOT`.

Native checks pass **64 cases / 304 rejected mutations**; all 64 unrelated-state
mutations pass this partial relation, as expected. Both original packets verify
in fresh processes (~0.387 s proof verification; 0.0004–0.0018 s decode/link check).
Substituting the small claim for the large packet is rejected by the integrated
verifier with `claim outcome root mismatch`.

## What remains between this component and execution

The existing `collect.rs::rcpt_raw` emits each receipt-list serialization into
`RC(j)`, each outcome serialization into `PEO(i)`, and refund-ID preimages into
`RID(i)`. Its `PEO(i)` digest consumption supplies the receipt's `peoh` field.
Our proof authenticates those SHA outputs, but does not yet prove that their
private bytes are the bytes emitted by a valid receipt execution. The public
receipt ID also needs equality with the ID in that execution and input list.
`srcp_raw` links the receipt-list digest to the claimed source tree; this path
and deduplication are still outside our new component.

A next integration must preserve all of these links:

1. Authenticate source receipt-list membership and canonical ordering/dedup.
2. Match the receipt ID and exact emitted RC/PEO/RID bytes to hash inputs.
3. Prove receipt execution, account/access-key reads and state writes, including
   refund arithmetic and scheduler context.
4. Bind pre/post state roots and all other statement fields, then enforce bounded
   PQ recursive predecessor/history composition.

Proving equality only between already-computed host digests does not establish
item 2. Hash inputs are private circuit witnesses; an independent receipt proof
needs a shared authenticated byte interface or both relations must be constrained
in one proof. A host-side equality audit is useful evidence for implementing that
interface, not a substitute for it. Full Wasm/runtime coverage and composed
security/representative end-to-end latency remain required as well.

## Evidence and reproduction

[evidence/claim-outcome](evidence/claim-outcome) contains the corpus audit, native
checks, fresh-verifier logs and preserved source. `audit_claim_outcome.py CLAIMS
MESSAGES --output REPORT` reproduces the independent field/root comparison.
Build `near-claim-outcome-check` and run it with the original D0a claim directory
and `leaf-wire-fixtures` directory. Build `near-hash-claim-outcome` on the preceding
stronger-policy source and verify the existing non-leaf packets with their
original job roots and original claims. No new proving-time claim is made; the
underlying four warm observations remain those in NATIVE_RECEIPT_LEAVES.md.
