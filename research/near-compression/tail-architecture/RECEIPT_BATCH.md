# Private receipt batches with constrained outcome hashes

2026-10-24. Receipt arithmetic/outcome component; **not full NEAR or PQ128**.

A fixed batch circuit now consumes receipt fields and account amounts as private
witnesses, shares a declared block gas price/height across active receipts, and
publishes receipt indices, IDs, outcome lengths and digests. Those digests come
from constrained arithmetic and serialization, not a free SHA message witness.
The native verifier reconstructs the outcome tree and compares its root with the
externally expected root. For real fixtures that root is extracted from the
original chunk claim. The declared context is separately supplied by the caller;
its derivation from the full claim is not proved by this component.

Private witness placement does not establish zero knowledge. Account/state and
receipt sourcing remain unauthenticated. A prover can choose otherwise plausible
balances and receipt fields without showing they came from the actual state or
incoming lists; this relation alone is not valid execution. This kernel only covers the described
D0a transfer arithmetic/success outcome, not general actions, account-name grammar,
access-key permissions, routing, source membership, arbitrary Wasm or history.

## Uniform profile — current candidate

Every one of **1,024 slots** supports either refund branch and receiver lengths
1–64. It does not assume the corpus's small refund count. Each slot uses the
previously checked generic receipt kernel. Inactive slots have canonical zero
public records and valid dummy private data. Their private gas context is gated
to zero, so inactive refund work does not constrain the real block gas price.

| Workload | Active receipts | Actual packet | Warm readiness |
|---|---:|---:|---:|
| Original 00-h10035-s3 | 814 | **215,398 B** | **1.542 / 1.521 s** |
| Original 00-h10012-s1 | 1 | **158,488 B** | **1.506 / 1.519 s** |
| Synthetic positive context | 4 | 158,698 B | 1.566 s |
| Synthetic maximum gas-price context | 1 | 158,488 B | 1.538 s |
| Synthetic 1,024 repeated long refunds | 1,024 | 230,098 B | 1.555 s |
| Synthetic 1,024 varied long refunds | 1,024 | **230,098 B** | **1.560 s** |

One stress case repeats a synthetic local-kernel receipt; a second uses 1,024
distinct IDs/receivers and varied balances, storage usage and gas prices. Both
are capacity/arithmetic tests, **not valid NEAR source lists or chunks**.
Likewise, positive-gas synthetic fixtures do not replace representative accepted
positive-gas NEAR claims. The real 64-case corpus still has zero block gas prices.

Readiness includes prepared batch reading, witness filling, proving and packet
export. Original claim/witness preprocessing is excluded. One CPU core, no GPU;
these few observations are not p95 or a full chunk deadline. Cold circuit/setup
adds 6.407 s, including a separate public-setup construction to derive codec
shapes. Peak RSS 4,277,948 KiB; virtual memory capped at 16 GiB.

This is a different workload from the earlier 266,607-byte SHA-r component:
**the remaining SHA jobs are absent here**. Their costs cannot be assumed covered
by this result. A single integrated proof must include them and their byte links;
concatenating component packets does not meet the target.

## Typed profile comparison and transport

The first profile reserved `[1024,8,8,8]` slots for no-refund receiver<=18,
no-refund receiver19–64, refund receiver<=50, and refund receiver51–64.
Each class predicate is enforced in its circuit. It matches the corpus but allows
only eight receipts in each rarer class, so it is not the general candidate.

Dense typed transport was **301,310 B**, over 300,000. Canonical active-only
transport reduced it to 266,078 B large / 209,168 B small. Four real warm samples
were 1.093/1.042/1.049/1.042 s; earlier dense samples were
1.042/0.989/0.979/0.991 s. Preserve both runs; no exclusive-host or p95 claim.
The uniform circuit is slower but its different backend geometry makes its
serialized proof smaller. No security level was lowered for that comparison.
This last statement describes parameter policy, not a composed security proof.

Typed packets use `NPRCBP02` with public section `NPRCBW01`; uniform packets use
`NPRCBU01` with public section `NPRCBWU1`. The public section is:

    magic8 || block_gas_price_u128_le || height_u64_le || count_u32_le
           || (class_u8, outcome_length_u8, index_u32_le, receipt_id32, digest32)*

Digests use canonical byte order. Rows are sorted by class/index; duplicates,
wrong lengths, over-capacity, trailing bytes and nonzero inactive public rows
reject. Expansion restores the exact dense proof input: 92,248 B typed or
90,136 B uniform. Both include canonical zero padding. Uniform class is always 0.
The remaining six packet sections carry tape, claimed value, left/opening RNS
commitments, norms and backend. All framing/public/proof bytes are counted.

## Validation and security scope

All four typed local circuits match the 2,305-case oracle, reject wrong-class
assignments and 27,216 output/length mutations, and each produces a verified
in-memory proof. Independently generated public fixtures match all 64 original
outcome roots plus two synthetic contexts; each codec passes 762 mutations.
The uniform full-capacity stress is additionally checked by proving and byte
verification. Six typed and eight uniform proof runs pass seven public/tape
mutations each. Fresh verification consumes packets and expected public context/
root only; no receipt witness is loaded. All six uniform packets verify freshly
in 0.710–0.734 s; the four typed packets verify in 0.609–0.620 s. Substituting the
wrong expected root or gas context rejects before proof acceptance. Exact logs
are in the evidence directory.

Five modulus limbs, stronger bridge/backend policy and corrected whole-word
metadata guards remain. Uniform geometry is witness log 21, left rank 5, opening
rank 11, 36 norms, binary vector rank 3,072. The typed geometry uses log 20,
left rank 4 and binary rank 1,536. These shapes are derived from fixed public
setup, not supplied proof metadata. Independent backend scalar screens pass;
uniform minimum modeled quantum cost is 144.955 bits. Structured/CRT attacks,
outer extraction, short challenges, QROM and complete composition remain open:
**these numbers are not a PQ128 result**. The C decoder is still trusted-local.

## Next required integration

1. Bind the same receipt fields to the serialized source receipt lists and prove
   their membership/dedup/order. The RC/other SHA jobs are not in this packet.
2. Feed these same computed after-balances into authenticated state updates;
   prove account/access-key reads, scheduling/context and all missing semantics.
3. Integrate the remaining relations into one proof and remeasure. Extend coverage
   beyond D0a transfers, establish bounded PQ history composition and audit the
   complete security argument and untrusted decoder.

No full NEAR/PQ/recursion or end-to-end deadline gate is complete.

## Reproduction

[evidence/receipt-batch](evidence/receipt-batch) preserves final and failed-dense
source, logs, hashes, independent public audits and backend screens. Build
`near-receipt-batch-unified` plus support modules on the preceding isolated
stronger-policy backend. The typed version is `near-receipt-batch`.
Generate original batches with `make_receipt_batches.py`; add synthetic contexts
and uniform fixtures with `make_receipt_batch_extras.py`. `receipt_batch_public.py`
and `audit_receipt_batch.py` independently reconstruct/check public vectors.

Fresh verification requires `NEAR_VERIFY_EXPORT`, `NEAR_EXPECTED_CONTEXT` and
`NEAR_OUTCOME_ROOT`; the circuit/setup policy is fixed by the binary. Proof mode
accepts batch paths and writes packets under `NEAR_EXPORT_DIR`.

## Source-binding audit checkpoint

`audit_receipt_source.py` independently parses the original RC SHA messages
and compares predecessor, receiver, receipt ID, gas price and deposit to the
exact batch kernel input bytes. All 64 cases / 2,138 receipts match; 10,690
single-field mutations reject. This is **host conformance, not proof binding**.
The compact report is `evidence/receipt-source-audit.json`; reproduction also
emits every source field's byte interval for shared-wire circuit construction.

The 814-receipt case has three source lists of 151, 1,263 and 111,780 bytes:
**1,770 additional SHA-256 compressions** including padding. These are absent
from the current uniform packet. Source signer/key fields and list shard/count/
ordering must be constrained too. Before/locked balances and storage are not
receipt-source fields and require separate authenticated state reads; block gas
price and height need authenticated context. Matching these host fixtures does
not discharge any of those proof obligations.
