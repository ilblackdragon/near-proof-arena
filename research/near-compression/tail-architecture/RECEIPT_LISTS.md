# Ordered source lists and receipt outcomes

2026-10-24. Correctness baseline; **large profile failed before proving**.

The circuit now takes private receipt fields, serializes each from the same
wires used by arithmetic/outcome hashing, concatenates active receipts in order,
adds the shard/count header and constrains the source-list SHA-256 digest.
A public count selects an active prefix and is bounded by fixed capacity.
Inactive receipt encodings have zero effective length and zero public records;
their private gas context is gated to zero. Public context is shared across
active receipts. Balanced pairwise concatenation preserves receipt order.

## Measured results

One fixed **16-slot** circuit (witness log17) proves original lists containing
0, 1, 2, 3, 4 and 9 receipts. Full dense packets are **198,526–200,830 bytes**.
Six warm prepared-fixture runs took **0.256–0.296 s** through packet export;
earlier one/nine-receipt runs took 0.284/0.300 s. These are small-list results.
Circuit construction takes about 0.24 s; setup about 0.106 s. No p95 claim.

All six packets verify in fresh processes in **0.164–0.167 s**, without loading
receipt witnesses, against independently generated expected public bytes.
Backend byte re-encoding matches. Seven public mutations per proof reject;
three checks per fresh verification reject wrong expected root, changed public
root and altered tape. Reversing the original nine-receipt input list while
keeping its expected root rejects at the four source-root assertions.
Independent public-byte audits match all six packets to original list fixtures.

The **1,024-slot** construction failed under a **16 GiB virtual memory limit**:
9,939,772 KiB peak RSS, then a failed 6,509,559,824-byte allocation after 13.88 s.
There is no large circuit/proof/packet from this attempt. Do not extrapolate
small-list latency to the 804-receipt original list. The failed run predates
only the decoder addition; the circuit-building path is unchanged.

## Decision and remaining work

Keep this as the constrained correctness baseline. Investigate cheaper packed
byte concatenation/streaming and measure its scaling before increasing profile
size. A larger memory allowance alone does not establish the 1–2 s goal.
Any replacement must retain shared kernel wires, source length/count/order and
full serialized fields; independently supplied SHA messages are insufficient.

Expected source roots are taken from original exported RC messages, but their
inclusion in the original chunk claim is **not proved**. Account/state reads,
state updates, name grammar, permissions, remaining runtime/hashes, bounded
history recursion and composed PQ security are still open. No new full NEAR
size/latency result exists. The previous 215,398-byte batch excludes source-list
work. This decoder remains restricted to trusted local C exports.

## Reproduction

`make_receipt_lists.py EXPORTS BATCHES OUTPUT --report REPORT` generates all
268 original list fixtures / 2,138 receipt inputs, including empty lists.
`receipt_list_public.py FIXTURE CAPACITY OUTPUT` independently builds the exact
expected public statement. Source and build logs are in `evidence/receipt-lists`;
use the explicit native flags/isolated backend documented in RECEIPT_SOURCE.md.

```
NEAR_EXPORT_DIR=EXPORT_DIR near-receipt-list 16 LIST_FIXTURES...
NEAR_VERIFY_EXPORT=PACKET NEAR_EXPECTED_PUBLIC=PUBLIC near-receipt-list 16
NEAR_GEOMETRY_ONLY=1 near-receipt-list 1024
```

Run with the documented memory cap and one CPU core. Public capacity selects a
fixed circuit; it is not accepted from untrusted packet metadata. Packet framing
counts all public/proof/backend bytes. Measurements exclude original claim
preprocessing and cold construction/setup. Evidence pins source, binary, packet
and public hashes. The manifest retains both successful and failed attempts.
