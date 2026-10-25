# zkVM near-chunk guest: pinned workload definition

2026-10-25. This pins exactly what the benchmark guest executes, so the
zkVM measurement is apples-to-apples with the custom circuit's proven
semantics slice (NPMULT03, commit 669eb99c0) and no stronger.

## Inputs (embedded via include_bytes; no runtime input plumbing)

1. Real corpus: `00-h10035-s3` — 814 receipts in 3 ordered lists, 10
   accounts, NPMTRIE01 witness (chain depth 6), claim-derived
   prev_state_root, NPMLEDG01 account table (initial/final values).
2. Synthetic variable-depth: six NPMTRIE02 families (depths 5, 7, [9,9,7],
   13, 15, and mixed16 with chain lengths 11..15 within one trie) —
   native-constructed PTries, host-verified (audit_synthetic_tries.py).

## Guest semantics (== the custom circuit's slice)

For each account (real + synthetic):
- key = nibbles(0x00 || name) — derived IN-GUEST from the row name;
- walk the provided node chain: every branch consumes exactly one key
  nibble; ext/leaf hexPrefix fragments decode and must equal the key
  nibbles at the current position; SHA-256 rehash each node's node_ser,
  child links must match the recomputed hashes, top hash must equal the
  fixture root (real: the claim-derived prev_state_root);
- leaf value_ref must equal u32le(72) || SHA-256(initial 72-byte value).

Ledger (real corpus only):
- u128 running-balance registers per account, threaded across ALL receipts
  in application order (list order, slot order), before == register on every
  matched receipt, register += deposit, final == table final balances;
- ordered receipt source hashing (SHA-256 over the serialized source) per
  list and the ordered outcome root over all receipts.

Outputs (public IO): final balances per account (or their SHA-256), the
ordered outcome root, the trie root(s). The host checks these against
independently computed expected values (audit_account_ledger.py +
audit_synthetic_tries.py reference outputs) — NO mismatch tolerated.

## Explicitly NOT in the guest (same as the circuit)

Access keys, routing/domain predicates, general actions/Wasm, scheduling,
post-state root, receipts beyond the D0a transfer slice. The corpus is
transfer-only; Wasm is the known coverage gap and is stated in the verdict,
not measured here.

## Measurement protocol

CI-profile binaries (Jolt 7931b223 + Akita dfdbd767; no LTO; 16 GiB cap);
/usr/bin/time -v; pinned CPU 8-11 for proving (4 threads), CPU8 RAYON=1
for serial verify; two observations max; extrapolations labeled with the
measured cycles/hash; no parameter changes to Jolt/Akita.
