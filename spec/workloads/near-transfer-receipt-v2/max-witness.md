# Workload class `max-witness` (candidate, not governed)

Purpose: an adversarial worst-case prover input, the maximal in-domain witness
of this statement, so that a later challenge revision can include it as a
class. It is **not** part of any governed challenge: the v2 draft's
`workload_suite` does not reference it (no weight, no held-out set); adding it
is a governance decision. Generator spec:
`spec/workloads/near-transfer-receipt-v2/max-witness.json`, i.e.
`near-arena-oracle gen --scope v2 --receipts 256 --profiles max_witness
--fixtures-layout` (the profile also works under `--scope v1`; it is never in
the default profile list). Source: `oracle/src/maxwit.rs`, a port of the
candidate-side `npudr gen-max --eps 0` onto real state: the oracle, not the
candidate, is the source of truth.

Shape, deterministic from `(seed, index)`: 256 receipts to distinct
64-character named receivers (130-nibble keys) with pairwise distinct
2-character prefixes. For every private nibble depth `d ≥ 4` of a receiver's
key there is one untouched sibling account that leaves the path exactly at `d`,
so each of the ~124 private nodes per path is a 2-child branch (75 bytes, 2
SHA-256 blocks) and the account leaf has an empty key; no extension compresses
a path, and siblings are never revealed (hash stubs). The remaining budget goes
to further siblings, pairs on odd-depth branches first (a 4-child branch is 139
bytes, 3 SHA blocks), calibrated against nearcore's own `TrieRecorder` so that
the slice witness (incl. the `0x0f` path) is `3 000 000 − r` bytes,
`0 ≤ r < 32`. Every receipt refunds (receipt gas price > block gas price
`10^8`); predecessors and signers are 64-character ids with SECP256K1 keys.
Empty-key extensions (the default `npudr gen-max` fill) cannot occur in a
nearcore trie and are not used.

Sizes (seed 42, v2): slice witness 2 999 973 revealed bytes in 32 402 values
(`witness.bin` 3 129 643 B), `request.bin` 89 037 B (limit 131 072), pre-state
49 921 entries (`state.bin` 5.5 MB); the full `Runtime::apply` recorded storage
is the same 2 999 973 B (< `main_storage_proof_size_soft_limit` 4 000 000:
nothing delayed). Generation takes ~1 s per case. Every case goes through
`Runtime::apply` and the domain check, like any other class.
