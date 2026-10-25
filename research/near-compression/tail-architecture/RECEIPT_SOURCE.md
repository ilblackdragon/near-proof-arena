# Shared source serialization and outcome kernel

2026-10-24. A local relation, not full NEAR or a new end-to-end size/latency result.

`receipt_source.rs` serializes a D0a transfer from the **same wires** used by the
arithmetic/outcome kernel: predecessor, receiver, receipt ID, gas price and
deposit. Additional wires provide signer, key kind and key bytes. The circuit
bounds lengths, constrains the whole key-kind word to 0/1, emits fixed action
receipt/transfer structure, prepends a singleton list's shard/count, and hashes
the resulting bytes. Public outputs include after/burn/refund amounts, outcome
digest and source-list digest. Source bytes are derived through constrained
concatenation, not supplied as an independent message witness.

## Evidence

- 2,138 original receipt inputs plus 20 synthetic length/key/gas boundary cases
  accepted; 12 invalid full-word length/key metadata cases rejected.
- 56,108 input/output mutations rejected during circuit evaluation.
- Three in-memory proofs verified; all 12 public-input mutations rejected.
- 47 singleton list fixtures exactly match original RC hash messages. Other
  corpus receipts are wrapped in synthetic singleton lists, not claimed to be
  original source lists. Synthetic cases are not valid NEAR claims.
- Witness log 13, compared with log 11 for the previous local outcome kernel.
  This growth motivates measuring/optimizing concatenation before full-batch
  integration. No batch timing or packet-size claim follows from this test.

The harness exposes inputs publicly for conformance testing. No source packet
codec, fresh-process verification, multi-receipt list proof, source-root
membership, state authentication, general runtime or PQ history is established.
The older uniform packet still excludes this relation and its cost.

## Next integration

Build one list digest from multiple serialized receipts while preserving original
order and list boundaries. The packed-list commitment must bind exactly the
same kernel fields; independent host equality checks are insufficient. Account
balances/storage require state proofs; context and source roots must be tied to
the expected claim. Measure combined circuit size and warm latency before
choosing a batch layout. The generic concat path may be too expensive.

## Reproduce

Generate fixtures with `make_receipt_sources.py EXPORTS BATCHES OUTPUT --report REPORT`.
Copy `evidence/receipt-source/source` into the isolated LaBinius bin directory.
Use the pinned dependencies and stronger-policy backend from prior checkpoints:

```
RUSTFLAGS='-C target-cpu=native -C link-arg=-fuse-ld=mold' \
CARGO_TARGET_DIR=/data/illia/pq-tail-architecture-20261024/target \
LABINIUS_LABRADOR_DIR=/data/illia/pq-tail-architecture-20261024/labrador-sis128 \
cargo build --release -j4 -p labinius-binius --bin near-receipt-source-check

taskset -c 8 /data/illia/pq-tail-architecture-20261024/target/release/near-receipt-source-check RECEIPT_SOURCE_BIN
```

Logs, source/binary hashes and fixture report: `evidence/receipt-source/`.
Global Cargo target configuration overrides project native flags unless
`RUSTFLAGS` is explicit; the initial build without that override failed AVX-512
compilation. The successful build used the isolated stronger-policy C backend.
