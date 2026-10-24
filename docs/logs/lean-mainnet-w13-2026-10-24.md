# W13 implementation checkpoint — 2026-10-24

Implemented an explicit `make w13-gate`, capture/import/packaging CLI, mismatch and coverage
reporting, immutable input/artifact checks, and 18 fail-closed harness tests. Existing CI discovers
the tests through `oracle/tools/test_*.py`. Public mainnet capture of three blocks yielded 30 chunks;
without witnesses the gate correctly fails, reporting mismatch N/A and replay coverage 0%.

The gate checks claim-to-mainnet chunk hash and epoch binding, captured segment hashes, and requires
a pinned native adapter to verify trusted chain facts and run actual stateless validation before
Lean. Lean acceptance checks recomputed validator commitments. It does not merely compare metadata
or emitted copies of expected fields. Reports retain exclusions, errors and incomplete populations.

W13 is **not complete**: a mainnet database/export and the actual native database-to-claim/validation
adapter are still required. No mainnet chunk has executed successfully in this checkpoint. The
current implementation is the test gate and acquisition interface, not a turnkey archive exporter.

FastNear's published API docs do not identify a state-witness download endpoint. The user has API
access; endpoint/product and local credential location were requested. Bearer credentials can be
passed by environment-variable name without writing them into artifacts. Cross-origin redirects
strip authorization. A private export endpoint remains a possible acquisition route.

Pinned nearcore has a `shadow_chunk_validation` build feature to generate witnesses on a stateful
node, plus `save_latest_witnesses` and the state-viewer dump command. A regular non-validator peer
cannot be assumed to receive every shard's validator witnesses. The retained-witness store is capped
at 1,800 entries / 4 GB; an all-shard 1000-block run needs continuous export. The shadow source also
notes a resharding limitation. Only 7 GB was free on `/data` during initial inspection; no node was
started. Disk cleanup is being handled separately at the user's request.

Evidence: [live probe](../evidence/lean-chunk-completion/mainnet-w13-probe/README.md).
Usage and exact gate contract: [mainnet replay README](../../tools/mainnet-replay/README.md).
No changes to Lean execution, signed oracle pins, or other lanes' uncommitted work were made here.
