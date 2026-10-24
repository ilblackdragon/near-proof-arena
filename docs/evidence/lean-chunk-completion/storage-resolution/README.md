# Recorder and code-resolution checkpoint

`combined-1788` and `l4-388` contain strict successor replay reports and result rows. They bind the
exact executable, inputs, output and comparison sources. They are verdict/domain evidence, not full
computed-observable parity or independent boundary-fixture generation.

`cases/` contains four recorded nearcore ETH-local chunks. The earlier runtimeLimits tier excludes
them; storageResolution accepts them. Their original metadata and bytes are retained.

Native boundary/rollback cases are in `TestStorageResolution.lean`; their two small source contracts
and compiled bytes are in `tools/d3/storage-fixtures`. Rebuild with `wasm-tools parse INPUT.wat -o
OUTPUT.wasm`. These tests use locally specified expected protocol behavior, not new nearcore results.
See the [handoff](../../../logs/lean-chunk-storage-resolution-2026-10-24.md) for scope and remaining work.
