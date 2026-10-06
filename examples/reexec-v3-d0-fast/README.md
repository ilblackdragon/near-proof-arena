# reexec-v3-d0-fast: PROVER-ONLY child of reexec-v3-d0

Same verifier, formal tree, encodings and public parameters as `examples/reexec-v3-d0`
(`formal/` is identical; the judge-built `verify` is the same binary,
`sha256:19ee48ed…`), so the judge classifies it `PROVER_ONLY` and reuses the parent's
formal gate results. Only the prover differs.

## Prover

`source/src/bin/prove.rs` (Rust, std only, its own SHA-256) re-implements the parent's
Lean prover natively: `proof.bin` = the witness file whose state witness is
`ReexecV3D0.normSW K R sw` (`formal/ReexecV3D0/NormBytesDefs.lean`) — ignored header
fields and transition block hashes zeroed, receipt-proof entries deduplicated (last
wins) and sorted by key, every `base_state` cut to the relation's read set (`qFor`)
deduplicated and sorted — with `R` (main pre-state root: the shard's slot in the last
new-chunk block of the claim's segment) and `K` (`mainKeys` of the entries' receipts and
the `BufferedReceiptIndices` shards found in the partial main trie) as `keysD0` computes
them on accepted witnesses. It skips `keysD0`'s checks (block hashes, chunk-header roots,
merkle paths, …): nothing here is trusted, because the verifier accepts a proof only if
its state witness is a byte-exact fixed point of `normSW` and `RelD0` holds.

## Gate: byte match with the Lean prover

`source/tests/byte_match.rs` runs `prove` on every public positive case of
`oracle/fixtures/v3/arena-public` and requires the sha256 of each proof to equal the
parent Lean prover's (`source/tests/lean-prover.sha256`, 78 cases; the test also checks
the manifest covers exactly the positive set). `tools/byte-match.sh` runs it (heavy
wrapper, CPUs 8-15,24-31); `tools/byte-match.sh --regen` rebuilds the parent with its own
build recipe from git HEAD, regenerates the manifest from its Lean prover and re-runs the
test.

Results (2026-10-06): 78/78 positives byte-identical to the Lean prover; on the 121
public rejection cases the native prover refuses 58 and the verifier rejects the other 63
(0 accepted; the Lean prover refuses 84, since it runs `keysD0`'s checks). Time: ~1.7 ms
per case including process start (Lean prover: 0.02–0.64 s).
