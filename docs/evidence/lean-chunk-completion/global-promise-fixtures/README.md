# Whole-chunk global promise hosts

`all-hosts-valid-receivers.wat` derives from the cache-closure lane's
`all-hosts.wat`. It executes all seven global/state-init promise hosts, creates
two receipts with transfer before state-init, and asserts both returned action
ordinals are 1. State-init map entries are deliberately inserted unsorted.

The only functional change is replacing `alice`/`bob` with the actual deterministic
account IDs at memory offsets 256/384 (length 42). `receiver-derivation.json`
contains native pinned-nearcore `codec-roundtrip state-init HEX` results for both
final maps. The original receiver names fail generated-receipt validation.

Compile with `wat2wasm all-hosts-valid-receivers.wat -o all-hosts-valid-receivers.wasm`.
The checked-in wasm is 940 bytes. Code and data offsets are otherwise unchanged.

Generate whole chunks with the v3-successor oracle (pinned nearcore commit
44f7ae6cd7ef08bab604e20a473bf77e35d4c993):

```sh
NEAR_SUCCESSOR_GAS_TGAS=300 \
NEAR_SUCCESSOR_CONTRACT="$PWD/tools/d3/global-promise-fixtures/all-hosts-valid-receivers.wasm" \
/path/to/near-arena-oracle-v3-successor gen --domain d3 --seed 1618 \
  --chains 1 --blocks 60 --mutate-every 0 --code-mutant-p 0 --ood-cap 2000 \
  --out /tmp/lean-global-promises-full-1618
```

This yields 211 honest chunks, all accepted by independent cold nearcore replay.
The first caller case (`ood/00-h10004-s3`) succeeds and emits both receipts.
The next chunk executes those receipts and fails at the initial transfer because
the target accounts do not exist. This tests host emission and authenticated
whole-chunk results, not successful target initialization.

Repeating with gas 20 yields 210 accepted honest chunks; the same first caller
fails with GasExceeded. This is a useful failure control, not a successful
all-hosts run. `runtime-fees-86.json` is emitted by
`codec-roundtrip runtime-fees` using the actual runtime configuration, including
7.43 Tgas state-init execution per action. Distribution's separate 20 Tgas base
is not the deploy-global promise-host action fee. Compare both cases when
checking gas reservation and rollback; do not infer host fee correctness from
only the 300 Tgas success.

Three compact cases and hashes are committed under
`docs/evidence/lean-chunk-completion/global-promise-fixtures/`. Their native
expected acceptance includes ordinary failed actions; Lean replay is a separate
validation step. These opt-in generator controls do not change signed D3 sources.

Integrated Lean replay: 83 target/child cases from both windows accepted on each
of `globalActions` and `completeCodeGlobal` (166/166 checks). This includes the
clean 300 Tgas success and 20 Tgas GasExceeded control against the same wasm,
so both host emission and gas-failure behavior match independent chunk headers.
See `lean-replay.json` in the evidence directory for exact runner hash/results.
