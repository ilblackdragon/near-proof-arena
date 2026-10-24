# Action code resolution and storage execution handoff

Base: main `dc4ff3dbe`. Branch: `work/lean-actions-resolution-storage-20261024`.
W05 is untouched. This implements the call-resolution/recorder integration in W08/W09;
it does not implement W07's global action tags, distribution receipts or promise translation.

## Execution

Use `nearspec-v3-check-successor --tier storageResolution CASE_DIR...`.
`Successor/StorageExecution.lean` consumes the existing logged D2 operations, retaining their exact
read trace in a chunk-scoped authenticated hash recorder. VM calls share the recorder and TTN cache.
The receipt baseline is captured after input-data and receiver-account reads, once per receipt.
Removing contract-data keys adds 2,000 bytes even for absent keys and failed receipts. VM writes
roll back with a failed receipt; recorder growth does not. Local/delayed/incoming processing and
promise-yield timeout draining check the strict `> 4,000,000` chunk soft limit. Instant receipt
draining retains the pinned loop's behavior. Finalization reads are recorded after scheduling.

Global resolution uses `get_ref().value_hash()` semantics. A global-by-account reference can resolve
with no code blob present; attempting execution then reports missing code. All four legacy wallet
magic hashes redirect on every chain, using the current chain's global wallet hash. The account's
stored contract field is never normalized to local as part of call execution.

Raw code retrieval and the pre-state `record_contract_call` probe are distinct from proof recording.
The latter uses the local/global contract trie key, with no side effects. The pinned
`TrieRecorder.record_code_len` method has no call sites in this nearcore checkout. Do not add every
code blob to ordinary trie read accounting. An account-identified global lookup does record the
trie path; ordinary actions that actually read code through the trie record those reads normally.

`Successor/RuntimeCore.lean` parameterizes the original validation shells over main execution and
the storage-size guard. Legacy specialization equals `checkD2Core` and `checkD2CoreG` by `rfl`;
header/proof/transaction comparisons are retained. New execution is opt-in through ProtocolCfg.
The signed definitions, old tier dispatch, gas bound and 8 MiB witness cap are preserved.

## Validation and reproduction

- Build `nearspec-v3-check-successor`, `nearspec-v3-test-storage-resolution`,
  `NearSpecV3.D3.GlobalContractTests`, `NearSpecV3.D3.GlobalContractCall` and
  `NearSpecV3.Successor.Resolution` from `spec/lean/v3`.
- `make d3-smoke` includes native recorder/resolution tests, eight-tier smoke, four committed new
  ETH-local chunks, 20 runtime/float chunks and four mutants under the new tier.
- Targeted corpus: 388 cases, 161 accepts and 227 licensed residual exclusions.
- Broader corpus: 1,788 cases, 1,503 accepts, 134 rejects, 151 licensed residual exclusions.
  Reports bind binary/input/output hashes and explicitly identify missing observable reporting.
- Native directed cases: below/at/above per-receipt and chunk limits; two calls sharing a budget;
  next-receipt reset; shared reference path deduplication; global identifier preservation;
  missing code blob; all four legacy hashes on four chains. A real action receipt runs 2,001 removes,
  fails, rolls back its writes, retains 4,002,000 proof bytes and delays the next incoming receipt.
- The older L4 test incorrectly expected an old-testnet wallet hash to remain local on mainnet.
  It now follows pinned `contract_code.rs:62`, which calls `LegacyEthWallet::resolve` across all hashes.

Final checks: `make d3-smoke` passed (1,030 allocation + six phase golden cases; 2,050 float
operator + 32 input-bundle golden cases, in addition to the new tests and chunk smoke). Python
test discovery: 59 tests, 58 passed and one skipped. Coverage drift and scoped diff checks passed.

## Remaining work and lane reconciliation

L4/W07 should route versioned actions and receipts through this stateful execution adapter. Do not
reuse `GlobalContractCall.functionCallResolved` for production integration: its older normalization
delegate retains the ETH guard and can persist a normalized identifier. Its old agreement lemmas
are not proofs of this new execution path. Reconcile with the shared corrected Rci resolver.

L1/W08 must settle cache/deploy/preparation ordering and authenticate any required environment fact.
The compiled-cache exclusion remains. Add independent positive global-by-hash/by-account/wallet
chunk fixtures, including absent blobs, rolled-back deploys and postponed calls.

L5/W09 must add independent nearcore whole-chunk proof-limit boundaries and full computed observable
comparison, then implicit/resharding interactions and measured resource bounds. The directed Lean
boundary tests are regression checks, not independent differential evidence. Existing recorded
chunk replays check verdicts and the roots/gas/receipts endorsed by accepted headers, but do not emit
all computed observables. The local cached successor oracle executable was unavailable during this
turn, so no fresh boundary-chain generation is claimed.

No whole work package, release gate, resharding support or W05 completion is asserted.
