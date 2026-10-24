# Cache closure and global action integration — 2026-10-24

Base: main `197767793`. Integration branch: `work/lean-cache-global-main-20261024`.
Nearcore: `44f7ae6cd7ef08bab604e20a473bf77e35d4c993`, PV86. W05 excluded.

## Delivered

Three parallel lanes implemented code-witness closure, typed global execution, and independent
nearcore fixtures. The integration composes them with the existing recorded runtime. The older
cached integration branch contained unrelated work, so this branch was reconstructed directly from
main and only this task's commits were picked. Lane branches/worktrees remain available.

- `globalActions`: versioned state-witness/transaction/delegate/global action and distribution codecs;
  canonical Borsh last-value-wins state-init maps; receipt validation and explicit shard routing;
  buffered, delayed, postponed and yield receipt decoding; deploy/use/state-init fees, balances,
  storage usage, nonce, refunds and rollback. Distribution V1/V2 performs target-state writes,
  compute charging and forwarding without inventing an execution outcome.
- Seven global/state-init promise hosts preserve deploy mode, identifier, data values and sorted
  keys. State-init returns a receipt-local action index, including interleaved receipts and preceding
  actions. Translation preserves ordinary actions/refund metadata and checks its temporary slots.
- `completeCodeGlobal`: the above plus hash-verified raw witness requirements for unchanged or
  unresolved pre-state code origins. Proven new identities may use authenticated current/committed
  deployment or distribution materialization. Failed attempted deployments never supply code.
  Missing bytes produce `invalid witness (w.code_complete)`; this is a distinct witness relation.
- Legacy signed decoding/dispatch retains its guards; the legacy runtime-driver specialization is
  definitionally equal to the original core. No signed relation is widened by a new default flag.

## Validation and evidence

| Check | Result and scope |
|---|---|
| Named driver build | All nine driver/test executables build; legacy logged receipt proofs rebuild; code-selection laws and promise host tests pass. |
| Global actions | Native directed codecs, fees, permissions, deploy/use/init, nonce, freshness, routing, refunds and malformed-identity checks pass. |
| Independent codec comparison | All 12 pinned Rust vectors match canonical bytes, transaction/delegate hashes, deterministic IDs and malformed rejection. |
| Global/cache chunks | 265 per tier, each 162 accept / 99 reject / 4 asserted exclusions. Honest population: 95 accept / 4 exclusions; all 166 mutants agree. |
| Global promise chunks | 83 per tier all accept, covering successful seven-host emission, gas-exhaustion rollback and child-action failure. |
| Complete-code pairs | 14 independent pairs × complete/incomplete/restored × two repetitions = 84 passing verdicts. Raw incomplete native observations remain 9 accept / 5 reject. |
| Portable CI | 26 global accepts, 2 explicit key exclusions, 3 promise controls in both tiers; 5 code-policy pairs give 30 repeated checks; old-host ablation rejects widening. |
| Python harness | 67 tests run, one existing skip; includes eight policy integrity checks. |
| Coverage inventory | Regenerated/reviewed source hashes and legacy decision-site counts only. No whole W07/W08 row or completion gate promoted from this checkpoint. |

Replay reports bind executable, harness, input and output hashes under
[global-cache fixtures](../evidence/lean-chunk-completion/global-cache-fixtures/replay/).
The [promise evidence](../evidence/lean-chunk-completion/global-promise-fixtures/lean-replay.json)
and [paired-policy evidence](../research/evidence/complete-code-policy/) record their exact artifacts.
Different artifact hashes are retained where tests ran before the unsupported-key error-label fix.
The final smoke suite exercises portable fixtures against the final executable.

The four broad-run exclusions are non-Ed25519 transaction keys, ML-DSA-65 keys, ecrecover host
execution and secp256k1 delegate verification. A real integration bug wrapped the ML-DSA `w.shape`
guard in a Wasm error; this was corrected and a full-key regression added. The complete-policy smoke
checks its expected missing-code rejection separately from the raw oracle's acceptance; metadata is
never relabeled to manufacture agreement. Generic `w.shape` exclusions are not globally waived.

These replays check acceptance and exclusion reasons. The checker recomputes and checks header
commitments, but this CLI still lacks independent export/comparison of every computed observable;
that W01/W12 obligation remains. Directed and generated coverage is not exhaustive equivalence.

## Remaining work and dependencies

1. **W07 → W06:** finish gas-key action/host translation and the required key/verification families.
2. **W07 → W11:** implement ancestor-shard mapping for distributions targeting an obsolete layout;
   the current explicit boundary is `c.same_layout`.
3. **W08 environment/identity:** current mismatched CodeHash distributions are explicitly excluded
   as `out of domain (w.shape): global_code_identity`. Pinned release nearcore trusts supplied hashes
   in compiled-code construction. Historical poisoned cache contents therefore remain an environment
   boundary; complete raw witness bytes alone do not prove equality with arbitrary cache histories.
4. **W08/W09 composition:** expand postponed/yield, wallet redirects and exact storage-limit scenarios
   with the complete-code policy. Establish full observable parity and the intended environment
   invariant, rather than treating missing-code normalization as a native protocol verdict.
5. **W12/W14:** overlap/tier proofs, full combined replay, capacity bounds and a frozen package.
   W13 representative witness acquisition and Gate A/B/C admission/release remain separate.

See [cache policy/source audit](../research/lean-code-witness-closure.md),
[global source review](lean-global-actions-source-review-2026-10-24.md), and the
[completion workplan](../requirements/LEAN_CHUNK_COMPLETION_WORKPLAN.md).

## Reproduction

From the repository root:

```sh
make d3-drivers
make d3-smoke
python3 -m unittest discover -s oracle/tools -p 'test_*.py'
python3 tools/d3/lean_chunk_coverage.py --repo . --nearcore /path/to/pinned/nearcore --check docs/research/lean-chunk-coverage.json
```

Fresh external windows and selected case lists are described in the global fixture README and
manifests. Portable CI fixtures require no external corpus or nearcore checkout.
