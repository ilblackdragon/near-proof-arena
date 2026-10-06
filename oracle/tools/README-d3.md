# `spec_check_v3_d3.py`: the independent Python checker for domain D3α

`spec_check_v3_d3.py` decides `Rel_D3α` for `near/pv86/chunk-validation/v0` case directories
(`claim.bin`, `witness.bin`). It prints one JSON line per case:
`{"case", "verdict": accept|reject|out_of_domain, "reason"}`.

```
oracle/tools/spec_check_v3_d3.py CASE_DIR...
oracle/tools/spec_check_v3_d3.py --list FILE        # case directories, one per line
oracle/v3-d3/tools/difftest_d3.py CORPUS --python [--no-lean] [--shards K] [--save DIR]
                                  [--lean-from FILE] [--python-from FILE]
```

## Sources and independence

The checker was written from:

* the nearcore 2.13.4 sources (PV 86);
* the D2 checker it extends, `spec_check_v3_d2.py`, imported as a module and unchanged;
* the prose specs `spec/near-chunk-validation-d2.md` and `spec/near-chunk-validation-d3.md`;
* the clean-room WASM implementation `oracle/wasm-d3/cleanroom/` (`nearwasm.py`, `nearstore.py`,
  `nearcrypto.py`), imported unchanged;
* `docs/research/d3-trie-accounting.md`.

It does not use the Lean specification, `oracle/wasm-d3/lean`, or the oracle's classifier
(`oracle/v3-d3/src`). The Lean checker's outputs were compared only as a black box, in the difftest.

## What it adds to D2

**Witness.** `w.no_code` is lifted. The code blobs appended to `witness.bin` are merged into the
main transition's recorded values, and every trie read uses `base_state ++ codes`. `w.size` sums
the merged list, both for the 3,000,000-byte bound and for the proof-limit bound.

**FunctionCall** (`ApplyD3.function_call`, `function_call.rs`):

* The exec fee, then the account check.
* An overflow of `amount + deposit` rejects.
* Action hash and data ids: `sha256(rid ‖ h ‖ u64(2⁶⁴−1−i))` and `sha256(ah ‖ h ‖ u64(n))`. The
  counter is shared by then-joins and yields.
* The code lookup (§2.2 and P1 below):
  * `contract = None` is a 0-gas `CodeDoesNotExist`.
  * A contract set by a deploy in this chunk comes from the deploy tracker (committed, or the
    current receipt's uncommitted deploys), then from the witness.
  * A pre-state contract comes from the witness only. If its blob is missing and the same code
    was deployed earlier in the chunk, the case is out of domain (`e.code_cache`). If its blob is
    missing otherwise, the case rejects (`MissingTrieValue`).
* The VM run. The clean-room VM is driven with nearcore's real `External`:
  * A `ReceiptManager` model holds receipt indices, `output_data_receivers` and `input_data_ids`
    of then-joins, `refund_to`, gas weights, and `InvalidMethodName` for non-UTF-8 FunctionCall
    and AddKey method names.
  * Yields create, look up and resume through the trie overlay (status, the yield-id mappings,
    and the `PromiseYieldReceipt` / `PromiseYieldStatus` checks).
  * Context getters come from B2 and the claim: timestamp, `random_value`, `epoch_height`, the
    validator stakes of B2's epoch, and `chain_id`.
  * `current_contract_code` returns the account's contract.
  * The 1-yocto subsidy is counted.
  * Contract storage goes through the D2 `TrieUpdate` overlay. Trie-node accounting follows
    `nearstore.TrieStore`: a chunk-scoped touch cache, path touches on write and remove, and an
    uncharged value touch on read.
* Gas-weight distribution, also for aborted outcomes.
* The VM outcome merges into the `ActionResult`:
  * On success: yield timeouts, V2 action and yield receipts, then resume receipts; then
    `PromiseYieldIndices`, and the account's `amount` and `storage_usage`.
  * Always: `gas_burnt_for_function_call` and the logs.

**`apply_action_receipt`:**

* `promise_results` come from the received data.
* `merge` keeps `ret` (`ReceiptIndex` shifted to the global index), `logs`, `gas_fc` and
  `subsidized`, with the panic assertion `gas_fc ≤ gas_burnt ≤ gas_used`.
* The receiver reward is `burn · ⌊gas_fc·3/10⌋`, paid after commit or rollback when the account
  exists. The outcome's `tokens_burnt` is taken before the reward. The chunk's `tx_burnt` is taken
  after it.
* Output data receivers are forwarded to the returned receipt on `ReceiptIndex`. Otherwise the
  data receipts carry `Some(v)`, `Some([])` or `None`.
* The status is `SuccessValue(v)` or `SuccessReceiptId`.
* The outcome leaf includes the hashed logs: `sha256(u32(2+n) ‖ id ‖ sha256(P) ‖ sha256(logᵢ)…)`.
* `balance_burnt = tx + other − subsidized`. A negative value rejects.

**Domain conditions.**

* Out of domain:
  * float modules;
  * the curve, state-init, global-contract and gas-key host functions (when called);
  * global-contract accounts;
  * ETH-implicit accounts with a local contract;
  * ML-DSA keys in VM-created actions;
  * `e.code_cache`;
  * `e.g_alpha`.
* D2's conditions are otherwise unchanged.

## Three-way difftest (nearcore, Lean `nearspec-v3-check-d3`, Python)

`difftest_d3.py --python` runs both checkers as 16 parallel processes. Inputs and outputs go
through files, not pipes. It reports three comparisons separately: Lean vs nearcore, Python vs
nearcore, and Lean vs Python, where every verdict difference counts, `out_of_domain` included.

**The two §10.0 conditions.** For the code-cache condition (decision 2) and G_α (decision 3),
nearcore has no verdict to compare against. Instead, the oracle's classifier marks them in
`meta.json` `d3_violations`. A checker's out-of-domain verdict on either condition must coincide
with the oracle's mark, and a checker must never accept a case the oracle puts above G_α.

The corpora are `d3corpus`, `d3corpus2` and `d3corpus3` (seeds 7, 8 and 9; the 2026-10-06
11:11 generation). The verdicts below are Python's. Lean's are identical, case by case.

| | corpus 1 | corpus 2 | corpus 3 |
|---|---|---|---|
| cases | 36,038 | 54,722 | 17,892 |
| accept (nearcore ok) | 11,888 | 18,189 | 5,850 |
| reject (nearcore reject) | 22,363 | 33,870 | 11,024 |
| out of domain: `e.g_alpha` | 1,503 | 2,196 | 882 |
| out of domain: `e.code_cache` (code mutants; nearcore ok / reject) | 91 (57 / 34) | 169 (110 / 59) | 59 (25 / 34) |
| out of domain: floats, curve calls, `w.shape`, `e.secp`, `c.not_genesis`, `c.segment` | 193 | 298 | 77 |
| honest in-domain witnesses accepted | 5,499 / 5,499 | 8,541 / 8,541 | 2,779 / 2,779 |
| **Python vs nearcore**, decided cases | **0** | **0** | **0** |
| **Lean vs nearcore**, decided cases | **0** | **0** | **0** |
| **Lean vs Python** (any verdict difference, `out_of_domain` included) | **0** | **0** | **0** |

Run times on 16 cores: Python 4 min (corpus 1), Lean 18 min (corpus 1).

**Stale oracle metadata.** These corpora predate the oracle classifier's `e.g_alpha` /
`e.code_cache` marks. The current `difftest_d3.py` requires the oracle's `d3_violations` to agree
with a checker's out-of-domain verdict on these two conditions. On these corpora it therefore counts
every G_α and code-cache case as a disagreement, for Lean and Python alike:

| corpus | counted | made up of |
|---|---|---|
| 1 | 1,594 | 1,503 G_α + 91 code-cache |
| 2 | 2,365 | 2,196 G_α + 169 code-cache |
| 3 | 941 | 882 G_α + 59 code-cache |

These counts go to 0 once the corpora are regenerated with the updated classifier, provided its
marks agree with both checkers.

**Sensitivity.** Each line is one deliberately wrong variant of the Python checker. The base set is
400 honest corpus-1 witnesses that execute contract code, all of which the correct checker accepts.
The count is how many each variant still accepts.

| variant | still accepted |
|---|---|
| no trie-node charges | 100 / 400 |
| logs not hashed into the outcome leaf | 233 / 400 |
| MockedExternal data ids | 309 / 400 |
| zero random seed | 380 / 400 |
| no gas-weight distribution | 391 / 400 |
| no receiver reward | 400 / 400 |

**Coverage gap: the receiver reward is never exercised.** The chunk gas price (B2's
`next_gas_price`) is 0 in these TestEnv chains. So `burn = min(purchase, gas_price) = 0`, and the
following are all 0 in every case:
* the receiver reward (§6.3, E10);
* every `tx_burnt` term;
* the outcome's `tokens_burnt`.

The difftest checks none of them, for Lean or Python. A corpus with a nonzero minimum gas price is
needed.

## Findings: where `spec/near-chunk-validation-d3.md` was wrong or silent

**P1. §2.2 [decision] and §10.1 do not say which contracts the deploy tracker may serve.**

What the spec says:
* §2.2 [decision] says the code is the blob with `sha256 = h` from "(a) the chunk's deploy tracker
  … or (b) `w.main.values ++ codes`".
* §10.1 says "A contract set by a deploy in this chunk is served by the deploy tracker" but never
  defines "pre-state contract".

What nearcore does:
* For a pre-state contract, rule (a) is not what nearcore does.
* The preparation pipeline (`runtime/runtime/src/pipelining.rs:152-300`) prepares a submitted
  receipt's call in the background, against the compiled-contract cache and the
  `ContractStorage` as it is *at preparation time*.
* `get_contract` reuses that preparation whenever its `expected_hash` still equals the
  identifier's hash (`pipelining.rs:351`).
* A call to a pre-state contract can therefore be prepared cold before an earlier-in-chunk deploy
  of the same code has run. nearcore then rejects, even though the tracker holds the code.

Observed:
* The first Python version (rule (a) for every account) accepted 3 corpus-1 code mutants that
  nearcore rejects with `MissingTrieValue`: `04-h10056-s4-code.flip.0`,
  `05-h10165-s4-code.truncate.0` and `06-h10070-s0-code.flip.1`.
* In each, the missing blob's code had been deployed, and committed, to another account earlier in
  the chunk.

Fix: §10.0's `e.code_cache` applies to every pre-state contract, whether the deploy was committed or
rolled back.

"Pre-state contract" needs a definition. The one that matches nearcore's pipeline is: the account's
current local code hash equals its hash in the chunk's pre-state trie.
* A deploy of different code changes `expected_hash`, so the stale preparation is discarded and the
  tracker serves the code (`pipelining.rs:351`, then `core/store/src/contract.rs:104-130`).
* A same-hash redeploy keeps the stale preparation, so it is still cache-dependent.

The second Python version used "the account had any deploy in this chunk". It disagreed with Lean
on 28 corpus-1 code mutants: 22 same-hash redeploys and 6 `code.none` mutants that reached such a
call first. With the definition above, all 28 agree.

**P2. §10.0 decision 3 (G_α) does not say when the condition is evaluated.**

* The condition is a property of the whole chunk, Σ `gas_burnt_for_function_call`.
* The spec does not say whether a storage error later in the main transition, after the G_α
  crossing, is a reject or out of domain.

The first Python version stopped at the call that crossed G_α, and returned `out_of_domain`. Lean
completes the main transition, including the trie update (`finalize`), and only then checks G_α.
So a `MissingTrieValue` anywhere in the main transition rejects, while post-state-root and header
mismatches are out of domain. This difference gave 142 Lean≠Python cases on corpus 1:
* `w.drop_node.main.*` and `w.base_state.drop_node` mutants;
* `code.drop` / `flip` / `truncate` mutants whose missing node or code lies after the crossing.

nearcore rejects all of them, so neither order disagrees with nearcore. The Python checker now
evaluates G_α after `finalize` and before the post-state-root comparison.

The spec should state this order. It should also note the consequence: deciding the condition
requires executing the whole chunk. The corpus has chunks with up to 229 Tgas of function-call
gas, 66× G_α.

**P3. §10 / §10.1 do not say *when* the excluded host-function families are out of domain.**

* The families are the state-init, global-contract and gas-key ones (and the curve functions of
  the WASM spec).
* The options are: at link time (the import is present), or when the function is called.

The Python checker follows the clean-room VM: it is out of domain when the function is called. An
import that is never called stays in domain. No corpus case distinguishes the two.

**P4. §3 and §9 are silent on ML-DSA keys in VM-created actions.**

* `PostQuantumSignatures` is enabled at PV 85 (`core/primitives-core/src/version.rs:567`).
* The VM decodes keys with `post_quantum_keys_enabled()` (`ext.rs` `post_quantum_keys_enabled`,
  `wasmtime_runner/logic.rs:530-542`).
* So a contract can create `Stake` / `AddKey` / `DeleteKey` actions with ML-DSA-65 keys.
* D2 decodes such keys as out of domain (`w.shape`), but the D3 spec does not say what happens when
  the VM *creates* them.

The Python checker returns `out_of_domain` (`w.shape`). The corpus has no such case.

**P5. §2.1 / §10: the ETH-implicit legacy-wallet exclusion is not decidable from the prose alone.**

The spec excludes "ETH-implicit legacy wallet resolution" (`contract_code.rs:56-76`). The test
`LegacyEthWallet::resolve(local_hash)` needs the wallet hashes, which the prose does not list. The
Python checker excludes every ETH-implicit account with a local contract. That set is larger than
the exclusion, so the checker is conservative. The corpus has no such case.
