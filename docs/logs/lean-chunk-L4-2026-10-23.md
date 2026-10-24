# Lean chunk L4 — global-contract actions and the two D3 hook guards

* **Owner:** L4
* **Worktree:** `/data/illia/nearproof-wt/lean-chunk-L4`
* **Branch:** `lane/lean-chunk-L4`
* **Base:** `a5ef42e0c`
* **Committed tip at the time of writing:** `0caa57d16` (see “Commits” below)
* **Nearcore pin:** `/data/illia/nearproof-deps/nearcore` @ `44f7ae6cd7ef08bab604e20a473bf77e35d4c993` (2.13.4, protocol version 86)
* **Plan:** `docs/requirements/LEAN_CHUNK_TRANSITION_PLAN.md` §“L4 — missing actions, hosts and contract resolution”

This log records what was actually built and measured. Five rows are in scope; **none reaches
`implemented`**, and this log says why for each rather than moving a status without evidence. The
short version:

* Tags 9/10/11 have pinned codecs, fees, storage charges and action bodies, all directed-tested,
  but **no whole chunk can carry one**, because `D2.Base` is closed and `pBase` rejects the tags.
  That widening is a signed-statement change owned by whoever owns the `near-chunk-v3` format.
* `L0-D3-008` (D3:248) **is closed by the delegate**: `functionCallResolved` rewrites
  `.global`/`.byAccount` to `.local`, so the guard's arm becomes unreachable. It is still not
  *exercised*, because no corpus witness has a global-contract account and the oracle cannot be
  changed to make one.
* `L0-D3-006` (D3:236-239) is **not closable by a delegate at all**, and that is now a proved
  theorem rather than an opinion: the delegate only ever produces `.none`/`.local _`, and the guard
  rejects every `.local _` on an ETH-implicit receiver. Lifting it needs the guard itself
  parametrised.

---

## 1. Row statuses

| Row | Inventory status before | after | Implemented? |
| --- | --- | --- | --- |
| `L0-action-09` DeployGlobalContract (tag 9) | `missing` | `partial` | semantics yes, whole-chunk no |
| `L0-action-10` UseGlobalContract (tag 10) | `missing` | `partial` | semantics yes, whole-chunk no |
| `L0-action-11` DeterministicStateInit (tag 11) | `missing` | `partial` | semantics yes, whole-chunk no |
| `L0-D3-008` `w.shape` / `D3/FunctionCall.lean:248` | `missing` | `partial` | guard closed, not exercised |
| `L0-D3-006` `e.eth_implicit_local` / `D3/FunctionCall.lean:236-239` | `missing` | `partial` | modelled + blocker proved, not lifted |

Inventory counts moved `missing 22 → 17`, `partial 8 → 13`; `implemented` stays 143. Regenerated
with the repo's own generator, so the file is not hand-edited:

```
python3 tools/d3/lean_chunk_coverage.py --repo . \
  --nearcore /data/illia/nearproof-deps/nearcore \
  --check docs/research/lean-chunk-coverage.json     # exit 0
```

The five rows are edited in `tools/d3/lean_chunk_coverage_l0.py` (the `R(...)` entries for the two
hooks) and in `tools/d3/lean_chunk_coverage.py` (`L4_ACTION_ROWS`, consulted by the action-tag
loop). The inventory is schema `near-lean-chunk-coverage-v2`, whose rows are **generated**; the
patch is therefore a source change plus a regenerated JSON, not a JSON-only edit.

---

## 2. What is implemented, with pinned citations

### 2.1 Tag 9 — `DeployGlobalContract`

| Fact | Pinned source | Lean |
| --- | --- | --- |
| Tag value 9 | `core/primitives/src/action/mod.rs` (`DeployGlobalContract`) | `GlobalContractExec.lean` `BaseL4.deployGlobal` |
| Borsh layout `code ‖ mode` | `action/mod.rs` | `pDeployGlobal`, `DeployGlobal.encode` |
| Mode tag 0 = code hash, 1 = account id | `core/primitives/src/action/mod.rs` | `GcdMode`, `pGcdMode` |
| Storage charge `0.0001 N/byte × code.len()` | `runtime/runtime/src/global_contracts.rs:38-44`; `core/parameters/res/runtime_configs/parameters.snap:271`; set by `77.yaml:2` | `deployGlobalStorageCost` = `globalContractStoragePerByte * code.length` |
| Insufficient balance ⇒ `LackBalanceForState` | `global_contracts.rs:41-47` | `actDeployGlobal` |
| Execution base cost `20_000_000_000_000` | `parameters.snap:272` | `deployGlobalExecBase` |
| Identifier trie key, column 18 | `core/primitives/src/trie_key.rs:133-143` | `kGlobalContractCode`, `colGlobalContractCode == 18` |
| Distribution receipt is a real receipt variant (tag 4) | `core/primitives/src/receipt.rs:572` | modelled; **not** in any witness (§4) |

### 2.2 Tag 10 — `UseGlobalContract`

| Fact | Pinned source | Lean |
| --- | --- | --- |
| Tag value 10 | `action/mod.rs` | `BaseL4.useGlobal` |
| Identifier encoding `0‖hash` / `1‖len‖id` | `core/primitives/src/global_contract.rs` | `Gci.encode`; `Gci.len` = 32 for hash, **account-id length** (not encoded length) for account id |
| Missing global contract ⇒ `GlobalContractDoesNotExist` | `global_contracts.rs:97-104`; `errors.rs:820` | `actUseGlobal` |
| Clears the account's local code storage usage | `global_contracts.rs:105-110` | `actUseGlobal` |
| Storage refund on replacing a larger local contract | `global_contracts.rs` | `contractStorageUsage`, `contractIdentifierUsage` |

The distinction `Gci.len (.accountId a) = a.length` versus `(Gci.accountId a).encode.length = a.length + 5`
is asserted in `GlobalContractTests.lean`; using the encoded length would over-charge storage.

### 2.3 Tag 11 — `DeterministicStateInit`

| Fact | Pinned source | Lean |
| --- | --- | --- |
| Tag value 11 | `action/mod.rs` | `BaseL4.stateInit` |
| Layout `state_init ‖ deposit` | `action/mod.rs` | `pDsi`, `Dsi.encode` |
| Account id = `"0s" ‖ hex(keccak256(borsh(state_init))[12..32])` — **Keccak-256 / SHA3-256**, not SHA-256 | `core/primitives/src/utils.rs:470-477` | `deriveDetAccountId`; 42 characters |
| Receiver must equal the derived id; keys/values within limits | `action_validation.rs:422-450` | `dsiValid` |
| New account: 0 balance, 100 usage (`num_bytes_account`) | `utils.rs` / `num_bytes_account` | `newDetAccount` |
| Base/entry/byte fees | `parameters.snap:86-98` | `feeStateInitBase`, `feeStateInitEntry`, `feeStateInitByte` |
| Entry storage charge `k.length + v.length + num_extra_bytes_record` | `trie_key.rs` / `num_extra_bytes_record` | `cdRecordBytes` |

The hash choice matters and is tested: Keccak-256 (SHA3-256) is **not** SHA-256, and the derivation
drops the first 12 bytes of the 32-byte digest. `GlobalContractTests.lean` pins the derived id's
length at 42 and its `0s` prefix.

---

## 3. The two hook guards

### 3.1 `L0-D3-008` — `D3/FunctionCall.lean:248` (`w.shape` global identifier)

`functionCallResolved` (`GlobalContractCall.lean`) resolves the account's contract before running
the **unchanged** `functionCall`:

* `.none` → `.none`;
* `.local h` → `.local h`, except an ETH-implicit account whose `h` is a wallet magic hash, which
  becomes `.local (ethWalletHash chainId)`;
* `.global h` → `.local h` (the identifier's code hash *is* `h`);
* `.byAccount id` → `.local (sha256 of the kGlobalContractCode trie value)`, and an absent value is
  `invalid: StorageInconsistentState` (`contract_code.rs:107-116`).

Because every successful branch yields a `local`, D3:248's `.global`/`.byAccount` arm is unreachable
behind the delegate. Proved as `resolvedContract_local_of_global` and
`resolvedContract_local_of_byAccount`.

### 3.2 `L0-D3-006` — `D3/FunctionCall.lean:236-239` (`e.eth_implicit_local`)

This guard is **broader than nearcore's condition**, and the gap is now formal:

* nearcore redirects only when the local hash resolves to a legacy wallet
  (`contract_code.rs:56-76`: `if let Some(legacy) = LegacyEthWallet::resolve(local_hash)`);
* the Lean guard refuses **every** ETH-implicit account whose contract is `.local _`.

So `redirects ⇒ guardPremise` holds (`redirects_imp_guardPremise`) but the converse fails
(`guardPremise_not_imp_redirects`): on "ETH-implicit, local, non-wallet-hash" accounts nearcore runs
the account's own local code, while D3 excludes it. That is 209 measured verdicts.

The delegate **cannot** fix this. Proved:

* `resolvedContract_local_stays_local`: a `.local` contract always resolves to `.local _`;
* `resolveAccount_local_stays_local`: the delegate's rewritten account always has a `.local` contract;
* `resolveAccount_eth_local_premise_survives`: therefore the guard's premise still holds after the
  delegate, so the guard still fires.

The honest conclusion: `L0-D3-006` needs the guard parametrised (an off-by-default flag so
`checkD3` is unchanged), which is a `checkD3`-adjacent edit this lane may not make under its
additive-only constraint. Escalated as the residual blocker in §7.

---

## 4. Measured behaviour

### 4.1 Successor vs D3α on the 539 in-scope corpus cases

All `d3c7`/`d3c8`/`d3c9`/`d3c10` OOD cases whose `d3_violations` contain `e.eth_implicit_local` or
`w.shape` (539 total; 1 case carries both, so the sets overlap once):

```
spec/lean/v3/.lake/build/bin/nearspec-v3-check-l4 <case-dir>...
```

| Result | Count |
| --- | --- |
| cases run | 539 |
| **identical verdict and reason** (`same: true`) | **539** |
| differences | **0** |

Verdict reasons: 209 ETH-implicit-local; 149 ML-DSA-65 key; 89 UseGlobalContract action; 79
non-ED25519 transaction key; 11 float operator; 1 chain segment; 1 SECP256K1 delegate signature.

**Why zero differences.** The delegate cannot lift either guard on these witnesses:

* 0 of 1,455 decoded accounts across the 539 witnesses have a `.global`/`.byAccount` contract, so
  D3:248 is never reached — and it could not fire anyway after resolution;
* 0 of the 890 local hashes are wallet magic hashes, so the ETH redirect never happens;
* the 89 “UseGlobalContract action” verdicts come from the **action decoder**
  (`D2/Types.lean:301`, `oodUseGlobal`), which runs before any hook. They never reach D3:248.

That last point corrects the previous inventory evidence, which attributed those 89 verdicts to
D3:248.

### 4.2 Accepted chunks

A 300-case random sample of the 19,007 accepted `*/d3/*` chunks: **300/300 accept under both
relations**, 0 differences. The hook change is provably a no-op off the wallet-redirect domain
(`successorHooks_functionCall_none`, `successorHooks_functionCall_local`).

### 4.3 Directed tests

`NearSpecV3/D3/GlobalContractTests.lean`: 134 kernel-evaluated `#guard` checks over codecs, trie
keys, identifier lengths, storage charges, wallet magic hashes (distinct from contract code hashes)
and the deterministic account-id derivation. Imported at `NearSpecV3.lean:32`, so a wrong literal
breaks `lake build` rather than only a downstream replay. All pass; the build would fail otherwise.

---

## 5. UQ-006 and UQ-007 answered

### UQ-006 — which global-contract/state-init receipts can appear in `source_receipt_proofs` at PV86?

**`GlobalContractDistribution` receipts are never in a chunk witness.** A witness's
`source_receipt_proofs` holds *outgoing* receipts of source chunks, and nearcore classifies
distribution receipts as **not instant** (`receipt.rs:474-492`: the `GlobalContractDistribution`
arm returns `false`), so they are ordinary outgoing receipts that cannot be validated from a
witness's own source proofs.

* `ReceiptEnum` tag 4 is `GlobalContractDistribution` (`receipt.rs:572`).
* `is_instant_receipt` returns `false` for it (`receipt.rs:490`) — unlike `PromiseYield` and
  single-`DeleteAccount` action receipts, which are instant.
* `validate_source_receipt_proofs` rejects any non-empty set when the source block is genesis and
  otherwise validates each proof against the source chunk's outgoing root
  (`chunk_validation.rs:449-470`, `528-545`).

Consequence for this lane: the `w.shape`/tag-4 exclusion in `D2/Types.lean` is **not** a gap in the
witness format. Tag 9/10/11 **actions** produce distribution receipts as *outgoing* receipts, but a
distribution receipt cannot be a *source* receipt in a witness. So the whole-chunk tests for tags
9/10/11 must exercise the action and its outgoing receipt, not a witness carrying a distribution
receipt as a source proof.

### UQ-007 — is `LegacyEthWallet` still reachable at PV86 after `EthImplicitGlobalContract` (83), and which hashes must be enumerated?

**Unreachable at PV86.** The gate flips at protocol version 83 and stays on:

* `core/parameters/res/runtime_configs/83.yaml:4`:
  `eth_implicit_global_contract: { old: false, new: true }`
* `core/parameters/res/runtime_configs/parameters.yaml:283` default `false`, superseded from 83 on.
* `core/primitives-core/src/version.rs:556` lists `EthImplicitGlobalContract` in the 83 group.

`contract_code.rs:64-78` therefore always takes the `Global { code_hash: eth_wallet_global_contract_hash(chain_id) }`
branch and never constructs `RuntimeContractIdentifier::LegacyEthWallet`. That is why
`Rci.legacyEthWallet` is modelled (`Rci.resolvePre83`) but dead at PV86.

**Hashes to enumerate.** Two different families, both recomputed from the pinned blobs and kept
apart in the Lean layer:

| Chain | Contract code hash (`ethWalletHash`) | Magic hash (`walletMagicHash` = `sha256("near" ‖ base58(codehash))`) |
| --- | --- | --- |
| mainnet / mocknet | `1daa835c4637f7ae3d924095ba3f0bf2829bcfa17b1068cd58bd853dcad7ceb5` | `5abc64622ddd3661899e5d765e7a5295115e9057c54e9bb9f0f0e02cd1d2116` |
| testnet | `238feac1f86cc9f9f4003e3f6d5aebc04eaea9c394032bd29470e9609b67f6c5` | `b4fbbc964b350bd021b4a785b9ddd63e41d6f132702a6b38a23b5648ab2fb472` |
| old testnet (PV70, testnet only) | `260f6d4224a7f35db6b76661a23ad3caafcc28d97064744a61c64529de1b6da8` | `394abeb35e707609de8f73b63d43bd1a376ffe67935caa68937dd29bc04e673c` |
| localnet (and any other chain id) | `d2884a900d4fa370e48f1e3d4865d4dc0dbd093c89f0e7baef2eddc142c49e8d` | `3e6d7dd8c2578ac8a5ebe78fd32d600a555cef5ef7445d3a964658669d707cf2` |

* `eth_wallet_global_contract_hash` (`near-wallet-contract/src/lib.rs:89-105`) returns the **code
  hash** above: mainnet/mocknet literal, testnet literal, else `LOCALNET.read_contract().hash()`.
  Its doc comment names the base58 forms `2zodJZK2e4nnv5AqwCRnenNSmkikXhEd7PPY6BmfTmW4` (mainnet)
  and `3PpYvRxBfC5BkZxTw8ZFG3D52w1ZRhvDDWirKoxphMDn` (testnet).
* `code_hash_matches_wallet_contract` / `LegacyEthWallet::resolve` (`lib.rs:37-52,107-124`) compare
  against the **magic hash**, and the old-testnet magic hash counts **only** when
  `chain_id == TESTNET`.
* `GlobalContract.lean` mirrors that: `walletOf`/`matchesWallet` (`lib.rs:64-70,107-124`) with the
  testnet-only old-testnet clause.
* `eth_wallet_global_contract_hash` and `wallet_contract_magic_bytes` differ for every variant; the
  Lean tests assert the difference so the two families cannot be conflated.

---

## 6. Commands and results

```
# build (root import pulls in GlobalContractExec + GlobalContractTests)
cd spec/lean/v3 && lake build NearSpecV3
# Build completed successfully (91 jobs)          exit 0
#   one pre-existing linter warning: GlobalContract.lean:334 unused `chainId`

lake build NearSpecV3.D3.GlobalContractCall       # 62 jobs   exit 0
lake build NearSpecV3.D3.GlobalContractChunk      # 63 jobs   exit 0
lake build probe-l4                               # 124 jobs  exit 0
lake build nearspec-v3-check-l4                   # 126 jobs  exit 0

# axiom footprint of the new theorems (no sorry, no new axiom)
lake env lean /tmp/Ax4.lean
# '…resolvedContract_local_stays_local'        depends on axioms: [propext]
# '…resolveAccount_local_stays_local'          depends on axioms: [propext]
# '…resolveAccount_eth_local_premise_survives' depends on axioms: [propext]

grep -rn "sorry" spec/lean/v3/NearSpecV3/D3/GlobalContract*.lean
# no proof-position occurrence (one match is the word "sorry" inside a doc comment)

# signed statement and protected files untouched since the base commit
git diff a5ef42e0c HEAD --stat -- \
  spec/lean/v3/NearSpecV3/D3/FunctionCall.lean \
  spec/lean/v3/NearSpecV3/D2/ \
  spec/tools/build_challenge_draft_v3_chunk.py
# (empty)

git diff a5ef42e0c HEAD -- spec/lean/v3/NearSpecV3.lean spec/lean/v3/lakefile.toml
# additive only: 14 import lines + 8 lines for the two research drivers

make pin-check                                    # exit 0 (oracle/v3-d3 source sha256 verified)
python3 tools/d3/lean_chunk_coverage.py --repo . \
  --nearcore /data/illia/nearproof-deps/nearcore \
  --check docs/research/lean-chunk-coverage.json  # "matches pinned sources", exit 0
```

`checkD3`/`RelD3` and the 115,284-case D3 run were **not re-run**: nothing in this lane touches the
pipeline they measure (the diff above is the proof), so the baseline 115,284/115,284 stands.

### Evidence paths

* `evidence/lean-chunk-L4/replay/d3-hook-full-replay-539.txt` — one JSON line per case
  (`d3`, `d3Reason`, `global`, `globalReason`, `same`).
* `evidence/lean-chunk-L4/replay/d3-hook-full-replay-summary.json` — totals and per-reason counts.
* `evidence/lean-chunk-L4/replay/d3-hook-replay-summary.json`, `d3-hook-cases.json` — the earlier
  388-case partial sweep, kept for provenance.
* `spec/lean/v3/NearSpecV3/D3/GlobalContractTests.lean` — 134 directed `#guard` checks.

---

## 7. Gaps and residual blockers

1. **Whole-chunk cases for tags 9/10/11 do not exist and cannot be made in this lane.**
   `D2/Types.lean:299-302` rejects the tags inside `pBase`, and `pRcpt`/`pTxD2` are the decoders
   `checkD2Core` calls internally. A successor that accepted these actions end to end would have to
   re-state `checkD2Core` (190 lines) or widen `D2.Base`; both are outside an additive-only lane.
   Whole-chunk acceptance is therefore **unmet** for all three action rows, and the rows say so.
2. **`L0-D3-006` needs the guard parametrised.** `resolveAccount_eth_local_premise_survives` proves a
   delegate cannot do it. The minimal additive change is an off-by-default flag in
   `functionCall`'s ETH branch plus a successor hook that passes it on — an edit to
   `D3/FunctionCall.lean`'s guard (not its `gAlpha`, which stays untouched either way). This needs
   an owner decision because it is adjacent to the signed statement.
3. **No witness exercises D3:248 or the wallet redirect.** 0 global/byAccount accounts and 0 wallet
   magic hashes in 1,455 decoded accounts over 539 witnesses. Closing either row needs a witness
   the oracle cannot currently produce (`oracle/v3-d3` is pinned and off-limits).
4. **`L0-D3-008` evidence corrected.** The 89 `w.shape: UseGlobalContract action` verdicts are the
   action decoder's, not D3:248's; D3:248 needs a `.global`/`.byAccount` *account*, which the corpus
   does not contain. The row's remaining work now names the real gap.
5. **Hook guard status.** `functionCallResolved` is wired into `checkD3Global`/`RelD3Global`
   (`GlobalContractChunk.lean`) but **not** into `checkD3`/`RelD3`, which is intentional and
   required. `GlobalContractCall.lean` §6 records the delegate's ETH limitation in its header so a
   later reader does not mistake the delegate for a complete fix.

---

## 8. Next step

Escalate item 2: decide whether `functionCall`'s ETH-implicit guard may gain an off-by-default
parameter. If yes, the sequence is (a) add the flag defaulting to the current behaviour so `checkD3`
is bit-identical, (b) add a successor hook that enables it and redirects wallet magic hashes to
`ethWalletHash`, (c) hand-build one witness with a wallet magic hash on an ETH-implicit receiver and
replay it. Items 1 and 3 need the format owner (widening `D2.Base`) or the oracle owner (producing
global-contract witnesses) respectively; neither is in L4's authority.

## 9. Safe files

Untouched since the base commit and safe to keep as they are: `D3/FunctionCall.lean` (including
`gAlpha`), all of `D2/`, `spec/tools/build_challenge_draft_v3_chunk.py`, `NearSpecV3/D2/Actions.lean`.
Changed by this lane: `D3/GlobalContract.lean`, `D3/GlobalContractExec.lean`,
`D3/GlobalContractTests.lean`, `D3/GlobalContractCall.lean`, `D3/GlobalContractChunk.lean`,
`NearSpecV3.lean` (imports only), `lakefile.toml` (two research drivers), `ProbeL4.lean`,
`MainL4.lean`, `tools/d3/lean_chunk_coverage.py`, `tools/d3/lean_chunk_coverage_l0.py`,
`docs/research/lean-chunk-coverage.json`, plus `evidence/lean-chunk-L4/`.

## 10. Commits

* `147e7c1d0` — successor FunctionCall hook that resolves global contract identifiers
* `7d983f391` — successor chunk checker with the resolving hook, plus the L4 probe
* `9e6bc2b35` — successor hook + guard-premise gap theorems, successor chunk layer, probe/checker drivers
* `0caa57d16` — prove the delegate's ETH-guard blocker; five owned rows to `partial` with measured evidence
