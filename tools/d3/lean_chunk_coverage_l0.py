#!/usr/bin/env python3
"""Generate docs/research/lean-chunk-coverage.json (L0 boundary/coverage inventory).

Documentation only: reads the Lean sources and the pinned nearcore tree, writes JSON.
Usage: python3 docs/research/lean-chunk-coverage-gen.py > docs/research/lean-chunk-coverage.json
"""
import json, sys, hashlib, os, re

NC = "44f7ae6cd7ef08bab604e20a473bf77e35d4c993"
BASE = "833f3311c26baa3144a1aece84f0c9d0f25d4f08"
ROWS = []

def R(id, family, lean, near, status, guard, evidence, owner="L0",
      deps=None, tests=None, work="none"):
    ROWS.append(dict(id=id, family=family, nearcore_commit=NC,
                     lean_path_symbol=lean, nearcore_path_symbol=near,
                     status=status, domain_guard=guard, evidence=evidence,
                     owner=owner, dependencies=deps or [], acceptance_tests=tests or [],
                     remaining_work=work))

# ---------------------------------------------------------------- D2 core guards
D2 = "spec/lean/v3/NearSpecV3/ChunkValidationD2.lean:"
R("L0-D2-001","d2-core",D2+"119","chain/chain/src/stateless_validation/state_witness.rs:45 (decode_witness); pwt.rs:693-696",
  "implemented","w.no_code",
  ["D2:119 `if !allowCodes then check codes.isEmpty`","D3 calls checkD2Core with allowCodes=true (D3/FunctionCall.lean:400)", "no `w.no_code` verdict in the 115,284-case D3 run"],
  deps=["L1"],tests=["D2 corpus 67,384/67,384 (D2 keeps allowCodes=false)"],work="none for D2; lifted only in D3")
R("L0-D2-002","d2-core",D2+"120","chain/chain/src/stateless_validation/state_witness.rs:21-22 (STATE_WITNESS_COMPRESSION_LEVEL; transport 64 MiB)",
  "implemented","w.size (8 MiB witness)",
  ["D2:120 `lenT swBytes ≤ 8388608`", "`out of domain (w.size): witness larger than 8 MiB` never appears in the 115,284-case D3 run"],tests=["directed 8 MiB boundary case (absent from corpus)"],work="none; arena-format bound, not a nearcore condition")
R("L0-D2-003","d2-core",D2+"122","chain/validation.rs / witness decode",
  "implemented","witness chunk header = claim",
  ["D2:122 `w.innerBytes == c.chunkInner`"],tests=["directed header-tamper case (absent from corpus)"],work="none")
R("L0-D2-004","d2-core",D2+"123","chain/chain/src/stateless_validation/chunk_validation.rs:310-318",
  "implemented","witness epoch id = claim epoch id",
  ["D2:123 `w.epochId == c.epochId`", "nearcore pre_validate also compares the epoch id (judge.rs:119-124 in oracle/v3-d3/src/d3judge.rs)"],tests=["directed epoch-id mutant (w.epoch_id mutant class rejects 131)"],work="none")
R("L0-D2-005","d2-core",D2+"125","core/primitives-core/src/version.rs:576 (EnforcePerReceiptStorageProofLimit => 86); oracle judge uses RuntimeConfigStore(None).get_config(86)",
  "implemented","c.pv86",
  ["D2:125 `c.protocolVersion == 86`", "not exercised: every corpus claim has pv=86"],deps=["L9"],tests=["directed PV85 claim (absent)"],work="PV-upgrade segments reference PV85 epochs; see UQ-009")
R("L0-D2-006","d2-core",D2+"128","chunk_validation.rs:369-371 (blocks_after_last_last_chunk non-empty)",
  "implemented","non-empty chain segment",
  ["D2:128 `!blks.isEmpty`"],tests=["directed n_blocks=0 claim"],work="none")
R("L0-D2-007","d2-core",D2+"131","spec/claim-v3.md §2.2 (epoch table strictly ascending)",
  "implemented","epoch table strictly ascending",
  ["D2:131 `strictlyAscending (c.epochs.map ...)`"],tests=["directed unsorted epoch table"],work="none")
R("L0-D2-008","d2-core",D2+"133","spec/claim-v3.md §2.2",
  "validated","epoch table = referenced epochs",
  ["D2:133 `c.epochs.map ... == referenced`", "988 verdicts `invalid: epoch table does not match the referenced epochs` in the 115,284-case run"],tests=["corpus mutant `w.epoch_id`/epoch-table mutants"],work="none")
R("L0-D2-009","d2-core",D2+"136","spec/claim-v3.md §2.2",
  "implemented","epoch_id in the epoch table",
  ["D2:136 `c.epochs.find? ...`"],tests=["directed missing epoch_id"],work="none")
R("L0-D2-010","d2-core",D2+"137","spec/claim-v3.md §2.2",
  "implemented","epoch record pv = claim pv",
  ["D2:137-138"],tests=["directed pv mismatch"],work="none")
R("L0-D2-011","d2-core",D2+"139","core/primitives-core/src/version.rs:540-576; per-epoch runtime config",
  "implemented","c.pv86 for every epoch",
  ["D2:139 `c.epochs.all (·.protocolVersion == 86)`", "never triggered in the corpus (all epochs pv=86)"],deps=["L9"],tests=["directed segment spanning a PV85->86 activation"],work="genuine cross-PV segment gap (UQ-009)")
R("L0-D2-012","d2-core",D2+"140","chunk_validation.rs:258-305 (get_resharding_transition); core/primitives/src/epoch_manager.rs:22-96 (DynamicReshardingConfig)",
  "implemented","c.same_layout (resharding)",
  ["D2:140 `c.epochs.all (·.shardLayout == ep.shardLayout)`", "claim scan of all 115,284 claims: 0 have two different shard layouts and 0 carry a split gate, so `c.same_layout`/`c.no_split_gate` never fire", "the 1,127 `c.no_resharding` oracle marks cannot mean a layout change: 274 have one epoch, 850 have two epochs with byte-identical layouts, 3 have 3-4 identical layouts; 700 are accepted by Lean, Python and nearcore. The resharding path therefore has zero corpus coverage.", "exclusion argument now stated: `ReshardingD3.sameLayout_forbids_resharding` (guard true => consecutive-epoch layouts equal => get_resharding_transition's `shard_layout != prev_shard_layout` conjunct at chunk_validation.rs:273-274 cannot hold)"],
  owner="L6",deps=["L6","L7"],tests=["var/l6/mut/same_layout_broken fires `out of domain (c.same_layout): resharding`"],work="legacy-core guard (checkD3Core) only: the signed tier hands such claims to the recorder (D3.withReshardHandover) and allFeatures decides them; see L0-resharding (validated)")
R("L0-D2-013","d2-core",D2+"142","core/primitives/src/shard_layout (V2/V3); Layout.lean:65",
  "implemented","c.layout (1..64 shards, V2/V3)",
  ["D2:142 `1 ≤ L.numShards && L.numShards ≤ 64`", "Layout.lean:65 rejects non-V2/V3 encodings", "never triggered: corpus uses 4-6 shard V2 layouts"],deps=["L1"],tests=["directed V1/V0 single-shard layout"],work="V1 layout codec out of scope; pinned mainnet target is V2/V3")
R("L0-D2-014","d2-core",D2+"143","core/primitives/src/reed_solomon.rs; claim-v3 T4",
  "implemented","Reed-Solomon parameters",
  ["D2:143 `rsGenesisParamsOk`; D2:266-270 encoded root recomputation"],tests=["mutant `t.rs_params.reject` (131 in d3c9 summary)"],work="none")
R("L0-D2-015","d2-core",D2+"144","chunk_validation.rs:144-253 (backward walk; no 32-block limit)",
  "partial","c.segment (n_blocks ≤ 32)",
  ["D2:144 `c.blocks.length ≤ 32`", "3 corpus cases with n_blocks=41/41/43 are out of domain (`c.segment`) and nearcore accepts them", "the bound is the arena claim-size budget, not a validator condition (claim-v3 §5)"],
  owner="L1",deps=["L1"],tests=["extend the claim-size budget and replay the 41/43-block cases"],work="arena-format capacity bound; 3 known protocol-valid cases excluded")
R("L0-D2-016","d2-core",D2+"145","spec/claim-v3.md §2.2 (one flag per block)",
  "implemented","epoch_start_after length",
  ["D2:145"],tests=["directed length mutant"],work="none")
R("L0-D2-017","d2-core",D2+"146","spec/claim-v3.md §2.2",
  "implemented","epoch_start_after flag 0/1",
  ["D2:146 `all (·.toNat ≤ 1)`"],tests=["directed flag=2"],work="none")
R("L0-D2-018","d2-core",D2+"149-155","epoch-manager/src/adapter.rs:170-179 (get_epoch_id_from_prev_block)",
  "validated","epoch_start_after vs headers",
  ["D2:149-155", "940 verdicts `invalid: epoch_start_after inconsistent with the headers`"],tests=["mutant `c.epoch_start_flip.reject` (131)"],work="none")
R("L0-D2-019","d2-core",D2+"156","chain/chain/src/runtime/mod.rs:1731-1769 (check_dynamic_resharding); core/primitives/res/epoch_configs/mainnet/85.json (dynamic_resharding_config)",
  "implemented","c.no_split_gate",
  ["D2:156 `applyFacts.all (fun f => f.splitGate.isNone)`", "0 corpus claims carry a split gate (mainnet genesis has dynamic_resharding=true, so gate-open blocks are reachable)", "`ReshardingD3.noSplitGate_iff` + `noResharding_iff_guards` + `splitGate_excludes_nonempty`, plus 8 kernel-decided directed tests", "reachability recorded honestly: version.rs:564 enables DynamicResharding at PV85 and mainnet/85.json sets dynamic_resharding_config, so the gate IS reachable at PV86"],
  owner="L6",deps=["L6"],tests=["var/l6/mut/split_gate_present fires `out of domain (c.no_split_gate)`"],work="legacy-core guard (checkD3Core) only: gate-carrying claims are decided by the signed hand-over and by allFeatures (Successor/TrieSplit transcribes check_dynamic_resharding/find_trie_split); see L0-resharding (validated)")
R("L0-D2-020","d2-core",D2+"158","chunk_validation.rs:321-337 (check_valid_for_config on new_transactions)",
  "implemented","new transaction size",
  ["D2:158 `w.newTxs.all TxD2.sizeOk`"],tests=["mutant `w.new_tx.reject` 112"],work="none")
R("L0-D2-021","d2-core",D2+"160","chunk_validation.rs:144-253 (walk starts at prev block)",
  "implemented","segment starts at prev_block_hash",
  ["D2:160 `hashes.headD [] == H.prevBlockHash`"],tests=["mutant `c.drop_last_block.reject` 131"],work="none")
R("L0-D2-022","d2-core",D2+"161","chunk_validation.rs:229-243 (walk follows prev_hash)",
  "implemented","segment hash-linked",
  ["D2:161-162"],tests=["mutant `c.extra_block.reject` 131"],work="none")
R("L0-D2-023","d2-core",D2+"163","sharding.rs (chunks per block = num shards)",
  "implemented","slot count = num shards",
  ["D2:163"],tests=["mutant `c.slot_height_flip`/`c.slot_inner_flip` 131 each"],work="none")
R("L0-D2-024","d2-core",D2+"166","shard_layout.get_shard_index",
  "implemented","shard in layout",
  ["D2:166"],tests=["directed foreign shard id"],work="none")
R("L0-D2-025","d2-core",D2+"169-171","sharding.rs:460-494 (is_new_chunk; block_congestion_info)",
  "implemented","height_included ≤ block height",
  ["D2:169-171"],tests=["directed height_included above height"],work="none")
R("L0-D2-026","d2-core",D2+"173-174","chunk_validation.rs:144-253",
  "implemented","segment has a new chunk",
  ["D2:173-174"],tests=["directed no-new-chunk segment"],work="none")
R("L0-D2-027","d2-core",D2+"176","chunk_validation.rs:403-413 (MainTransition::Genesis); genesis.rs:218-257 (genesis_chunk_extra)",
  "validated","c.not_genesis",
  ["D2:176 `!B2.isGenesis`", "137 corpus cases (39/60/19/19) have a genesis B2 and nearcore accepts them; baseline Lean returned out of domain", "successor checker `NearSpecV3.checkD3G` (GenesisD3.lean) models MainTransition::Genesis: 137/137 accept, matching meta.json expected_rel; non-genesis verdicts byte-identical to baseline over all 115,147 cases", "16 directed negatives each fire their intended error"],
  owner="L6",deps=["L6","L9"],tests=["var/l6/genesis-cases.txt replayed through nearspec-v3-check-d3g; var/l6/mut-results2.jsonl"],work="non-genesis delegation argued by construction and measured over 115,284 cases but not proved as a rewrite theorem; txValid.all untested (no genesis corpus case carries a transaction)")
R("L0-D2-028","d2-core",D2+"177","claim-v3 T14 (genesis_chunk_extra Some iff B2 genesis)",
  "implemented","genesis_chunk_extra for non-genesis",
  ["D2:177 `c.genesisChunkExtra.isNone`"],tests=["directed Some on non-genesis B2"],work="none")
R("L0-D2-029","d2-core",D2+"179-181","chunk_validation.rs:144-253 (exactly the blocks the walk reads)",
  "validated","segment = walk",
  ["D2:179-181", "940 `segment does not reach the last-but-one new chunk` + 892 `segment is not exactly the blocks the validator reads` verdicts"],tests=["mutants c.drop_last_block/c.extra_block"],work="none")
R("L0-D2-030","d2-core",D2+"184","spec/claim-v3.md §2.3 (one ApplyFacts per applied block)",
  "implemented","apply_facts length",
  ["D2:184"],tests=["directed wrong apply_facts length"],work="none")
R("L0-D2-031","d2-core",D2+"186-189","claim-v3 T10 (validator_update Some iff epoch start)",
  "implemented","validator_update presence",
  ["D2:186-189"],tests=["directed missing/extra validator_update"],work="none")
R("L0-D2-032","d2-core",D2+"202-205","sharding.rs:963-990 (ReceiptProof::verify_against_receipt_root)",
  "validated","source receipt proof (lookup/from/to/merkle path)",
  ["D2:202-205", "940 missing proof, 636 to_shard, 1244 merkle path verdicts"],tests=["mutants w.corrupt_proof/w.drop_proof/w.extra_proof"],work="none")
R("L0-D2-033","d2-core",D2+"210","core/primitives/src/utils.rs (shuffle_with_seed)",
  "implemented","shuffle fuel",
  ["D2:210"],tests=["directed shuffle exhaustion (probability < 2^-1024)"],work="none")
R("L0-D2-034","d2-core",D2+"213","chunk_validation.rs:449-470 (source_receipt_proofs exact set)",
  "validated","no extra proofs",
  ["D2:213", "940 `source_receipt_proofs contains extra proofs`"],tests=["mutant w.extra_proof"],work="none")
R("L0-D2-035","d2-core",D2+"214","chunk_validation.rs:349-355 (applied receipts hash)",
  "validated","applied receipts hash",
  ["D2:214", "940 `invalid: applied receipts hash`"],tests=["mutant w.applied_receipts_hash.reject 131"],work="none")
R("L0-D2-036","d2-core",D2+"216","chunk_validation.rs:372-380 (transaction root)",
  "validated","tx root of the last chunk",
  ["D2:216", "2043 `transaction root of the last chunk`"],tests=["mutant w.tx.reject 387"],work="none")
R("L0-D2-037","d2-core",D2+"217","claim-v3 T13 (tx_valid length)",
  "implemented","tx_valid length",
  ["D2:217"],tests=["mutant t.tx_valid_flip 261"],work="none")
R("L0-D2-038","d2-core",D2+"220-221","bandwidth_scheduler (calculate params; assert panics)",
  "implemented","scheduler params",
  ["D2:220-221", "BandwidthScheduler.lean"],deps=["L1"],tests=["directed numShards/epoch outside scheduler table"],work="capacity bound; scheduler table coverage is finite")
R("L0-D2-039","d2-core",D2+"230","Trie::from_recorded_storage (chunk_validation.rs:709; store trie/mod.rs:715-735)",
  "implemented","main base_state hashes to prev_state_root",
  ["D2:230 `tMain.hashOf == slotB2.prevStateRoot`"],tests=["mutant w.base_state.reject 131"],work="none")
R("L0-D2-040","d2-core",D2+"235-237","runtime/runtime/src/lib.rs:838-845; runtime/near-vm-runner/src/logic/recorded_storage_counter.rs:27; 69.yaml per_receipt_storage_proof_size_limit=4_000_000",
  "partial","w.size (storage-proof upper bound)",
  ["D2:235-237 `baseBytes + 2000 * out.cdRemovals ≤ 4000000`", "doc marks the inequality unverified in the presence of contract-storage removals (spec/near-chunk-validation-d3.md §10)", "PV86 enforces the per-receipt limit (EnforcePerReceiptStorageProofLimit=86, version.rs:576)"],
  owner="L5",deps=["L5","L7"],tests=["construct a chunk where a receipt's recorded-size delta exceeds Σ values + 2000R but stays under 4e6"],work="prove or replace the chunk-level bound; the per-receipt limit is the real boundary")
R("L0-D2-041","d2-core",D2+"240","arity: G_alpha is a prover cap, not a nearcore condition (D3/FunctionCall.lean:389)",
  "partial","e.g_alpha",
  ["D2:240 `out.wasmGas ≤ cap`", "846 exact `e.g_alpha` verdicts; 1,010 oracle-tagged cases; all nearcore-accepted"],deps=["L1"],tests=["raise the cap and replay; compare with nearcore"],work="capacity choice; 1,010 protocol-valid chunks excluded")
R("L0-D2-042","d2-core",D2+"242","chunk_validation.rs:623-632 (post state root early check)",
  "validated","main post state root",
  ["D2:242", "2832 `main transition post state root`"],tests=["mutant w.main_post_root.reject 131"],work="none")
R("L0-D2-043","d2-core",D2+"244","chunk_validation.rs:565-660 (implicit transitions)",
  "validated","implicit transitions count",
  ["D2:244", "85 `implicit transitions count`"],tests=["mutant w.implicit.reject 33"],work="none")
R("L0-D2-044","d2-core",D2+"252","chunk_validation.rs:565-660",
  "validated","implicit transition post root",
  ["D2:252", "85 `implicit transition post state root`"],tests=["mutant w.implicit.reject 33"],work="none")
R("L0-D2-045","d2-core",D2+"254","chunk_validation.rs:648-660 (invalid state root)",
  "validated","InvalidStateRoot",
  ["D2:254", "940 verdicts"],tests=["mutant hdr.prev_state_root.reject 131"],work="none")
R("L0-D2-046","d2-core",D2+"255","chunk_validation.rs:648-660 (outcome root)",
  "validated","InvalidOutcomesProof",
  ["D2:255", "954 verdicts"],tests=["mutant hdr.prev_outcome_root.reject 131"],work="none")
R("L0-D2-047","d2-core",D2+"256","chunk_validation.rs:648-660 (proposals)",
  "validated","InvalidValidatorProposals",
  ["D2:256", "958 verdicts"],tests=["mutant hdr.proposals.reject 129"],work="none")
R("L0-D2-048","d2-core",D2+"257","chunk_validation.rs:648-660 (gas limit)",
  "validated","InvalidGasLimit",
  ["D2:257", "940 verdicts"],tests=["mutant hdr.gas_limit.reject 131"],work="none")
R("L0-D2-049","d2-core",D2+"258","chunk_validation.rs:648-660 (gas used)",
  "validated","InvalidGasUsed",
  ["D2:258", "940 verdicts"],tests=["mutant hdr.prev_gas_used.reject 131"],work="none")
R("L0-D2-050","d2-core",D2+"259","chunk_validation.rs:648-660 (balance burnt)",
  "validated","InvalidBalanceBurnt",
  ["D2:259", "940 verdicts"],tests=["mutant hdr.prev_balance_burnt.reject 131"],work="none")
R("L0-D2-051","d2-core",D2+"260","chunk_validation.rs:648-660 (outgoing receipts root)",
  "validated","InvalidReceiptsProof",
  ["D2:260", "940 verdicts"],tests=["mutant hdr.prev_outgoing_receipts_root.reject 131"],work="none")
R("L0-D2-052","d2-core",D2+"261","chunk_validation.rs:648-660 (congestion info)",
  "validated","InvalidCongestionInfo",
  ["D2:261", "3108 verdicts"],tests=["mutant hdr.congestion.reject 387"],work="none")
R("L0-D2-053","d2-core",D2+"262","chunk_validation.rs:648-660 (bandwidth requests)",
  "validated","InvalidBandwidthRequests",
  ["D2:262", "930 verdicts"],tests=["mutant hdr.bandwidth_requests.reject 129"],work="none")
R("L0-D2-054","d2-core",D2+"263","chunk_validation.rs:648-660 (proposed split)",
  "validated","InvalidChunkHeaderShardSplit",
  ["D2:263", "922 verdicts"],tests=["mutant hdr.proposed_split.reject 129"],work="none")
R("L0-D2-055","d2-core",D2+"264","chunk_validation.rs:648-660 (tx root)",
  "validated","InvalidTxRoot",
  ["D2:264", "1721 verdicts"],tests=["mutant hdr.tx_root.reject 131"],work="none")
R("L0-D2-056","d2-core",D2+"266-270","chunk_validation.rs:648-660 (encoded merkle root / length)",
  "validated","InvalidChunkEncodedMerkleRoot / InvalidChunkEncodedLength",
  ["D2:266-270", "1880 + 940 verdicts"],tests=["mutant hdr.encoded_merkle_root/encoded_length 131 each"],work="none")
R("L0-D2-057","d2-core",D2+"54-67","chain store witness decode; state_witness.rs:21 (64 MiB transport)",
  "implemented","decode: witness size/tag/trailing bytes",
  ["D2:54-67 (decodeStateWitnessD2)","940 `decode: Not all bytes read`"],tests=["directed trailing byte / wrong tag"],work="none")
R("L0-D2-058","d2-core",D2+"149-155 (epoch_start_after)","epoch-manager adapter",
  "validated","epoch_start_after consistency (genesis flag)",
  ["D2:153 `!b.isGenesis || f.toNat == 1`"],tests=["mutant c.epoch_start_flip"],work="none")

# ---------------------------------------------------------------- D3 hook
D3 = "spec/lean/v3/NearSpecV3/D3/FunctionCall.lean:"
R("L0-D3-001","d3-hook",D3+"51-65; Wasm/Exec.lean:62-78","runtime/near-vm-runner/src/imports.rs:95-380 (host table); spec/near-chunk-validation-d3.md §10.0a P3",
  "validated","e.ood_host (called only)",
  ["`realOodHosts` gate is in `callHost` (Exec.lean:72) and fires only on a call; importing is in-domain","curve functions are absent from `hostCall`; a call becomes `unmodeled ... not modelled` and OOD","480 oracle-tagged cases: 244 curve calls, 214 state-init/global/gas-key calls; 192 import-only cases are accepted"],
  deps=["L3","L4"],tests=["import-only case d3c7/d3/00-h10027-s2 (accept)","calling ecrecover d3c9/ood/00-h10006-s2 (OOD)"],work="called-vs-imported semantics correct; close the families in L3/L4")
R("L0-D3-002","d3-hook",D3+"62-69","prepare_v3.rs:397-470",
  "validated","contractOOD float/prepare",
  ["D3:62-69 `contractOOD` maps `.outOfDomain`/`.unmodeled` to OOD; `.prepErr`/`.compileErr` stay in-domain","150 exact float OOD verdicts"],deps=["L2"],tests=["d3float contract cases"],work="floats are a real PV86 feature; see UQ-003")
R("L0-D3-003","d3-hook",D3+"71","spec/near-chunk-validation-d3.md §10.1",
  "implemented","e.wasm-alpha wrapper",
  ["D3:71 `oodE why = \"out of domain (e.wasm-α): ...\"`"],tests=["reason-prefix assertions"],work="cosmetic double `unmodeled unmodeled` prefix for curve calls (lineOutcome + wrapper)")
R("L0-D3-004","d3-hook",D3+"232","runtime/runtime/src/actions.rs (FunctionCall arm)",
  "implemented","hook on non-FunctionCall",
  ["D3:232"],tests=["internal invariant only"],work="none")
R("L0-D3-005","d3-hook",D3+"233","runtime/runtime/src/lib.rs:631-668 (EXPECT_ACCOUNT_EXISTS)",
  "implemented","EXPECT_ACCOUNT_EXISTS",
  ["D3:233"],tests=["directed missing account at dispatch"],work="none")
R("L0-D3-006","d3-hook",D3+"236-239","runtime/runtime/src/contract_code.rs:56-76 (LegacyEthWallet / EthImplicitGlobalContract); runtime/near-wallet-contract/src/lib.rs:37-52,89-124",
  "partial","e.eth_implicit_local",
  ["D3:236-239 conservatively OOD","209 exact verdicts; the resolution is deterministic given chain_id (`eth_wallet_global_contract_hash`, lib.rs:89-105)",
   "modelled: `Rci.resolve` (D3/GlobalContract.lean §6) returns `.global (ethWalletHash chainId)` for a wallet magic hash, `.accountLocal h` otherwise; `ethWalletHash`/`walletMagicHash` recomputed from the four pinned res/*.wasm blobs and kept distinct",
   "PROVEN BLOCKER: the delegate cannot lift this guard. `resolvedContract` only ever yields `.none`/`.local _` (`resolvedContract_local_stays_local`), and D3:236-239 rejects every `.local _` on an ETH-implicit receiver, so `guardPremise` survives the delegate (`resolveAccount_eth_local_premise_survives`). Lifting needs an edit to that guard (a `checkD3`-adjacent change), not a delegate",
   "measured on all 539 d3c7-d3c10 OOD cases whose d3_violations contain e.eth_implicit_local or w.shape: the resolving successor `checkD3Global` returns the identical verdict and reason for all 539 (0 differences); 0 of 1,455 decoded accounts in those witnesses carry a wallet magic hash, so no corpus case exercises the redirect"],
  owner="L4",deps=["L4"],tests=["hand-built successor case with a wallet magic hash on an ETH-implicit receiver (needs the guard parametrised, blocked by additive-only)"],
  work="parametrise D3:236-239's guard (off by default so checkD3 is unchanged) and replay a wallet-magic-hash witness; a delegate alone cannot reach the wallet branch")
R("L0-D3-007","d3-hook",D3+"243","runtime/runtime/src/function_call.rs:49-54 (amount + deposit overflow)",
  "implemented","account balance overflow",
  ["D3:243 `acct.amount + deposit ≥ 2^128`"],tests=["directed u128 overflow deposit"],work="none")
R("L0-D3-008","d3-hook",D3+"248","runtime/runtime/src/contract_code.rs:39-95 (RuntimeContractIdentifier::resolve); trie_key.rs:133-143 (kGlobalContractCode)",
  "partial","w.shape global contract identifier",
  ["D3:248 `_ => throw \"out of domain (w.shape): global contract identifier\"`",
   "CORRECTION to the earlier evidence: the 89 `w.shape: UseGlobalContract action` verdicts come from the ACTION decoder (`D2/Types.lean:301`, `oodUseGlobal`), not from D3:248; D3:248 needs an account whose `Contract` is `.global`/`.byAccount`, and 0 of 1,455 decoded accounts in all 539 OOD cases have one",
   "implemented additively: `functionCallResolved` rewrites `.global h` -> `.local h` and `.byAccount id` -> `.local` (sha256 of the `kGlobalContractCode` trie value, column 18), so D3:248's global/byAccount arm is unreachable behind it (`resolvedContract_local_of_global`, `resolvedContract_local_of_byAccount`); a missing identifier value is `invalid: StorageInconsistentState` (contract_code.rs:107-116)",
   "not exercised end to end: no corpus case reaches D3:248 (the action decoder fires first), and no whole-chunk case with a global-contract receiver could be generated without changing oracle/v3-d3 (pinned, off-limits)",
   "measured: `checkD3Global` vs `checkD3` agree on all 300 sampled accepted chunks and all 539 OOD cases"],
  owner="L4",deps=["L4"],tests=["hand-built witness whose receiver's account carries a `.global` contract and whose code blob is present (needs an oracle or hand-encoder path)"],
  work="whole-chunk case with a global-contract receiver; the delegate closes D3:248 but no witness exercises it")
R("L0-D3-009","d3-hook",D3+"252-275","runtime/runtime/src/contract.rs:104-131; contract.rs:42-69 (ContractsTracker); function_call.rs:355-393",
  "partial","e.code_cache",
  ["D3:252-275: no witness blob + pre-state hash => OOD if the same code was ever deployed in-chunk; else MissingTrieValue","279 exact OOD verdicts; cold validator accepts 169 and rejects 110","the rule does not distinguish committed from rolled-back deploys: a committed deploy is served deterministically by `ContractsTracker` (contract.rs:104-131), so the 169 cold-accept cases are protocol-valid witnesses excluded by the relation"],
  owner="L1",deps=["L1","L7"],tests=["split the 279 cases by committed vs rolled-back deploy; replay cold validator"],work="narrow e.code_cache to rolled-back deploys only; see UQ-008")
R("L0-D3-010","d3-hook",D3+"272,275","runtime/runtime/src/function_call.rs:293-305 (MissingTrieValue)",
  "validated","MissingTrieValue (contract code)",
  ["D3:272/275","14,246 `invalid: MissingTrieValue (contract code)` verdicts"],tests=["mutant code.drop.reject 662","mutant code.none.reject 150"],work="none")
R("L0-D3-011","d3-hook",D3+"268-275","runtime/runtime/src/contract.rs:42-69 (deploy tracker)",
  "implemented","codeAvailable (in-chunk deploy)",
  ["D3:268-275"],tests=["ran.d3program.deployed_in_chunk 19 / d3rich 85 / d3tiny 195"],work="none")
R("L0-D3-012","d3-hook",D3+"153,176,219,328,367","oracle/v3-d3/src/d3.rs (mock action log)",
  "implemented","unmodeled action log entries => OOD",
  ["D3:153/176/219/328/367","representation gap for any action tag the mock log does not describe; never observed as a refusal in the 115,284-case run"],deps=["L4"],tests=["directed new manager tag"],work="extend the action log or replace it with a real ReceiptManager model")
R("L0-D3-013","d3-hook",D3+"218-219","runtime/runtime/src/actions.rs (NewReceiptValidationError)",
  "implemented","action re-encoding / shape OOD",
  ["D3:218-219"],tests=["mutant w.new_tx.reject 112"],work="none")
R("L0-D3-014","d3-hook",D3+"356","runtime/runtime/src/function_call.rs:100-142 (promise_return)",
  "implemented","promise_return of a non-receipt",
  ["D3:356"],tests=["directed promise_return of a yield/log entry"],work="none")
R("L0-D3-015","d3-hook",D3+"339-341","runtime/runtime/src/function_call.rs:154-222 (yield timeout)",
  "implemented","yield indices overflow",
  ["D3:339-341"],tests=["directed 2^64-1 yields"],work="none")
R("L0-D3-016","d3-hook",D3+"192-211","runtime/runtime/src/receipt_manager.rs:654-695 (distribute_unused_gas)",
  "implemented","gas distribution overflow",
  ["D3:192-211"],tests=["directed large weighted unused gas"],work="none")
R("L0-D3-017","d3-hook",D3+"400","near/pv86/chunk-validation/v0 statement",
  "validated","checkD3 wiring (allowCodes=true, gasCap=gAlpha)",
  ["D3:400 `checkD2Core (d3Hooks Wasm.pv86) true ... (some gAlpha)`"],tests=["115,284-case run, 0 disagreements"],work="none")

# ---------------------------------------------------------------- WASM guards
W = "spec/lean/v3/NearSpecV3/Wasm/"
R("L0-W-001","wasm-prepare",W+"Prepare.lean:205","runtime/near-vm-runner/src/prepare/prepare_v3.rs:303-333 (transform_import_section)",
  "missing","float in an imported function type",
  ["Prepare.lean:205 `.ood \"float in an imported function type\"`","PV86 wasmparser features include floats and saturating_float_to_int (features.rs:47-59)"],
  owner="L2",deps=["L2"],tests=["contract importing a float-signature function, never calling it"],work="implement floats or prove the import-only case harmless")
R("L0-W-002","wasm-prepare",W+"Prepare.lean:234","runtime/near-vm-runner/src/prepare/prepare_v3.rs (global section)",
  "missing","float global",
  ["Prepare.lean:234 `.ood \"float global\"`"],owner="L2",deps=["L2"],tests=["contract with an f64 global"],work="L2")
R("L0-W-003","wasm-prepare",W+"Prepare.lean:315","prepare_v3.rs:397-470 (validate_contract); finite-wasm",
  "missing","float type or operator in a function body",
  ["Prepare.lean:315", "150 exact float OOD verdicts (d3float contract)"],owner="L2",deps=["L2"],tests=["d3float run/cb"],work="float semantics incl. NaN determinism (H3)")
R("L0-W-004","wasm-prepare",W+"Prepare.lean:392","prepare.rs:22-33",
  "validated","prepare result dispatch",
  ["Prepare.lean:392-397 (`.prepErr` / `.outOfDomain` / `.unmodeled`)"],tests=["cleanroom prepare vectors (oracle/wasm-d3)"],work="none")
R("L0-W-005","wasm-prepare",W+"Prepare.lean:178-390","runtime/near-vm-runner/src/logic/errors.rs:166-211 (PrepareError variants)",
  "implemented","PrepareError limits (types/functions/locals/tables/table elements/body size/blocks/params/stack/instrumented size)",
  ["Prepare.lean prepFail sites: TooManyTypes, TooManyFunctions, TooManyLocals, TooManyTables, TooManyTableElements, FunctionBodyTooLarge, InstrumentedCodeTooLarge, TooManyBlocksPerFunction/Contract, TooManyParamsPerFunction/Contract, OperandStackTooLarge, Instantiate, Memory"],tests=["corpus fail.FunctionCallError:CompilationError classes (23 CodeDoesNotExist; MethodResolve 82)"],work="none")
R("L0-W-006","wasm-prepare",W+"Prepare.lean:455-472","runtime/near-vm-runner/src/wasmtime_runner/mod.rs:571-580 (WasmtimeCompileError)",
  "implemented","compileErr (instrumented locals/body size)",
  ["Prepare.lean:455-472 (H1: params+locals 49,999/50,000)"],tests=["directed boundary function"],work="none")
R("L0-W-007","wasm-prepare",W+"Prepare.lean:478-490","runtime/near-vm-runner/src/wasmtime_runner/mod.rs:1127-1155 (link)",
  "validated","LinkError unknown import / signature",
  ["Prepare.lean:478-490; HostSigs.lean:13-106 (89 PV86 signatures)"],tests=["corpus LinkError cases"],work="none")
R("L0-W-008","wasm-prepare",W+"Prepare.lean:492-500","runtime/near-vm-runner/src/wasmtime_runner/mod.rs:887-902 (resolve)",
  "validated","MethodResolveError (empty/not found/invalid signature)",
  ["Prepare.lean:492-500; Host.lean / runCall nop lines","d3c9 summary: MethodNotFound 59, MethodInvalidSignature 23"],tests=["mutant methods"],work="none")
R("L0-W-009","wasm-exec",W+"Exec.lean:446-471","runtime/near-vm-runner/src/wasmtime_runner/mod.rs:744-784",
  "implemented","contract loading gas",
  ["Exec.lean:468-470 `payPerC.contractLoadingBytes`/`contractLoadingBase`"],tests=["directed loading-gas exhaustion"],work="none")
R("L0-W-010","wasm-exec",W+"Exec.lean:60-78","runtime/near-vm-runner/src/imports.rs (host dispatch)",
  "validated","called vs imported host gate",
  ["Exec.lean:72 `if s.real.isSome && realOodHosts.contains name`","Exec.lean:462-464 `if real.isNone && curve imports` (harness only)","hostCall covers 75 names; the 14 curve names are intentionally absent"],tests=["192 import-only cases: 167 accept, 25 OOD for an unrelated guard, 0 reject"],work="none (trap resolved: exclusion is call-triggered under RuntimeD3)")
R("L0-W-011","wasm-exec",W+"Exec.lean:14-352","Wasm/Machine.lean (invariants)",
  "implemented","unmodeled WASM invariants",
  ["Exec.lean:14,18,39,51,75,82,169,186,190,210,324,338,341,344,352"],tests=["never hit in 115,284 cases"],work="none; internal invariants")
R("L0-W-012","wasm-exec",W+"Exec.lean:325; Validate.lean:270,293; FiniteWasm.lean:132",
  "runtime/near-vm-runner/src/prepare/prepare_v3.rs (float checks)",
  "missing","float operator (interpreter/validator/analyzer)",
  ["four float sites; unreachable once Prepare rejects floats"],owner="L2",deps=["L2"],tests=["after L2 lifts prepare, exercise each site"],work="L2")
R("L0-W-013","wasm-exec",W+"Host.lean:406,423,437","mock/external contract",
  "implemented","host arity / real store missing",
  ["Host.lean:406 `popArgs`","Host.lean:423/437 `unmodeled: real store`"],tests=["internal invariants"],work="none")
R("L0-W-014","wasm-exec",W+"TrieStore.lean:97; ChunkStorage.lean:76","core/store/src/trie/mod.rs (lookup)",
  "implemented","lookup fuel / real store lost",
  ["TrieStore.lean:97","ChunkStorage.lean:76"],tests=["never hit in 115,284 cases"],work="none")
R("L0-W-015","wasm-exec",W+"Exec.lean:430-434","runtime/near-vm-runner/src/imports.rs:354-368 (curve host table)",
  "missing","curve host functions",
  ["`curveHosts` 14 names; `hostCall` has none; call => `unmodeled ... not modelled` => OOD","244 exact verdicts"],owner="L3",deps=["L3"],tests=["replay d3curve run/cb"],work="implement alt_bn128/BLS12-381/ecrecover/p256_verify")
R("L0-W-016","wasm-domain","spec/lean/v3/NearSpecV3/ReshardingD3.lean:80","chunk_validation.rs:258-308 (get_resharding_transition)",
  "partial","noResharding (stated predicate)",
  ["ReshardingD3.lean:80 `noResharding`; `noResharding_spec`","not called by checkD3; the legacy core checkD2Core enforces its own c.same_layout/c.no_split_gate"],owner="L1",deps=["L1"],tests=["prove `checkD3 => noResharding` or delete the duplicate"],work="wire or remove the parallel predicate (UQ-010)")
R("L0-W-017","wasm-domain","spec/lean/v3/NearSpecV3/Wasm/Exec.lean (runCall call gate)","prepare_v3.rs (imports)",
  "partial","contractInD3α (stated predicate)",
  ["`contractInD3α` checked curve *imports*; the checker deliberately allows imports (P3)","not called by checkD3"],owner="L1",deps=["L1"],tests=["import-only curve case: contractInD3α=false but checkD3 accepts"],work="the stated predicate is stricter than the implementation; reconcile (UQ-010)")
R("L0-W-018","wasm-domain",W+"Syntax.lean:9,67","runtime/near-vm-runner/src/features.rs:47-102",
  "implemented","float syntax (decoder only)",
  ["Syntax.lean:9/67 floats parsed only to be rejected"],owner="L2",deps=["L2"],tests=["decode f32/f64"],work="L2")

# ---------------------------------------------------------------- lane boundary rows
R("L0-LANE-001","layer-boundary","spec/lean/v3/NearSpecV3/D2/Actions.lean:88","runtime/runtime/src/lib.rs:631-668",
  "implemented","e.wasm (D2 only)",
  ["D2 hook returns OOD on FunctionCall dispatch","lifted by D3 (checkD3 uses d3Hooks)"],tests=["D2 67,384/67,384"],work="none")
R("L0-LANE-002","layer-boundary","spec/lean/v3/NearSpecV3/D2/Actions.lean:399","core/crypto/src/signature.rs:250-257 (SECP256K1); core/primitives/src/signature.rs",
  "missing","e.secp",
  ["D2/Actions.lean:399 `SECP256K1 delegate signature verification`","38 exact verdicts; secp256k1 keys are live at PV86"],owner="L3",deps=["L3"],tests=["replay a secp Delegate case"],work="implement secp256k1 verification")
R("L0-LANE-003","layer-boundary","spec/lean/v3/NearSpecV3/D2/Types.lean:34-39,46","core/crypto/src/signature.rs:250-257 (MLDSA65); core/primitives-core/src/version.rs:414,567; 85.yaml ml_dsa_65_verification_cost",
  "missing","w.shape ML-DSA-65 keys",
  ["Types.lean:34/35/46","260 exact `ML-DSA-65 public key` verdicts + 79 `non-ED25519 transaction key`","PostQuantumSignatures enabled at 85"],owner="L3",deps=["L3"],tests=["ML-DSA AddKey/Stake/DeleteKey and tx signature"],work="implement ML-DSA-65 keys and signatures")
R("L0-LANE-004","layer-boundary","spec/lean/v3/NearSpecV3/D2/Types.lean:36-39,300-302","core/primitives/src/action/mod.rs:349-370 (tags 9-11); version.rs:553-562",
  "missing","w.shape global/state-init/gas-key",
  ["Types.lean:36-38 and 300-302","89 UseGlobalContract + state-init/gas-key OOD verdicts; live at PV83/85"],owner="L4",deps=["L4"],tests=["replay DeployGlobal/UseGlobal/StateInit"],work="implement the action families and GlobalContractDistribution receipts")
R("L0-LANE-005","layer-boundary","spec/lean/v3/NearSpecV3/D2/TxD2.lean:46,59","core/crypto/src/signature.rs:43-90 (KeyType ED25519/SECP256K1/MLDSA65)",
  "missing","w.shape non-ED25519 transaction key/signature",
  ["TxD2.lean:46/59","79 `non-ED25519 transaction key` verdicts"],owner="L3",deps=["L3"],tests=["secp/ML-DSA transaction"],work="L3")
R("L0-LANE-006","layer-boundary","spec/lean/v3/NearSpecV3/D2/Queues.lean:327","shard layout (outgoing buffer routing)",
  "implemented","c.same_layout outgoing buffer",
  ["D2/Queues.lean:327"],owner="L6",deps=["L6"],tests=["after resharding corpus"],work="resharding only")
R("L0-LANE-007","layer-boundary","spec/lean/v3/NearSpecV3/D2/Receipts.lean:29","nearcore receipt decoding",
  "implemented","receipt shape (isShapeOOD / inconsistent)",
  ["D2/Receipts.lean:29"],tests=["receipt mutants"],work="none")
R("L0-LANE-008","layer-boundary","spec/lean/v3/NearSpecV3/ChunkValidationD1.lean:63-189","D1 statement",
  "implemented","D1 guards (c.single_epoch, c.own_congestion_zero, base_state 3 MB, e.distinct_ids, r.*, e.*)",
  ["D1:71,80,88,106,145,148,159; all lifted or superseded by D2","D1 corpus 53,048 cases"],tests=["D1 53,048-case run"],work="none for D3; D1 retained as a rung")
R("L0-LANE-009","layer-boundary","spec/lean/v3/NearSpecV3/ChunkValidationV0.lean:105-192","D0 statement",
  "implemented","D0 guards (w.no_code, w.no_txs, c.no_tx_flags, c.single_epoch, c.own_congestion_zero, r.shape/success)",
  ["V0:105-192"],tests=["D0 corpus"],work="none for D3")
R("L0-LANE-010","layer-boundary","spec/lean/v3/NearSpecV3/ChunkValidationD1a.lean:200-208","D1a amendments",
  "partial","D1a amendments (gas limit, proof routing, sched canonical, unfolded bytes, bw requests, ChaCha words, path depth, layout wf, tx count)",
  ["D1a:200-208; none of these checks is called by checkD2Core/checkD3","D2 spec §12 says D2 lifts/changes most D1a conditions; `c.gas_limit` and `w.tx_count` are capacity bounds, `canon0f` is subsumed by the full trie model"],owner="L7",deps=["L7"],tests=["discriminating case for each amendment in D3"],work="prove each is subsumed or port it")
R("L0-LANE-011","layer-boundary","spec/lean/v3/NearSpecV3/Layout.lean:65","ShardLayout borsh V2/V3",
  "implemented","c.layout codec",
  ["Layout.lean:65 rejects non-V2/V3"],owner="L1",deps=["L1"],tests=["V1/V0 layout claim"],work="pinned mainnet target is V2/V3; document")
R("L0-LANE-012","layer-boundary","spec/lean/v3/NearSpecV3/Wire.lean:288","BlockHeader V6",
  "implemented","c.headers V6",
  ["Wire.lean:288 `block header is not V6`","PV86 produces V6; unreachable for an honest claim"],tests=["V5 header claim"],work="none at target")

# ---------------------------------------------------------------- claim facts (trusted)
R("L0-CLAIM-001","claim-fact","spec/claim-v3.md §2.4 T3; ChunkValidationD2.lean:117","nearcore judge reads chain_id from genesis config",
  "impossible-at-boundary","chain_id (trusted)",
  ["claim-v3 T3: trusted; `Rel` cannot authenticate it","read by D2 ETH-implicit creation and D3 contract resolution / chain_id host fn"],
  owner="L8",deps=["L8"],tests=["arena admission must bind chain_id to the verifier's genesis config"],work="admission-time binding, not Rel")
R("L0-CLAIM-002","claim-fact","spec/claim-v3.md §2.4 T8; ChunkValidationD2.lean:100-107","D3 VMContext validators (fc.rs:252-281)",
  "impossible-at-boundary","epochs[e].validators (trusted)",
  ["used by validator_stake / validator_total_stake host functions","no hash in the claim determines it"],owner="L8",deps=["L8"],tests=["bind to epoch manager at admission"],work="L8")
R("L0-CLAIM-003","claim-fact","spec/claim-v3.md §2.4 T11; D2/Actions.lean (Stake)","EpochInfoProvider::minimum_stake",
  "impossible-at-boundary","apply_facts.minimum_stake (trusted)",
  ["D2:101-107 env carries minimumStake","only internal consistency is checked"],owner="L8",deps=["L8"],tests=["bind to epoch manager"],work="L8")
R("L0-CLAIM-004","claim-fact","spec/claim-v3.md §2.4 T13; ChunkValidationD2.lean:217","chain store check_transaction_validity_period",
  "impossible-at-boundary","tx_valid (trusted)",
  ["only length-checked (D2:217); a false flag changes which txs apply"],owner="L8",deps=["L8"],tests=["bind to the verifier's chain store / tx validity period"],work="L8")
R("L0-CLAIM-005","claim-fact","spec/claim-v3.md §2.4 T4; ChunkValidationD2.lean:143,266","genesis epoch config num_data_parts/num_total_parts",
  "impossible-at-boundary","rs_data_parts/rs_total_parts (trusted)",
  ["only internal consistency and the encoded root are checked"],owner="L8",deps=["L8"],tests=["bind to genesis epoch config"],work="L8")
R("L0-CLAIM-006","claim-fact","spec/claim-v3.md §2.4 T12; ChunkValidationD2.lean:156","dynamic-resharding config / can_reshard",
  "impossible-at-boundary","apply_facts.split_gate (trusted)",
  ["the relation requires None; the truth of None is a claim fact"],owner="L8",deps=["L8","L6"],tests=["bind to epoch manager"],work="L8 + L6")
R("L0-CLAIM-007","claim-fact","spec/claim-v3.md §2.4 T10; ChunkValidationD2.lean:186-189","compute_stake_return_info",
  "impossible-at-boundary","validator_update contents (trusted)",
  ["presence is checked against epoch_start_after; contents are trusted"],owner="L8",deps=["L8"],tests=["bind to epoch manager"],work="L8")
R("L0-CLAIM-008","claim-fact","spec/claim-v3.md §2.4 T14; ChunkValidationD2.lean:177","Chain::genesis_chunk_extra",
  "impossible-at-boundary","genesis_chunk_extra (trusted)",
  ["Some iff B2 genesis is checked; bytes are trusted (and the genesis path is OOD)"],owner="L8",deps=["L8","L9"],tests=["bind to the chain store"],work="L8 + L9")

# ---------------------------------------------------------------- acceptance/regression rows
R("L0-EVID-001","evidence","spec/lean/v3/NearSpecV3/D3/FunctionCall.lean:400","nearcore 44f7ae6, PV86",
  "validated","D3 whole-corpus agreement",
  ["115,284 cases, 0 disagreements: report-d3-full.json","per corpus 33,248 / 49,490 / 15,995 / 16,551","verdicts accept 41,131 / reject 71,605 / out_of_domain 2,548","checker sha256 b4154b212fc482af99fafd4a1c4d5cf6b1157f4e26c154fc1a66e907312ce5d8"],tests=["re-run difftest_d3.py on all four corpora"],work="none; carried-forward evidence, not re-run by L0")
R("L0-EVID-002","evidence","spec/lean/v3/NearSpecV3/ChunkValidationD2.lean:272","nearcore 44f7ae6, PV86",
  "validated","D2 regression",
  ["D2 67,384/67,384, 0 disagreements"],tests=["D2 difftest"],work="none")
R("L0-EVID-004","evidence","docs/research/lean-chunk-coverage-gen.py (claim scan)","claim-v3 §2.2 EpochRec.shard_layout; chunk_validation.rs:258-308",
  "validated","no resharding case exists in the corpus",
  ["decoded all 115,284 claim.bin files: epoch count distribution 1/2/3/4 = 114,431 / 850 / 1 / 2 (sums to 115,284); every claim with >1 epoch has byte-identical shard layouts","0 of 115,284 claims carry a split gate","n_blocks distribution: max 43; 3 claims exceed 32"],
  tests=["scan script is deterministic and re-runnable; see generation command"],work="none; this is the negative evidence behind UQ-008")
R("L0-EVID-003","evidence","spec/lean/v3/NearSpecV3/ChunkValidationD1.lean:44","nearcore 44f7ae6, PV86",
  "validated","D1 regression",
  ["D1 53,048 cases"],tests=["D1 difftest"],work="none")

# ---------------------------------------------------------------- oracle marks
ORACLE = [
 ("c.no_resharding", [("d3c7",333),("d3c8",495),("d3c9",159),("d3c10",140)], 1127,
  "near/pv86/chunk-validation/v0#D3 `c.no_resharding`",
  ["ChunkValidationD2.lean:140 `out of domain (c.same_layout): resharding`",
   "ChunkValidationD2.lean:156 `out of domain (c.no_split_gate)`"],
  "mapped-with-defect",
  "1,127 claims carry the tag. A full claim scan shows none has two different shard layouts and none has a split gate; 274 have a single epoch, 850 have two epochs with byte-identical layouts, 3 have 3-4 identical layouts. 700 are ACCEPTED by Lean, Python and nearcore; the other 427 leave the domain for some other reason. The Lean guards are `c.same_layout`/`c.no_split_gate` (D2:140,156), which never fire here. The tag is therefore a false-positive oracle classifier (an older single-epoch rule), not a Lean-vs-nearcore disagreement (the recorded difftest still shows 0 disagreements). Consequence: the resharding path is completely untested, and the mark will mask real resharding gaps until it is fixed.")
,("c.not_genesis", [("d3c7",39),("d3c8",60),("d3c9",19),("d3c10",19)], 137,
  "genesis main transition", ["ChunkValidationD2.lean:176 `out of domain (c.not_genesis)`"],
  "mapped","137/137 Lean out_of_domain; all 137 nearcore-accepted. Exact 1:1 match.")
,("c.segment", [("d3c7",1),("d3c8",2)], 3,
  "chain segment > 32 blocks", ["ChunkValidationD2.lean:144 `out of domain (c.segment)`"],
  "mapped","3/3 Lean out_of_domain (n_blocks 41/41/43); all nearcore-accepted. Absent from d3c9 (10 distinct strings there).")
,("e.code_cache", [("d3c7",92),("d3c8",125),("d3c9",31),("d3c10",31)], 279,
  "cache-dependent code verdict", ["D3/FunctionCall.lean:271 `out of domain (e.wasm-α): pre-state contract served only by the in-chunk compiled-contract cache`"],
  "mapped","279/279 Lean out_of_domain; cold validator accepts 169 and rejects 110 (`nearcore_cold_no_codes`). The oracle mark and the Lean guard coincide exactly (the difftest's code_cache boundary check).")
,("e.eth_implicit_local", [("d3c7",69),("d3c8",95),("d3c9",24),("d3c10",35)], 223,
  "ETH-implicit account with a Local contract", ["D3/FunctionCall.lean:238 `ETH-implicit account with a local contract (legacy wallet resolution)`"],
  "mapped","209 exact; 14 pre-empted by another guard (float/segment/secp/w.shape) yet still out_of_domain. No accept.")
,("e.float", [("d3c7",35),("d3c8",80),("d3c9",26),("d3c10",19)], 160,
  "float type/opcode in an executed contract", ["Wasm/Prepare.lean:315 `out of domain (e.wasm-α): float type or operator in a function body` (via D3:277)"],
  "mapped","150 exact; 10 pre-empted. Prepare.lean:205/234 (float in an imported signature/global) would also be e.float but have no corpus case.")
,("e.g_alpha", [("d3c7",302),("d3c8",428),("d3c9",149),("d3c10",131)], 1010,
  "chunk function-call gas above G_alpha", ["ChunkValidationD2.lean:240 `out of domain (e.g_alpha): chunk function-call gas … > G_α …`"],
  "mapped","846 exact; 164 pre-empted by an earlier OOD. All 1,010 nearcore-accepted. G_alpha = 2^22 * 822756 = 3,450,888,781,824.")
,("e.mldsa_key", [("d3c7",28),("d3c8",60),("d3c9",14),("d3c10",16)], 118,
  "ML-DSA-65 key in an action/receipt", ["D2/Types.lean:34 `out of domain (w.shape): ML-DSA-65 public key` (D2:46 pPk)"],
  "mapped","114 exact; 4 pre-empted. Same Lean string as the w.shape family (by design).")
,("e.ood_host", [("d3c7",142),("d3c8",197),("d3c9",70),("d3c10",71)], 480,
  "call of an excluded host family", ["Wasm/Exec.lean:72-73 `out-of-domain host function {name} called` (realOodHosts: state-init/global/gas-key)",
   "Wasm/Exec.lean:78 `host function {name} not modelled in D3α` (curve families absent from hostCall)"],
  "mapped","458 exact; 22 pre-empted. 244 curve calls, 214 state-init/global/gas-key calls. 192 import-only contracts are in-domain and accepted (P3).")
,("e.secp", [("d3c7",10),("d3c8",19),("d3c9",8),("d3c10",4)], 41,
  "SECP256K1 delegate signature verification", ["Signed layer: `D2/actDelegate` verifies with `Secp256k1.verify` (W06 widening); no longer a throw",
   "Successor `pBaseGlobalKeyed`/`pTxD2Global` admit the key families"],
  "mapped","0 on the widening tree: the 41 signed exclusions are gone and all 41 accept at `allFeatures` (35 signed-accept after the widening, 6 out-of-domain for unrelated guards). Pre-widening text said `D2/Actions.lean:399` threw and `No accept` — both false now.")
,("w.shape", [("d3c7",77),("d3c8",155),("d3c9",34),("d3c10",51)], 317,
  "out-of-domain action/receipt shape", ["D2/Types.lean:36-39 (DeployGlobalContract/UseGlobalContract/DeterministicStateInit/GlobalContractDistribution)",
   "D2/Types.lean:34-35,46 (ML-DSA keys)", "D2/TxD2.lean:46,59 (non-ED25519 tx key/signature)", "D3/FunctionCall.lean:248 (global contract identifier)"],
  "mapped","317/317 out_of_domain: 149 ML-DSA public key, 89 UseGlobalContract action, 79 non-ED25519 transaction key. No accept.")
]

# ---------------------------------------------------------------- exclusion classification
EXCL = [
 ("e.float","unimplemented","PV86 contracts may contain floats: wasmparser features enable MVP floats and saturating float-to-int (`runtime/near-vm-runner/src/features.rs:47-59`, `SATURATING_FLOAT_TO_INT=true`). Lean rejects them at preparation (`Wasm/Prepare.lean:205,234,315`). 160 protocol-valid cases excluded.","L2"),
 ("e.secp","implemented on the widening tree","SECP256K1 is a live key type and Delegate signature scheme at PV86 (`core/crypto/src/signature.rs:250-257`; `KeyType::SECP256K1`). The W06 widening replaces the `D2/actDelegate` throw with `Secp256k1.verify`, so all 41 protocol-valid cases decide: 41/41 accept at `allFeatures`, 35 accept at `signed` (6 excluded for unrelated guards). Note this is NOT successor-only: `actDelegate` is shared with `checkD3`, so the signed tier moved 35 verdicts `out_of_domain → accept`.","L3"),
 ("e.mldsa_key","unimplemented","ML-DSA-65 is enabled at PV85 (`core/primitives-core/src/version.rs:414,567`; `85.yaml` adds `ml_dsa_65_verification_cost`). Lean treats ML-DSA keys/signatures as `w.shape` (`D2/Types.lean:34-35,46`); 118 protocol-valid cases excluded.","L3"),
 ("w.shape","unimplemented","Global contracts, deterministic state init and gas keys are live at PV83/85 (`Action` tags 9-11, `core/primitives/src/action/mod.rs:349-370`; `version.rs:553-562`; `GlobalContractDistributionNonce`, `GasKeys`). Lean rejects them at `D2/Types.lean:36-39,300-302` and `D3/FunctionCall.lean:248`; 317 protocol-valid cases excluded.","L4"),
 ("e.eth_implicit_local","unimplemented","Legacy ETH-wallet resolution is deterministic given `chain_id` (`runtime/runtime/src/contract_code.rs:56-76`, `eth_wallet_global_contract_hash`), not random. Lean conservatively excludes it (`D3/FunctionCall.lean:236-239`); 223 protocol-valid cases excluded.","L4"),
 ("c.no_resharding","unimplemented (oracle mark defective)","Dynamic resharding is enabled at PV85 (`version.rs:342,564`); the validator has a resharding transition path (`chain_validation.rs:258-308`, `ImplicitTransitionParams::Resharding`, `reassign_outgoing_receipts_for_resharding` at :638) and mainnet genesis sets `dynamic_resharding: true` (`utils/mainnet-res/res/mainnet_genesis.json`). Lean excludes any layout change (`ChunkValidationD2.lean:140`) and any split gate (:156). The 1,127 oracle marks are a stale multi-epoch classifier: all have one layout and 700 are accepted. No genuine resharding case is in the corpus.","L6"),
 ("c.not_genesis","unimplemented","The genesis main transition is a first-class validator branch (`chain_validation.rs:403-411`, `MainTransition::Genesis`, `Chain::genesis_chunk_extra`) and claim-v3 T14 carries `genesis_chunk_extra`. Lean excludes it (`ChunkValidationD2.lean:176`); 137 protocol-valid cases excluded.","L9"),
 ("e.g_alpha","capacity choice, not a boundary condition","`G_α` is a prover table-size cap (`D3/FunctionCall.lean:389`, `D3_WASM_REQUIREMENTS.md` §2.4), not a nearcore condition; nearcore accepts all 1,010 tagged chunks. A chunk above `G_α` is protocol-valid.","L1"),
 ("e.code_cache","partly impossible-at-boundary, partly unimplemented","nearcore's verdict depends on the compiled-contract cache (`oracle/v3-d3/src/d3judge.rs` ColdCache; `function_call.rs:355-393` records the access, `pipelining.rs:323-374` may reuse a preparation). For a *rolled-back* in-chunk deploy the verdict is genuinely cache-dependent, so no cache-independent relation can decide it. For a *committed* deploy the deploy tracker serves the code deterministically (`contract.rs:42-131`), so those 169 cold-accepted cases are decidable; Lean's blanket rule (`D3/FunctionCall.lean:268-275`) excludes them anyway.","L1 + L7"),
 ("c.segment","arena-format bound, not a validator condition","The 32-block bound is a claim-size budget (`spec/claim-v3.md` §5 `max_claim_bytes`), not a nearcore rule; the validator's backward walk (`chain_validation.rs:144-253`) has no such limit. Three protocol-valid claims have 41/41/43 blocks and are excluded by `ChunkValidationD2.lean:144`.","L1")
]

# ---------------------------------------------------------------- unresolved questions
UQ = [
 ("UQ-001","Must `Rel_D3` be cache-independent, and is the cold-cache statement the one the arena admits?","L1",
  "spec/near-chunk-validation-d3.md §10.0 decision 1 fixes cold-cache; the signed challenge and successor API must state it. Gate B cannot claim 'every protocol-valid case' while a validator-cache parameter changes the verdict."),
 ("UQ-002","Can `e.code_cache` be narrowed to rolled-back deploys (committed deploys are served by `ContractsTracker`)?","L1 + L7",
  "169 of 279 code-cache cases are cold-validator accepts; `contract.rs:104-131` makes a committed deploy deterministic. Narrowing needs a proof and a re-run."),
 ("UQ-003","Which NaN payload/sign semantics does the pinned Wasmtime produce, and is that stable across validator architectures?","L2",
  "Float types/ops are accepted at PV86 (`features.rs:47-59`); H3 in `docs/research/near-wasm-boundary.md` says canonical NaN sign on non-x86 is an assumption."),
 ("UQ-004","Are the curve host-function gas schedules fully pinned at PV86 (there is no `86.yaml`)?","L3",
  "`core/parameters/res/runtime_configs/` has 79/82/83/84/85.yaml and `parameters.snap`; the D3 spec says PV86 params are the 85 snapshot. Curve costs must come from the snapshot, not a 86 file."),
 ("UQ-005","Is the ML-DSA-65 trie key handle (SHA3-256 of the pubkey) part of the pinned claim/trie model?","L3",
  "`core/crypto/src/signature.rs:498-506`, `core/primitives/src/trie_key.rs:182,327` use `PublicKeyHandle::MlDsa65`; `D2/Types.lean:18` says the handle is not formalized."),
 ("UQ-006","Which global-contract / state-init receipts can appear in `source_receipt_proofs` at PV86, and are `GlobalContractDistribution` receipts ever in a chunk witness?","L4",
  "`D2/Types.lean:15` models tag 4 as `w.shape`; `version.rs:553-562` gates distribution nonce at 83."),
 ("UQ-007","Is the `LegacyEthWallet` branch still reachable at PV86 after `EthImplicitGlobalContract` (83), and which wallet hashes must be enumerated?","L4",
  "`contract_code.rs:56-76`: with `eth_implicit_global_contract` on, the legacy path becomes a `Global{eth_wallet_global_contract_hash(chain_id)}`."),
 ("UQ-008","Which witness carries a resharding transition, and must `retain_split_shard` / child congestion info be modelled per child shard?","L6",
  "`chain_validation.rs:258-308` + `ImplicitTransitionParams::Resharding`; `D2/Queues.lean:327` already excludes out-of-layout buffers."),
 ("UQ-009","May a valid segment reference a PV85 epoch (a protocol-version activation boundary), and does the pinned target require both PV85 and PV86 runtime configs?","L9 + L6",
  "`ChunkValidationD2.lean:125,139` require pv=86 for every epoch; the claim table can contain a pre-activation epoch. `epoch_start_after` already models the boundary."),
 ("UQ-010","Which predicate is the statement of record: `checkD3` (implementation) or the parallel domain predicates `noResharding`/`contractInD3α` (unused, and stricter on curve imports)?","L1",
  "The parallel predicates were not referenced by `checkD3`; `contractInD3α` rejected curve *imports* while the checker accepts them (P3). `noResharding_spec` was proved but disconnected."),
 ("UQ-011","Does Gate B require removing the arena claim-size bounds (`c.segment` 32 blocks, `w.size` 4 MB/8 MiB), or is a larger versioned claim format acceptable?","L1 + L8",
  "`ChunkValidationD2.lean:120,144,237`; `claim-v3.md` §5 sets `max_claim_bytes` from these bounds. These are not validator conditions."),
 ("UQ-012","Does Gate B require unbounded chunk function-call gas (segmented proof), or is a stated `G_α` capacity contract acceptable?","L1",
  "`G_α` is a prover table bound; 1,010 corpus chunks exceed it and nearcore accepts them. The plan says 'every protocol-valid case'."),
 ("UQ-013","What admission contract binds the trusted facts (`chain_id`, validators, `minimum_stake`, `tx_valid`, RS params, `genesis_chunk_extra`) to the verifier's own chain state?","L8",
  "`claim-v3.md` §2.4 T3/T4/T8/T10/T11/T13/T14 are outside `Rel`; a proof alone is not meaningful."),
 ("UQ-014","Are the Wasmtime `LoadingError` / `WasmUnknownError` / resource `LinkError` branches (H2/H9/H10) truly absent at PV86, or must they be modelled?","L7",
  "`docs/research/near-wasm-boundary.md` §8 H2/H9/H10 assume them absent; `Prepare.lean` models only `LinkError` and compile errors."),
 ("UQ-015","Is `Σ|values| + 2000·R ≤ 4 000 000` a sound upper bound on `recorded_storage_size_upper_bound` when contract-storage removals are present?","L5",
  "`ChunkValidationD2.lean:235-237`; the D3 spec marks the inequality unverified. PV86 enforces the per-receipt limit (`version.rs:576`, `lib.rs:838-845`, `recorded_storage_counter.rs:27`)."),
 ("UQ-016","Is the mock action log equivalent to nearcore's `ReceiptManager` for every reachable promise/yield/gas-key shape, or does it silently OOD a valid shape?","L4",
  "`D3/FunctionCall.lean:88-220` parses the oracle's `MAct.text`; tags it cannot parse become OOD (`:153,176,219,328`). No corpus case exercises an unparsed tag, so the gap is unmeasured."),
 ("UQ-017","For the genesis main transition, which header comparisons apply and is `tx_valid` all-1?","L9",
  "`chain_validation.rs:382-401` sets all-1 for a genesis last chunk; `chunk_extra` is the genesis chunk extra. Lean's `c.not_genesis` excludes the whole branch.")
]

# Current disposition of each UQ (docs/research/lean-chunk-w00-owner-map.md §3, abridged).
OM = "docs/research/lean-chunk-w00-owner-map.md §3"
UQ_DISPOSITION = {
 "UQ-001": ("resolved 2026-10-29 (W08)", "the relation is the cold-cache statement; accepts and non-missing-code rejects are cache-independent for every hash-consistent cache (docs/evidence/lean-chunk-completion/w08-warm-cache/README.md)"),
 "UQ-002": ("resolved 2026-10-29", "on allFeatures only the preparation-pipeline race stays cache-dependent (e.code_prep_race); 279 e.code_cache corpus cases, 0 disagreements (open-uqs)"),
 "UQ-003": ("resolved 2026-10-29", "positive canonical NaN; 5,920 calls bit-identical x86_64/aarch64/Lean (open-uqs)"),
 "UQ-004": ("resolved 2026-10-29", "PV86 uses the config stored at key 85; 32/32 crypto costs and flags agree (open-uqs)"),
 "UQ-005": ("resolved 2026-10-26", "SHA3-256 ML-DSA-65 handle matches nearcore; 533 honest chunks and 3,886 mutants agree (mldsa-fixtures)"),
 "UQ-006": ("resolved 2026-10-26", "distribution receipts reach witnesses and are executed/routed, including across a split (global-cache-fixtures, resharding-fixtures-2)"),
 "UQ-007": ("resolved 2026-10-29", "LegacyEthWallet unreachable at PV86; 7/7 wallet hashes match; no whole-chunk magic-hash fixture (row L0-D3-006)"),
 "UQ-008": ("resolved 2026-10-26", "the first child chunk carries the Resharding transition; per-child congestion and retain_split_shard modelled and matched on 2,920 real-split witnesses (row L0-resharding)"),
 "UQ-009": ("resolved 2026-10-26", "mainnet goes PV84 -> PV86; a PV86 layout change is a V3 split (Successor/LayoutReach.lean)"),
 "UQ-010": ("resolved 2026-10-29", "checkD3/RelD3 is the statement of record; the parallel predicates were retired (owner map §3.4 (d)); the witness-size domain bound was settled 2026-10-30 (maxWitnessChunk = 75,497,501)"),
 "UQ-011": ("resolved for allFeatures 2026-10-26", "c.segment, w.size (8 MiB) and c.layout lifted; nearcore's 64 MiB/48 MiB witness limits kept (gate-b-caps, size-limit-fixtures)"),
 "UQ-012": ("resolved for allFeatures 2026-10-26", "gasCap := none; 1.8 Pgas chunks accept and match nearcore (gate-b-caps)"),
 "UQ-013": ("resolved 2026-10-30 by user decision", "admission contract A1: the verifier rebuilds the claim's trusted section from its own chain state and requires byte identity (open-uqs)"),
 "UQ-014": ("open", "Wasmtime LoadingError/WasmUnknownError/resource LinkError branches at PV86: proof owed (L7)"),
 "UQ-015": ("resolved 2026-10-29", "the signed bound is sound; allFeatures does not use it (open-uqs; row L0-D2-040)"),
 "UQ-016": ("resolved 2026-10-29", "no action-log entry reaches the unmodeled exclusion on whole-state tiers (open-uqs)"),
 "UQ-017": ("resolved 2026-10-29", "genesis main transition uses the non-genesis comparison set; 266/266 genesis-main chunks agree (row L0-genesis-main-transition)"),
}

# Current disposition of each exclusion class on the canonical relation (allFeatures) and on the
# signed tier, from the pre-freeze replay (workplan 2026-10-31) and the owner map §3.4.
EXCL_NOW = {
 "e.float": "decided on allFeatures (floats); signed tier excludes (150 census claims; 279 of mainnet shard 13's 1,223 chunks)",
 "e.secp": "decided on both tiers since the UQ-010 secp strengthening",
 "e.mldsa_key": "decided on allFeatures (ML-DSA-65 implemented, mldsa-fixtures); signed tier excludes (260 census claims)",
 "w.shape": "decided on allFeatures (global actions validated, rows L0-action-09..11); a w.shape global_code_identity exclusion remains, unreachable (row L0-AF-global-code-identity); signed tier excludes (~303 census claims)",
 "e.eth_implicit_local": "decided on allFeatures (row L0-D3-006, implemented, validation gap); signed tier excludes (210)",
 "c.no_resharding": "decided on allFeatures and by the signed hand-over (row L0-resharding, validated)",
 "c.not_genesis": "decided on allFeatures (row L0-genesis-main-transition, validated); signed tier excludes (137)",
 "e.g_alpha": "lifted on allFeatures (gasCap := none) and on the signed hand-over path; the signed core keeps G_α (847)",
 "e.code_cache": "decided on allFeatures except the pipeline race (e.code_prep_race, impossible-at-boundary); signed tier excludes (169)",
 "c.segment": "lifted on allFeatures (segmentUnbounded); signed tier keeps it (3)",
}

# ---------------------------------------------------------------- guard counts
def strip_comments(src):
    out=[]; in_block=False
    for line in src.split("\n"):
        if in_block:
            if "-/" in line: in_block=False
            continue
        if "/-" in line and "-/" not in line:
            in_block=True
            line=line.split("/-")[0]
        i=line.find("--")
        if i>=0: line=line[:i]
        out.append(line)
    return "\n".join(out)

MODS=["spec/lean/v3/NearSpecV3/ChunkValidationD2.lean","spec/lean/v3/NearSpecV3/ChunkValidationD1.lean",
 "spec/lean/v3/NearSpecV3/ChunkValidationD1a.lean","spec/lean/v3/NearSpecV3/ChunkValidationV0.lean",
 "spec/lean/v3/NearSpecV3/ChunkValidationV0a.lean","spec/lean/v3/NearSpecV3/D3/FunctionCall.lean",
 "spec/lean/v3/NearSpecV3/Wasm/Prepare.lean","spec/lean/v3/NearSpecV3/Wasm/Exec.lean",
 "spec/lean/v3/NearSpecV3/Wasm/Validate.lean","spec/lean/v3/NearSpecV3/Wasm/FiniteWasm.lean",
 "spec/lean/v3/NearSpecV3/ReshardingD3.lean","spec/lean/v3/NearSpecV3/Wasm/Host.lean",
 "spec/lean/v3/NearSpecV3/Wasm/Syntax.lean","spec/lean/v3/NearSpecV3/Wasm/Decode.lean",
 "spec/lean/v3/NearSpecV3/Wasm/Segment.lean","spec/lean/v3/NearSpecV3/Wasm/TrieStore.lean",
 "spec/lean/v3/NearSpecV3/Wasm/ChunkStorage.lean","spec/lean/v3/NearSpecV3/Wasm/Machine.lean",
 "spec/lean/v3/NearSpecV3/Wasm/TrieAccounting.lean","spec/lean/v3/NearSpecV3/Wasm/InstrSize.lean",
 "spec/lean/v3/NearSpecV3/D2/Types.lean","spec/lean/v3/NearSpecV3/D2/Actions.lean",
 "spec/lean/v3/NearSpecV3/D2/Receipts.lean","spec/lean/v3/NearSpecV3/D2/Queues.lean",
 "spec/lean/v3/NearSpecV3/D2/TxD2.lean","spec/lean/v3/NearSpecV3/RuntimeD1.lean",
 "spec/lean/v3/NearSpecV3/RuntimeD0.lean","spec/lean/v3/NearSpecV3/Layout.lean",
 "spec/lean/v3/NearSpecV3/Wire.lean","spec/lean/v3/NearSpecV3/PrepD0.lean"]
GUARDS={}
for m in MODS:
    try: src=strip_comments(open(m).read())
    except FileNotFoundError: continue
    check=len(re.findall(r"\bcheck\s*\(",src))+len(re.findall(r"\bcheckK\s*\(",src))
    throw=len(re.findall(r"\bthrow\b",src))
    err=len(re.findall(r"\.error\b",src))
    ood=len(re.findall(r'out of domain',src))
    unmod=len(re.findall(r'unmodeled',src))
    GUARDS[m.split("NearSpecV3/")[1]]={"check":check,"throw":throw,"error":err,"ood":ood,"unmodeled":unmod,
                                        "decision_sites":check+throw+err}



def _s(x):
    if isinstance(x, list):
        return " | ".join(str(y) for y in x)
    return str(x)


def extra_rows():
    out=[]
    for r in ROWS:
        if r["family"] in ("layer-boundary",):
            continue  # main's 114 rows already cover action/host/domain dispatch at this granularity
        d=dict(r)
        d["evidence"]=_s(r["evidence"])
        d["dependencies"]=_s(r["dependencies"])
        d["acceptance_tests"]=_s(r["acceptance_tests"])
        out.append(d)
    return out


def lean_files():
    out=set()
    for r in ROWS:
        for sym in (r["lean_path_symbol"],):
            for tok in sym.replace("("," ").replace(")"," ").split():
                if tok.startswith("spec/lean/v3/NearSpecV3/"):
                    out.add(tok.split(":")[0].split("NearSpecV3/")[1])
    return sorted(out)


def sections():
    return {
        "oracle_marks": [dict(tag=t, counts=dict(c), total=n, nearcore_fact=f,
                              lean_guards=g, mapping=m, note=note)
                         for t,c,n,f,g,m,note in ORACLE],
        "exclusion_classification": [dict(exclusion=e, classification=c, justification=j, owner=l,
                                          now=EXCL_NOW[e])
                                     for e,c,j,l in EXCL],
        "unresolved_boundary_questions": [dict(id=i, question=q, owner=l, why=w,
                                               disposition=UQ_DISPOSITION[i][0],
                                               disposition_detail=UQ_DISPOSITION[i][1] + " (" + OM + ")")
                                          for i,q,l,w in UQ],
        "guards_per_module": GUARDS,
        "called_vs_imported_hosts": {
            "answer": "Under RuntimeD3 exclusion triggers on a CALL, not on an import.",
            "lean": [
                "Wasm/Exec.lean:72 gate is inside callHost",
                "Wasm/Exec.lean:78 curve families are absent from hostCall",
                "Wasm/Exec.lean:462-464 import gate fires only when real.isNone (state-free harness)",
                "D3/FunctionCall.lean:277 contractOOD consults prepare only",
            ],
            "nearcore": "imports link at instantiation (wasmtime_runner/mod.rs:1127-1155); only a call runs External code",
            "evidence": "192 import-only cases: 167 accept, 25 OOD for an unrelated guard, 0 reject",
        },
    }
