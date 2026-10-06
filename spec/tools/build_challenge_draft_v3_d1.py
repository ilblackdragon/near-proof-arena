#!/usr/bin/env python3
"""Build challenges/drafts/near-chunk-validation-d1.draft.json (unsigned): domain D1 (+ Transfer transactions).

All digests are computed from the repository at HEAD (tracked files only):
  runtime_config_digest = sha256(JCS(spec/challenge-inputs/runtime-config-pv86-v3-d1.json))
                          (the v3 description plus the transaction fees D1 reads)
  formal_spec.tree_digest = TreeDigest(spec/lean formal-core)   (spec/tools/tree_digest.py)
  spec_doc_digest = sha256 of spec/near-chunk-validation-d1.md; claim spec_digest = sha256(spec/claim-v3.md)
  public_fixtures = TreeDigest(oracle/fixtures/v3/public-d1)
"""
import hashlib, json, os, subprocess, sys

ROOT = subprocess.run(["git", "rev-parse", "--show-toplevel"], capture_output=True, text=True,
                      check=True).stdout.strip()

def jcs(v): return json.dumps(v, separators=(",", ":"), sort_keys=True, ensure_ascii=False)
def dig(v): return "sha256:" + hashlib.sha256(jcs(v).encode()).hexdigest()
def fdig(p): return "sha256:" + hashlib.sha256(open(os.path.join(ROOT, p), "rb").read()).hexdigest()
def tree(*paths):
    return subprocess.run([sys.executable, os.path.join(ROOT, "spec/tools/tree_digest.py"), *paths],
                          capture_output=True, text=True, check=True, cwd=ROOT).stdout.strip()

R = lambda i, t: {"id": i, "text": t}
restrictions = [
    R("c.pv86", "protocol_version = 86 (nearcore 2.13.4), mainnet runtime parameters RuntimeConfigStore::new(None).get_config(86)"),
    R("c.single_epoch", "every block of the claim's chain segment is in epoch_id; one epoch record; no epoch start in the segment"),
    R("c.layout", "the epoch's shard layout is ShardLayout V2 or V3 with 1..=64 shards"),
    R("c.headers", "block headers V6; chunk header inners V4/V5"),
    R("c.no_split_gate", "no validator-account update and no dynamic-resharding split check for any applied block"),
    R("c.not_genesis", "the last new chunk of the shard is not the genesis chunk"),
    R("c.segment", "the chain segment has at most 32 blocks"),
    R("c.own_congestion_zero", "the shard's congestion info in the last-chunk block has zero delayed gas, buffered gas and receipt bytes"),
    R("w.tx_shape", "every transaction in transactions and new_transactions: V0, or V1 with a plain nonce; exactly one Transfer action; ED25519 public key and ED25519 signature"),
    R("t.signer_v1", "every signer account read by process_transactions is AccountV1"),
    R("w.no_code", "no contract code accompanies the witness"),
    R("w.size", "state witness <= 8 MiB and the main transition's base_state <= 3,000,000 bytes"),
    R("w.proof_shape", "every receipt in every source_receipt_proofs entry (incl. overridden duplicate keys) has the D0 receipt shape"),
    R("r.shape", "every applied receipt (incoming or local): ReceiptEnum::Action, one Transfer action, no data dependencies, ED25519/SECP256K1 signer key, named receiver"),
    R("r.refunds", "a gas refund (system predecessor, signer = receiver) finds no access key or a FullAccess key"),
    R("r.success", "every applied receipt (incoming or local) succeeds (receiver exists as AccountV1, no overflow, storage stake covered)"),
    R("e.compute", "no local or incoming receipt is delayed by the compute limit (transactions' gas counts)"),
    R("e.queues_empty", "delayed-receipt queue, outgoing buffers and promise-yield queue are empty in the pre-state"),
    R("e.forwarded", "every transaction receipt and generated receipt is forwarded (never buffered)"),
    R("e.distinct_ids", "applied (incoming and local) receipt ids are pairwise distinct"),
]

def main():
    rc = json.load(open(os.path.join(ROOT, "spec/challenge-inputs/runtime-config-pv86-v3-d1.json")))
    draft = {
        "schema": "arena-challenge-v1",
        "name": "near-chunk-validation-d1",
        "season": "2026-s1",
        "tier": "formal",
        "nearcore": {"repo": "https://github.com/near/nearcore", "tag": "2.13.4",
                     "commit": "44f7ae6cd7ef08bab604e20a473bf77e35d4c993"},
        "protocol_version": 86,
        "chain_id": "mainnet",
        "runtime_config_digest": dig(rc),
        "semantic_scope": {
            "name": "near/pv86/chunk-validation/v0#D1",
            "kind": "subset",
            "granularity": "chunk_validation",
            "restrictions": restrictions,
            "excludes": ["block_finality", "data_availability", "chunk_producer_signatures",
                         "witness_transport_and_part_decoding", "trusted_epoch_facts_correctness",
                         "non_transfer_transactions", "gas_key_transactions",
                         "secp256k1_and_mldsa_transactions", "non_transfer_actions", "function_calls_and_wasm",
                         "failure_paths_and_rollback", "delayed_and_buffered_receipts",
                         "epoch_boundaries_and_validator_updates", "resharding",
                         "dynamic_resharding_split_search", "genesis_main_transition",
                         "other_protocol_versions"],
            "formal_spec": {
                "relation_module": "NearSpecV3.ChunkValidationD1",
                "relation_decl": "NearSpecV3.RelD1",
                "challenge_spec_decl": "NearSpecV3.challengeSpecD1",
                "tree_digest": tree("spec/lean", "formal-core"),
                "lean_toolchain": "leanprover/lean4:v4.34.1"},
            "spec_doc_digest": fdig("spec/near-chunk-validation-d1.md"),
        },
        "claim_encoding": {"format": "near-arena-claim-v3", "spec_digest": fdig("spec/claim-v3.md"),
                           "max_request_bytes": 1048576, "max_witness_bytes": 8392704,
                           "max_claim_bytes": 1048576},
        "security_profile": json.load(open(os.path.join(ROOT, "security/profiles/validity-classical-128.json"))),
        "toolchain_policy": {"lean_toolchain": "leanprover/lean4:v4.34.1", "checker_image": None,
                             "axiom_allowlist": ["propext", "Classical.choice", "Quot.sound"],
                             "allowed_packages": [], "recheckers": ["leanchecker", "nanoda", "lean4lean"]},
        "required_obligations": ["PKG_WELLFORMED", "BUILD_REPRODUCIBLE", "ARTIFACT_BINDING",
                                 "FORMAL_SEMANTIC_SOUNDNESS", "FORMAL_SEMANTIC_COMPLETENESS",
                                 "FORMAL_CRYPTO_SOUNDNESS", "FORMAL_IMPL_CONNECTION", "AXIOM_AUDIT",
                                 "CONFORMANCE_DIFFERENTIAL", "ADVERSARIAL_PROOFS", "PROVER_RELIABILITY",
                                 "RESOURCE_LIMITS", "BENCHMARK"],
        "not_applicable_gates": ["FORMAL_ZK"],
        "hardware_profile": None,
        "workload_suite": {
            "revision": "near-chunk-validation-d1-r0",
            "classes": [{"id": "d1-chunks", "description": "real ChunkStateWitness + claim-v3 pairs in D1 from multi-shard nearcore TestEnv chains with Transfer transactions of every validity class (near-arena-oracle-v3 gen --domain d1)",
                         "weight_ppm": 1000000, "batch_size": 8, "generator": None}],
            "public_fixtures": tree("oracle/fixtures/v3/public-d1"),
            "heldout_commitment": None, "baseline_submission": None, "baseline_ns": []},
        "measurement": {"warmup_runs": 3, "measured_runs": 15, "aggregation": "median", "outlier_mad_k": 5,
                        "cold_runs": 1, "concurrency": 1, "per_run_timeout_ms": 600000},
        "resource_limits": {"max_proof_bytes": 67108864, "max_verify_ms": 10000, "max_prove_ms": 600000,
                            "max_ram_bytes": 17179869184, "max_vram_bytes": 0,
                            "max_public_artifact_bytes": 67108864, "max_prepare_ms": 600000,
                            "max_build_ms": 3600000},
        "supersedes": None,
        "created_at": "2026-10-06T00:00:00Z",
        "formal_params": {"verify_fuel": 1073741824, "max_proof_bytes": 67108864,
                          "max_reduction_fuel": 1073741824},
        "draft_notes": "UNSIGNED DRAFT. Not loadable by the server: checker_image, hardware_profile, workload generator digests and the held-out commitment are still to be pinned. Statement: spec/near-chunk-validation-v0.md with domain D1 in spec/near-chunk-validation-d1.md; formats: spec/claim-v3.md (unchanged from D0). v1/v2 challenges are unrelated and stay frozen.",
    }
    out = os.path.join(ROOT, "challenges/drafts/near-chunk-validation-d1.draft.json")
    open(out, "w").write(json.dumps(draft, indent=2) + "\n")
    print(out)

if __name__ == "__main__":
    main()
