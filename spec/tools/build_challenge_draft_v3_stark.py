#!/usr/bin/env python3
"""Build challenges/drafts/near-chunk-validation-d0.draft.json (unsigned) and the
workload generator specs spec/workloads/near-chunk-validation-d0/<class>.json.

  build_challenge_draft_v3.py [--freeze-commit SHA] [--heldout-commitment sha256:…]
                              [--baseline-summary benchmarks/results/<s>/summary.json]
                              [--created-at RFC3339] [--out PATH] [--measure]

All digests are computed from the repository at HEAD (tracked files only):
  runtime_config_digest = sha256(JCS(spec/challenge-inputs/runtime-config-pv86-v3.json))
  formal_spec.tree_digest = TreeDigest(spec/lean formal-core)   (spec/tools/tree_digest.py)
  spec_doc_digest / claim spec_digest = sha256 of the spec documents
  public_fixtures = TreeDigest(oracle/fixtures/v3/arena-public)  (arena layout + params.bin)
  workload_suite.classes[].generator = sha256(JCS(generator spec))
  generator spec oracle_source_tree_digest = TreeDigest(oracle/v3/src oracle/v3/Cargo.toml oracle/v3/Cargo.lock)
--freeze-commit pins toolchain_policy.allowed_packages (ArenaCore, NearSpec, NearSpecV3) at the
commit whose formal-core + spec/lean the challenge freezes (and the reference candidate vendors).
--measure writes the baseline-measurement draft (no baseline) instead.
"""
import argparse, hashlib, json, os, subprocess, sys

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
    R("c.no_tx_flags", "no transaction validity flags (no transactions)"),
    R("c.segment", "the chain segment has at most 32 blocks"),
    R("c.gas_limit", "the chunk gas_limit in the last-chunk block's slot of the validated shard is at most 10^15 gas (mainnet genesis 1000 Tgas; nearcore never changes a chunk gas limit after genesis) [A1]"),
    R("c.own_congestion_zero", "the shard's congestion info in the last-chunk block has zero delayed gas, buffered gas and receipt bytes"),
    R("w.no_txs", "the witness has no transactions and no new_transactions"),
    R("w.no_code", "no contract code accompanies the witness"),
    R("w.size", "state witness <= 8 MiB and the main transition's base_state <= 3,000,000 bytes"),
    R("w.proof_shape", "every receipt in every source_receipt_proofs entry (incl. overridden duplicate keys) has the D0 receipt shape"),
    R("w.proof_routing", "every receipt of every used source receipt proof routes, under the epoch's shard layout, to the validated shard (true of every honest single-epoch witness) [A2]"),
    R("r.shape", "every applied receipt: ReceiptEnum::Action, one Transfer action, no data dependencies, ED25519/SECP256K1 signer key, named receiver"),
    R("r.refunds", "a gas refund (system predecessor, signer = receiver) finds no access key or a FullAccess key"),
    R("r.success", "every applied receipt succeeds (receiver exists as AccountV1, no overflow, storage stake covered)"),
    R("e.compute", "no incoming receipt is delayed by the compute limit"),
    R("e.queues_empty", "delayed-receipt queue, outgoing buffers and promise-yield queue are empty in the pre-state"),
    R("e.forwarded", "every generated receipt is forwarded (never buffered)"),
    R("e.sched_canonical", "every BandwidthSchedulerState value read (main and implicit pre-states) is absent or V1 listing exactly the layout's n^2 links in sender-major order (what update_scheduler_state writes) [Canon0f]"),
    R("w.unfolded", "unfoldBytes <= B0 = 2,000,000: the bytes of every partial trie the relation builds, unfolded per read-path copy, plus the post-write path copies, summed over all transitions (NearSpecV3.unfoldBytes) [A7]"),
    R("e.distinct_ids", "applied receipt ids are pairwise distinct"),
]

# Workload classes (spec/near-chunk-validation-v0.md §6 D0; oracle/v3 `gen --class`):
# every class draws real multi-shard nearcore TestEnv chains whose parameter set is rotated
# by the seed (4/5/6 shards x Reed-Solomon (2,8), (33,100) = mainnet, (5,16), (1,3); 1000 Tgas
# or 10 Tgas gas limit), at most 2 chunks per chain, so a batch spans 4 chain configurations.
CLASSES = [
    ("d0-quiet", "quiet", 200000, [],
     "D0 chunks with no incoming receipt and no implicit transition: context authentication "
     "(hash-linked segment, chunk_headers_root), empty main transition, bandwidth scheduler, "
     "congestion info and the Reed-Solomon encoded merkle root"),
    ("d0-transfers", "transfers", 500000, [],
     "D0 chunks applying >= 1 incoming cross-shard Transfer receipt (source receipt proofs, ChaCha20 "
     "shuffle, Runtime::apply over the partial trie, refunds, outcome and outgoing-receipts roots), "
     "no implicit transition"),
    ("d0-missing", "missing", 300000, ["--p-missing", "0.25"],
     "D0 chunks after >= 1 missing chunk of the shard (implicit transitions: missing-chunk applies "
     "with the bandwidth scheduler), with or without incoming receipts; chains with 25% chunk skips"),
]

def generator_spec(cid, cls, extra, oracle_digest):
    return {
        "schema": "near-arena-workload-generator-v1",
        "challenge": "near-chunk-validation-d0",
        "class": cid,
        "tool": "near-arena-oracle-v3 gen",
        "args": ["--fixtures-layout", "--class", cls, "--rotate", "--per-chain-cap", "2",
                 "--chains", "48", "--blocks", "40", "--mutate-every", "0", "--ood-cap", "0", *extra],
        "seed": "judge-chosen per run (season-secret HMAC, BENCHMARK_SPEC §11.1); --d0-target = batch size; held-out set: secret seed",
        "oracle_source_tree_digest": tree("oracle/v3/src", "oracle/v3/Cargo.toml", "oracle/v3/Cargo.lock"),
        "nearcore_commit": "44f7ae6cd7ef08bab604e20a473bf77e35d4c993",
        "statement_id": "near/pv86/chunk-validation/v0",
        "domain": "D0",
    }

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--freeze-commit", default=None)
    ap.add_argument("--heldout-commitment", default=None)
    ap.add_argument("--baseline-summary", default=None)
    ap.add_argument("--created-at", default="2026-10-05T12:00:00Z")
    ap.add_argument("--checker-image", default="sha256:66b014d4e05744bcf21771c469f93d119a0d24a5dc4288d28cb46126c4bf1867")
    ap.add_argument("--out", default=os.path.join(ROOT, "challenges/drafts/near-chunk-validation-d0-stark.draft.json"))
    ap.add_argument("--measure", action="store_true")
    ap.add_argument("--name", default="near-chunk-validation-d0-stark")
    ap.add_argument("--supersedes", default=None, help="challenge id this one supersedes")
    a = ap.parse_args()
    # Same workload generators as near-chunk-validation-d0 (their honest positives come from
    # chains with 10 / 1000 Tgas gas limits and satisfy A1, A2, Canon0f): the digests are
    # recomputed here, the generator spec files under spec/workloads/near-chunk-validation-d0
    # are not rewritten.
    classes = []
    for cid, cls, w, extra, desc in CLASSES:
        spec = generator_spec(cid, cls, extra, None)
        classes.append({"id": cid, "description": desc, "weight_ppm": w, "batch_size": 8,
                        "generator": dig(spec)})
    baseline_sub, baseline_ns = None, []
    if a.baseline_summary:
        bs = json.load(open(a.baseline_summary))
        baseline_sub = bs["reference_candidate"]["package_digest"]
        baseline_ns = bs["baseline_ns"]
    allowed = [] if not a.freeze_commit else [[p, a.freeze_commit] for p in ("ArenaCore", "NearSpec", "NearSpecV3")]
    rc = json.load(open(os.path.join(ROOT, "spec/challenge-inputs/runtime-config-pv86-v3.json")))
    draft = {
        "schema": "arena-challenge-v1",
        "name": a.name,
        "season": "2026-s1",
        "tier": "formal",
        "nearcore": {"repo": "https://github.com/near/nearcore", "tag": "2.13.4",
                     "commit": "44f7ae6cd7ef08bab604e20a473bf77e35d4c993"},
        "protocol_version": 86,
        # The claim's chain_id (trusted fact T3, spec/claim-v3.md §2.4) is the chain the claims are
        # about: the oracle's TestEnv chains are "arena-v3-local" (nearcore asserts the real genesis
        # hash for chain_id "mainnet", so a test chain cannot carry it). D0 never reads chain_id;
        # parameters are mainnet's (runtime_config_digest, RuntimeConfigStore::new(None) at PV 86).
        "chain_id": "arena-v3-local",
        "runtime_config_digest": dig(rc),
        "semantic_scope": {
            "name": "near/pv86/chunk-validation/v0#D0a",
            "kind": "subset",
            "granularity": "chunk_validation",
            "restrictions": restrictions,
            "excludes": ["block_finality", "data_availability", "chunk_producer_signatures",
                         "witness_transport_and_part_decoding", "trusted_epoch_facts_correctness",
                         "transactions", "non_transfer_actions", "function_calls_and_wasm",
                         "failure_paths_and_rollback", "delayed_and_buffered_receipts",
                         "epoch_boundaries_and_validator_updates", "resharding",
                         "dynamic_resharding_split_search", "genesis_main_transition",
                         "other_protocol_versions"],
            "formal_spec": {
                "relation_module": "NearSpecV3.ChunkValidationV0a",
                "relation_decl": "NearSpecV3.RelD0a",
                "tree_digest": tree("spec/lean", "formal-core"),
                "lean_toolchain": "leanprover/lean4:v4.34.1"},
            "spec_doc_digest": fdig("spec/near-chunk-validation-v0a.md"),
        },
        "claim_encoding": {"format": "near-arena-claim-v3", "spec_digest": fdig("spec/claim-v3.md"),
                           "max_request_bytes": 1048576, "max_witness_bytes": 8392704,
                           "max_claim_bytes": 1048576},
        "security_profile": json.load(open(os.path.join(ROOT, "security/profiles/validity-classical-128.json"))),
        "toolchain_policy": {"lean_toolchain": "leanprover/lean4:v4.34.1", "checker_image": a.checker_image,
                             "axiom_allowlist": ["propext", "Classical.choice", "Quot.sound"],
                             "allowed_packages": allowed, "recheckers": ["leanchecker", "nanoda", "lean4lean"]},
        "required_obligations": ["PKG_WELLFORMED", "BUILD_REPRODUCIBLE", "ARTIFACT_BINDING",
                                 "FORMAL_SEMANTIC_SOUNDNESS", "FORMAL_SEMANTIC_COMPLETENESS",
                                 "FORMAL_CRYPTO_SOUNDNESS", "FORMAL_IMPL_CONNECTION", "AXIOM_AUDIT",
                                 "CONFORMANCE_DIFFERENTIAL", "ADVERSARIAL_PROOFS", "PROVER_RELIABILITY",
                                 "RESOURCE_LIMITS", "BENCHMARK"],
        "not_applicable_gates": ["FORMAL_ZK"],
        # Same dev-host profile and procedure as near-transfer-receipt-v1-6: 8 vCPUs per run,
        # benchmarks on CPUs 0-7 (CCD0, docs/LIVE.md §4), one microVM per batch.
        "hardware_profile": {"id": "nearproof-local-ryzen9-9950x3d",
                             "cpu_model": "AMD Ryzen 9 9950X3D 16-Core Processor (local operator host; 8 vCPUs pinned per run)",
                             "vcpus": 8, "ram_bytes": 34359738368, "gpu": None},
        "workload_suite": {
            "revision": "near-chunk-validation-d0-stark-r0",
            "classes": classes,
            "public_fixtures": tree("--relative-to", "oracle/fixtures/v3/arena-public", "oracle/fixtures/v3/arena-public"),
            "heldout_commitment": a.heldout_commitment or "sha256:" + "0" * 64,
            "baseline_submission": None if a.measure else baseline_sub,
            "baseline_ns": [] if a.measure else baseline_ns},
        "measurement": {"warmup_runs": 3, "measured_runs": 15, "aggregation": "median", "outlier_mad_k": 5,
                        "cold_runs": 1, "concurrency": 1, "per_run_timeout_ms": 600000,
                        "invocation_mode": "vm_per_batch"},
        "resource_limits": {"max_proof_bytes": 8388608, "max_verify_ms": 10000, "max_prove_ms": 600000,
                            "max_ram_bytes": 17179869184, "max_vram_bytes": 0,
                            "max_public_artifact_bytes": 67108864, "max_prepare_ms": 600000,
                            "max_build_ms": 3600000},
        "supersedes": a.supersedes,
        "draft_notes": "UNSIGNED DRAFT (lane v3-spec). Successor of near-chunk-validation-d0-1 for the formally admitted STARK backend: RelD0a B0 = RelD0 ∧ A1 (c.gas_limit) ∧ A2 (w.proof_routing) ∧ Canon0f (e.sched_canonical) ∧ A7 (w.unfolded, B0 = 2,000,000) ∧ A8 (c.bw_requests), spec/near-chunk-validation-v0a.md, NearSpecV3.ChunkValidationV0a / ChallengeD0a (challengeSpecD0a, challengeParamsD0a); proof cap 8 MiB formal and operational (docs/zk-formal/V3-D0-DESIGN.md §10, §11). Workload generators and public fixtures as near-chunk-validation-d0 (all positives satisfy the amendments; checked with nearspec-v3-check-d0a); D0a difftest fixtures: oracle/fixtures/v3/public-d0a.",
        "created_at": a.created_at,
        "formal_params": {"verify_fuel": 1073741824, "max_proof_bytes": 8388608,
                          "max_reduction_fuel": 1073741824},
    }
    out = a.out
    open(out, "w").write(json.dumps(draft, indent=2) + "\n")
    print(out)

if __name__ == "__main__":
    main()
