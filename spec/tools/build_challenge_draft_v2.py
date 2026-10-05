#!/usr/bin/env python3
"""Build challenges/drafts/near-transfer-receipt-v2.draft.json (UNSIGNED) for
statement near/pv86/receipt-transfer-batch/v1. The v1 draft/template/inputs are
not touched; the v1 template supplies only the policy skeleton (obligations,
security profile id).

Steps: (1) write the v2 workload generator specs, (2) optionally (re)compute the
held-out commitment from the off-repo held-out directory, (3) run
challenge_inputs_v2.py, (4) fill the draft. Then (governance, later):
  arena-admin check challenges/drafts/near-transfer-receipt-v2.draft.json
  arena-admin sign  ... --key <governance key>
"""
import argparse, datetime, json, os, subprocess, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from challenge_inputs import J, jcs, tree
import hashlib

def dig(v): return "sha256:" + hashlib.sha256(jcs(v).encode()).hexdigest()

CLASSES = [("batch-1", 1, 200000), ("batch-16", 16, 300000), ("batch-256", 256, 500000)]
PROFILES = "basic,prefix,boundary,repeat,prices,large,bw_state,trie_shapes,missed,shards"
NAME = "near-transfer-receipt-v2"
STATEMENT = "near/pv86/receipt-transfer-batch/v1"
# Generator specs written next to the suite but NOT part of the draft's
# workload_suite (no weight, no held-out set): adding one to a challenge is a
# governance decision. max-witness: the maximal in-domain witness class
# (spec/near-transfer-receipt-v2.md §13.1).
CANDIDATE_CLASSES = [("max-witness", 256, "max_witness")]

def oracle_source_digest():
    return tree("oracle/src", "oracle/Cargo.toml", "oracle/Cargo.lock", "oracle/NEARCORE_PIN")

def workload_spec(cid, r, profiles, oracle_digest):
    return {
        "schema": "near-arena-workload-generator-v1",
        "challenge": NAME,
        "class": cid,
        "receipts_per_request": r,
        "tool": "near-arena-oracle gen --scope v2",
        "args": ["--scope", "v2", "--receipts", str(r), "--profiles", profiles, "--fixtures-layout"],
        "seed": "fresh per run (judge-chosen after freeze); held-out set: secret seed",
        "oracle_source_tree_digest": oracle_digest,
        "nearcore_commit": "44f7ae6cd7ef08bab604e20a473bf77e35d4c993",
        "statement_id": STATEMENT,
    }

def write_spec(spec):
    p = J(f"spec/workloads/{NAME}/{spec['class']}.json")
    open(p, "w").write(json.dumps(spec, indent=1) + "\n")

def write_candidate_classes(oracle_digest):
    os.makedirs(J(f"spec/workloads/{NAME}"), exist_ok=True)
    for cid, r, profiles in CANDIDATE_CLASSES:
        write_spec(workload_spec(cid, r, profiles, oracle_digest))

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--created-at")
    ap.add_argument("--season", default="2026-s1")
    ap.add_argument("--heldout-dir", help="off-repo held-out set (oracle/scripts/gen-heldout-v2.sh output)")
    ap.add_argument("--candidate-classes-only", action="store_true",
                    help="only (re)write the non-governed CANDIDATE_CLASSES specs; governed files untouched")
    a = ap.parse_args()
    if a.candidate_classes_only:
        write_candidate_classes(oracle_source_digest())
        return
    out = J(f"challenges/drafts/{NAME}.draft.json")
    created = a.created_at or (json.load(open(out))["created_at"] if os.path.exists(out) else None)
    if not created:
        sys.exit("--created-at required for a new draft (RFC 3339 UTC)")

    oracle_digest = oracle_source_digest()
    gens = {}
    os.makedirs(J(f"spec/workloads/{NAME}"), exist_ok=True)
    for cid, r, _ in CLASSES:
        spec = workload_spec(cid, r, PROFILES, oracle_digest)
        write_spec(spec)
        gens[cid] = dig(spec)
    write_candidate_classes(oracle_digest)  # not referenced by the draft

    hc_path = J("spec/challenge-inputs/heldout-commitment-v2.json")
    if a.heldout_dir:
        td = subprocess.run([J("target/debug/arena-admin"), "tree-digest", a.heldout_dir],
                            capture_output=True, text=True, check=True).stdout.strip()
        hc = {
            "schema": "near-arena-heldout-commitment-v1",
            "challenge": NAME,
            "statement_id": STATEMENT,
            "tree_digest": td,
            "algorithm": "TreeDigest (docs/CONTRACTS.md §1; arena-admin tree-digest) of the held-out directory",
            "layout": "batch-{1,16,256}/{params.bin, cases/<name>/{request.bin,witness.bin,expected_claim.bin,state.bin,diagnostics.json}}",
            "cases_per_class": 24,
            "generated_with": "oracle/scripts/gen-heldout-v2.sh <secret seed file> <dir> (near-arena-oracle at the oracle source digest in the workload generator specs)",
            "oracle_source_tree_digest": oracle_digest,
            "seed": "secret; kept off-repo by the local operator until season end",
            "synthetic_state": True,
        }
        open(hc_path, "w").write(json.dumps(hc, indent=1) + "\n")
    held = json.load(open(hc_path))["tree_digest"]

    subprocess.run([sys.executable, J("spec/tools/challenge_inputs_v2.py")], check=True, capture_output=True)
    inp = json.load(open(J(f"spec/challenge-inputs/{NAME}.json")))
    t = json.load(open(J("challenges/templates/near-transfer-receipt-v1.template.json")))
    t.pop("_template_notice", None)
    prof = json.load(open(J("security/profiles/validity-classical-128.json")))
    lean_tc = inp["semantic_scope"]["formal_spec"]["lean_toolchain"]
    pkg_commit = subprocess.run(["git", "-C", J(), "log", "-1", "--format=%H", "--", "spec/lean", "formal-core"],
                                capture_output=True, text=True, check=True).stdout.strip()
    image = os.environ.get("CHECKER_IMAGE_DIGEST") or subprocess.run(
        [J("target/debug/formal-check"), "--print-image-digest"], capture_output=True, text=True, check=True).stdout.strip()
    ss = inp["semantic_scope"]
    t.update({
        "name": NAME,
        "season": a.season,
        "chain_id": inp["chain_id"],
        "protocol_version": inp["protocol_version"],
        "nearcore": inp["nearcore"],
        "runtime_config_digest": inp["runtime_config_digest"],
        "semantic_scope": {
            "name": ss["name"], "kind": ss["kind"], "granularity": ss["granularity"],
            "restrictions": ss["restrictions"], "excludes": ss["excludes"],
            "formal_spec": ss["formal_spec"], "spec_doc_digest": ss["spec_doc_digest"],
        },
        "claim_encoding": {k: inp["claim_encoding"][k] for k in
                           ("format", "spec_digest", "max_request_bytes", "max_witness_bytes", "max_claim_bytes")},
        "security_profile": prof,
        "toolchain_policy": {
            "lean_toolchain": lean_tc,
            "checker_image": image,
            "axiom_allowlist": ["propext", "Classical.choice", "Quot.sound"],
            "allowed_packages": [["ArenaCore", pkg_commit], ["NearSpec", pkg_commit]],
            "recheckers": ["leanchecker", "nanoda", "lean4lean"],
        },
        "hardware_profile": {
            "id": "nearproof-local-ryzen9-9950x3d",
            "cpu_model": "AMD Ryzen 9 9950X3D 16-Core Processor (local operator host; 8 vCPUs pinned per run)",
            "vcpus": 8, "ram_bytes": 34359738368, "gpu": None,
        },
        "workload_suite": {
            "revision": f"{NAME}-r1",
            "classes": [{"id": cid, "description": f"requests with exactly {r} single-Transfer receipt(s); generator profiles {PROFILES}",
                         "weight_ppm": w, "batch_size": 8, "generator": gens[cid]} for cid, r, w in CLASSES],
            "public_fixtures": inp["workload_suite"]["public_fixtures"],
            "heldout_commitment": held,
            "baseline_submission": None,
            "baseline_ns": [],
        },
        "measurement": {"warmup_runs": 3, "measured_runs": 15, "aggregation": "median", "outlier_mad_k": 5,
                        "cold_runs": 1, "concurrency": 1, "per_run_timeout_ms": 600000},
        "resource_limits": {
            "max_proof_bytes": 8388608, "max_verify_ms": 10000, "max_prove_ms": 600000,
            "max_ram_bytes": 17179869184, "max_vram_bytes": 0, "max_public_artifact_bytes": 67108864,
            "max_prepare_ms": 600000, "max_build_ms": 3600000,
        },
        "formal_params": {"verify_fuel": 1073741824, "max_proof_bytes": 8388608, "max_reduction_fuel": 1073741824},
        "supersedes": None,
        "created_at": created,
    })
    bad = [k for k, v in t.items() if "TODO" in json.dumps(v)]
    if bad:
        sys.exit(f"unfilled TODO in {bad}")
    os.makedirs(os.path.dirname(out), exist_ok=True)
    open(out, "w").write(json.dumps(t, indent=2, ensure_ascii=False) + "\n")
    print(out)

if __name__ == "__main__":
    main()
