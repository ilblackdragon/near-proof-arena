#!/usr/bin/env python3
"""Build challenges/drafts/near-transfer-receipt-v1.draft.json from
challenges/templates/near-transfer-receipt-v1.template.json and the spec-lane
inputs. Deterministic given the git tree (except `created_at`, taken from
--created-at or the existing draft).

Steps: (1) write the workload generator specs, (2) run challenge_inputs.py,
(3) fill every TODO of the template. Then:
  arena-admin check challenges/drafts/near-transfer-receipt-v1.draft.json
  arena-admin sign  ... --key /data/illia/nearproof-deps/keys/governance-local.key
"""
import argparse, hashlib, json, os, subprocess, sys

REPO = subprocess.run(["git", "rev-parse", "--show-toplevel"], capture_output=True, text=True, check=True).stdout.strip()
J = lambda *p: os.path.join(REPO, *p)
def jcs(v): return json.dumps(v, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
def dig(v): return "sha256:" + hashlib.sha256(jcs(v).encode()).hexdigest()
def tree(*paths, rel=None):
    cmd = [sys.executable, J("spec/tools/tree_digest.py")] + (["--relative-to", J(rel)] if rel else []) + [J(p) for p in paths]
    return subprocess.run(cmd, capture_output=True, text=True, check=True).stdout.strip()

CLASSES = [("batch-1", 1, 200000), ("batch-16", 16, 300000), ("batch-256", 256, 500000)]
PROFILES = "basic,prefix,boundary,repeat,prices,large"

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--created-at")
    ap.add_argument("--season", default="2026-s1")
    a = ap.parse_args()
    out = J("challenges/drafts/near-transfer-receipt-v1.draft.json")
    created = a.created_at or (json.load(open(out))["created_at"] if os.path.exists(out) else None)
    if not created:
        sys.exit("--created-at required for a new draft (RFC 3339 UTC)")

    oracle_digest = tree("oracle/src", "oracle/Cargo.toml", "oracle/Cargo.lock", "oracle/NEARCORE_PIN")
    gens = {}
    os.makedirs(J("spec/workloads/near-transfer-receipt-v1"), exist_ok=True)
    for cid, r, _ in CLASSES:
        spec = {
            "schema": "near-arena-workload-generator-v1",
            "challenge": "near-transfer-receipt-v1",
            "class": cid,
            "receipts_per_request": r,
            "tool": "near-arena-oracle gen",
            "args": ["--receipts", str(r), "--profiles", PROFILES, "--fixtures-layout"],
            "seed": "fresh per run (judge-chosen after freeze); held-out set: secret seed",
            "oracle_source_tree_digest": oracle_digest,
            "nearcore_commit": "44f7ae6cd7ef08bab604e20a473bf77e35d4c993",
            "statement_id": "near/pv86/receipt-transfer-batch/v0",
        }
        p = J(f"spec/workloads/near-transfer-receipt-v1/{cid}.json")
        open(p, "w").write(json.dumps(spec, indent=1) + "\n")
        gens[cid] = dig(spec)

    subprocess.run([sys.executable, J("spec/tools/challenge_inputs.py")], check=True, capture_output=True)
    inp = json.load(open(J("spec/challenge-inputs/near-transfer-receipt-v1.json")))
    held = json.load(open(J("spec/challenge-inputs/heldout-commitment.json")))["tree_digest"]
    t = json.load(open(J("challenges/templates/near-transfer-receipt-v1.template.json")))
    t.pop("_template_notice", None)
    prof = json.load(open(J("security/profiles/validity-classical-128.json")))
    lean_tc = inp["semantic_scope"]["formal_spec"]["lean_toolchain"]
    pkg_commit = subprocess.run(["git", "-C", REPO, "log", "-1", "--format=%H", "--", "spec/lean", "formal-core"],
                                capture_output=True, text=True, check=True).stdout.strip()
    image = os.environ.get("CHECKER_IMAGE_DIGEST")
    if not image:
        image = subprocess.run([J("target/debug/formal-check"), "--print-image-digest"], capture_output=True,
                               text=True, check=True).stdout.strip()
    ss = inp["semantic_scope"]
    t.update({
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
            "revision": "near-transfer-receipt-v1-r1",
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
    open(out, "w").write(json.dumps(t, indent=2, ensure_ascii=False) + "\n")
    print(out)

if __name__ == "__main__":
    main()
