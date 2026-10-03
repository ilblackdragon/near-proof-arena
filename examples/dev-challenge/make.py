#!/usr/bin/env python3
"""DEV-ONLY, UNSIGNED challenge definition for local `arena check-local` runs of
the examples/ candidates against `near/pv86/receipt-transfer-batch/v0`.

Filled from challenges/templates/near-transfer-receipt-v1.template.json and the
spec lane's spec/challenge-inputs/near-transfer-receipt-v1.json. Tier is
`experimental`, resource limits / baselines are local placeholders. The real
challenge is produced and signed by governance; candidates must then set
`challenge = <that id>`.
"""
import copy, hashlib, json, os

repo = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
t = json.load(open(os.path.join(repo, "challenges/templates/near-transfer-receipt-v1.template.json")))
inp = json.load(open(os.path.join(repo, "spec/challenge-inputs/near-transfer-receipt-v1.json")))
prof = json.load(open(os.path.join(repo, "security/profiles/validity-classical-128.json")))
d = copy.deepcopy(t)
d.pop("_template_notice")
dev = lambda s: "sha256:" + hashlib.sha256(s.encode()).hexdigest()
d["season"] = "dev-local"
d["tier"] = "experimental"
d["chain_id"] = inp["chain_id"]
d["runtime_config_digest"] = inp["runtime_config_digest"]
ss = inp["semantic_scope"]
d["semantic_scope"] = {
    "name": ss["name"], "kind": ss["kind"], "granularity": ss["granularity"],
    "restrictions": ss["restrictions"], "excludes": ss["excludes"],
    "formal_spec": {k: ss["formal_spec"][k] for k in ("relation_module", "relation_decl", "tree_digest", "lean_toolchain")},
    "spec_doc_digest": "sha256:" + hashlib.sha256(open(os.path.join(repo, "spec/near-transfer-receipt-v1.md"), "rb").read()).hexdigest(),
}
ce = inp["claim_encoding"]
d["claim_encoding"] = {k: ce[k] for k in ("format", "spec_digest", "max_request_bytes", "max_witness_bytes", "max_claim_bytes")}
d["security_profile"] = prof
d["toolchain_policy"] = {
    "lean_toolchain": inp["toolchain_policy"]["lean_toolchain"],
    "checker_image": dev("dev-local formal-checker image"),
    "axiom_allowlist": ["propext", "Classical.choice", "Quot.sound"],
    "allowed_packages": [["formal-core", "0" * 40], ["near-spec", "0" * 40]],
    "recheckers": ["lean4checker", "nanoda"],
}
d["hardware_profile"] = {"id": "dev-local-x86_64", "cpu_model": "local", "vcpus": 8, "ram_bytes": 17179869184, "gpu": None}
ws = inp["workload_suite"]
classes = [{"id": c["id"], "description": c["description"],
            "weight_ppm": w, "batch_size": 8, "generator": ws["generator_digest"]}
           for c, w in zip(ws["suggested_classes"], (400000, 200000, 400000))]
d["workload_suite"] = {
    "revision": "dev-local", "classes": classes, "public_fixtures": ws["public_fixtures"],
    "heldout_commitment": dev("dev-local heldout"), "baseline_submission": None,
    "baseline_ns": [[c["id"], 10_000_000] for c in classes],
}
d["measurement"]["per_run_timeout_ms"] = 60000
d["resource_limits"] = {
    "max_proof_bytes": 8388608, "max_verify_ms": 120000, "max_prove_ms": 60000,
    "max_ram_bytes": 4294967296, "max_vram_bytes": 0, "max_public_artifact_bytes": 1048576,
    "max_prepare_ms": 10000, "max_build_ms": 1800000,
}
d["created_at"] = "2026-10-03T00:00:00Z"
out = os.path.join(os.path.dirname(__file__), "near-transfer-receipt-v1.dev.json")
json.dump(d, open(out, "w"), indent=2)
open(out, "a").write("\n")
print(out)
