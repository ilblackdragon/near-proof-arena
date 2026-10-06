#!/usr/bin/env python3
"""Build challenges/drafts/near-chunk-v3.draft.json (unsigned) and the workload generator specs
spec/workloads/near-chunk-v3/<class>.json for the D1 / D2 / D3α classes.

`near-chunk-v3` ("NEAR chunk state-transition succinct proof") is ONE coverage-tiered challenge
(docs/CONTRACTS.md §11, docs/BENCHMARK_SPEC.md §17): statement `near/pv86/chunk-validation/v0` over the
largest formalized domain, `NearSpecV3.RelChunkV3 = RelD0 ∨ RelD1 ∨ RelD2 ∨ D3.RelD3`
(`spec/lean/v3/NearSpecV3/ChallengeChunkV3.lean`); candidates declare a tier D0 / D1 / D2 / D3a and are
admitted under `NearSpecV3.challengeParamsChunk <tier>` (soundness for `Rel_t`, completeness on
`Domain_t`); soundness lifts to the statement by `NearSpecV3.sound_lift`.

  build_challenge_draft_v3_chunk.py [--freeze-commit SHA] [--heldout-commitment sha256:…]
                                    [--baseline-summary benchmarks/results/<s>/summary.json]
                                    [--created-at RFC3339] [--measure] [--out PATH]

Digests, computed from the repository (tracked files; commit spec/, oracle/ and fixtures first):
  runtime_config_digest   = sha256(JCS(spec/challenge-inputs/runtime-config-pv86-v3-d2.json))
                            (`near-arena-oracle-v3-d1 params --d1 --d2`: every parameter D0–D2 read,
                            plus sha256 of nearcore's whole RuntimeConfigView at PV 86, which covers the
                            WASM config D3α reads); params.bin domain id `D3a` (spec/tools/params_bin_v3.py)
  formal_spec.tree_digest = TreeDigest(spec/lean formal-core) at --freeze-commit (default: the working
                            tree's tracked files); it includes every D0–D3α module, ChallengeChunkV3 and
                            the judge templates
  spec_doc_digest         = sha256 of the concatenation of spec/near-chunk-validation-v0.md and the
                            d1 / d2 / d3 domain documents (listed in `spec_docs`)
  public_fixtures         = TreeDigest(oracle/fixtures/v3/public-chunk-v3) (spec/tools/
                            build_public_chunk_v3.sh: the union of the D0 arena-public set and the arena
                            layouts of public-d1, public-d2 and public-d3, one params.bin)
  Rejection-case rule (fixtures and held-out): the statement is RelChunkV3 = RelD0 ∨ RelD1 ∨ RelD2 ∨
                            RelD3 (= Rel ∧ InD3α), so a rejection case must be false at EVERY tier: a
                            case nearcore rejects (false for Rel), or an honest chunk outside InD3α
                            (the D3 oracle's classifier; D0 ⊂ D1 ⊂ D2 ⊂ D3α, tested) — never a D0/D1/D2
                            "rejection" that nearcore accepts (an out-of-lower-domain chunk may be a
                            true claim of the union: 75 such public cases were RelD3-true). From the
                            D0-D2 sources only nearcore-rejected cases are kept; every kept rejection
                            is re-checked: checkD3 accepts none (public: 0/244; held-out: 0/64)
  generator               = sha256(JCS(generator spec)); D0 classes reuse the signed D0 challenge's specs
                            (spec/workloads/near-chunk-validation-d0, oracle/v3 source pinned there);
                            D1/D2 specs pin TreeDigest(oracle/v3-d1 src, Cargo.toml, Cargo.lock) + the
                            shared oracle/v3/src; D3 specs additionally oracle/v3-d3
  weight_source           = workload_suite.weight_source (contracts v1.7, CONTRACTS §11): status ASSUMED,
                            the documented assumption (WEIGHT_SOURCE) and ref = the weights record
                            spec/challenge-inputs/near-chunk-v3-weights.json; a measured mix from mainnet
                            replay is a follow-up (a versioned successor with status MEASURED)

Judge workers (runners/worker NearV3Oracle): each generator spec's `tool` selects the binary
(ARENA_NEAR_ORACLE_V3 / _D1 / _D3); judge-sampled rejections use the D3α recipe on the D3 oracle.

Checklist when the draft id changes (any edit here) and again after signing (the signed id is the id of
the final definition: created_at, held-out commitment, baseline and scoring filled in):
  [ ] examples/reexec-v3-d3/candidate.toml                               challenge = "<id>"
  [ ] adversarial/hostile-submissions/near-v3-d3-lenient-codes/candidate.toml   challenge = "<id>"
  (cargo test -p proof-mutators --test packages checks both against this draft or a signed
  challenges/chl_<id>.json of near-chunk-v3)
"""
import argparse, hashlib, json, os, subprocess, sys

ROOT = subprocess.run(["git", "rev-parse", "--show-toplevel"], capture_output=True, text=True,
                      check=True, cwd=os.path.dirname(os.path.abspath(__file__))).stdout.strip()


def jcs(v): return json.dumps(v, separators=(",", ":"), sort_keys=True, ensure_ascii=False)
def dig(v): return "sha256:" + hashlib.sha256(jcs(v).encode()).hexdigest()
def fdig(p): return "sha256:" + hashlib.sha256(open(os.path.join(ROOT, p), "rb").read()).hexdigest()


def tree(*paths):
    return subprocess.run([sys.executable, os.path.join(ROOT, "spec/tools/tree_digest.py"), *paths],
                          capture_output=True, text=True, check=True, cwd=ROOT).stdout.strip()


def tree_at(commit, *paths):
    """TreeDigest of `paths` as frozen at `commit`: refuses unless the working tree's `paths` equal
    the commit's (tracked and untracked), then hashes them (tree_digest.py hashes tracked files)."""
    d = subprocess.run(["git", "diff", "--quiet", commit, "--", *paths], cwd=ROOT)
    u = subprocess.run(["git", "ls-files", "--others", "--exclude-standard", "--", *paths],
                       capture_output=True, text=True, cwd=ROOT).stdout.strip()
    n = subprocess.run(["git", "diff", "--quiet", "--cached", commit, "--", *paths], cwd=ROOT)
    if d.returncode or n.returncode or u:
        raise SystemExit(f"{' '.join(paths)} differ from the freeze commit {commit}: freeze again")
    return tree(*paths)


R = lambda i, t: {"id": i, "text": t}
# InD3α (spec/near-chunk-validation-d3.md §10, §10.0a; D2 §12; v0 §6), the largest tier = the statement.
RESTRICTIONS = [
    R("c.pv86", "protocol_version = 86 (nearcore 2.13.4) for every epoch of the claim, mainnet runtime parameters RuntimeConfigStore::new(None).get_config(86)"),
    R("c.layout", "the epoch's shard layout is ShardLayout V2 or V3 with 1..=64 shards"),
    R("c.same_layout", "all epochs of the claim have the byte-identical shard layout (no resharding); no non-empty outgoing buffer to a shard outside the layout"),
    R("c.headers", "block headers V6; chunk header inners V4/V5"),
    R("c.no_split_gate", "no dynamic-resharding split check for any applied block"),
    R("c.not_genesis", "the last new chunk of the shard is not the genesis chunk"),
    R("c.segment", "the chain segment has at most 32 blocks"),
    R("w.size", "state witness <= 8 MiB; sum of the main transition's base_state values and the contract code blobs + 2000 x ContractData removals <= 4,000,000 bytes (the storage-proof limit never triggers)"),
    R("w.shape", "no DeployGlobalContract / UseGlobalContract / DeterministicStateInit action, no GlobalContractDistribution receipt, no ML-DSA-65 key in any decoded transaction or receipt (incl. receipts created by contracts); transactions carry ED25519 keys and signatures"),
    R("e.secp", "no SECP256K1 Delegate signature is verified"),
    R("e.scheduler_state", "the BandwidthSchedulerState value is absent or decodes as V1"),
    R("e.wasm_alpha", "every executed contract prepares inside D3α: integer WASM only (no float type or opcode); no executed FunctionCall calls a curve host function (alt_bn128_*, bls12381_*, ecrecover, p256_verify) or a state-init / global-contract / gas-key host function (importing them is allowed); no unmodeled VM outcome"),
    R("e.global_code", "every FunctionCall receiver's contract is None or Local (global identifiers out of domain); no FunctionCall on an ETH-implicit account with a Local contract (legacy-wallet resolution)"),
    R("e.code_cache", "cold-cache statement: the code of every executed pre-state contract must be in the witness (else reject); out of domain when such a blob is absent and the same code was deployed earlier in the chunk (committed or rolled back): nearcore's verdict then depends on its compiled-contract cache"),
    R("e.g_alpha", "the chunk's sum of gas_burnt_for_function_call (incl. host gas) <= G_alpha = 2^22 x 822,756 gas (NearSpecV3.D3.gAlpha), checked after the main transition"),
]
EXCLUDES = ["block_finality", "data_availability", "chunk_producer_signatures",
            "witness_transport_and_part_decoding", "trusted_epoch_facts_correctness",
            "compiled_contract_cache_dependent_verdicts", "float_wasm_and_curve_host_functions",
            "global_contracts_and_state_init", "mldsa_and_secp256k1_transactions",
            "resharding", "dynamic_resharding_split_search", "genesis_main_transition",
            "witnesses_above_G_alpha", "other_protocol_versions"]

# (class, tier, weight_ppm, domain, generator args (without --seed/--out/--d0-target), description)
D0_SPECS = "spec/workloads/near-chunk-validation-d0"
CLASSES = [
    ("d0-quiet", "D0", 20000, "d0", None,
     "D0 chunks with no incoming receipt and no implicit transition: context authentication, empty main transition, bandwidth scheduler, congestion info, Reed-Solomon encoded merkle root"),
    ("d0-transfers", "D0", 30000, "d0", None,
     "D0 chunks applying >= 1 incoming cross-shard Transfer receipt, no implicit transition"),
    ("d0-missing", "D0", 30000, "d0", None,
     "D0 chunks after >= 1 missing chunk of the shard (implicit transitions), chains with 25% chunk skips"),
    ("d1-transfers", "D1", 50000, "d1", ["--rotate", "--chains", "6", "--blocks", "40", "--mutate-every", "0", "--ood-cap", "0"],
     "D1 chunks whose last chunk's Transfer transactions all succeed (cross-shard and local self-transfers, V0/V1, monotonic/strict nonces)"),
    ("d1-mixed", "D1", 20000, "d1", ["--rotate", "--chains", "6", "--blocks", "40", "--mutate-every", "0", "--ood-cap", "0"],
     "D1 chunks with >= 1 Transfer transaction that fails validation or is skipped (an adversarial chunk producer's crafted validity classes: signatures, nonces, keys, balances, expiry, duplicates)"),
    ("d1-receipts", "D1", 30000, "d1", ["--rotate", "--chains", "6", "--blocks", "40", "--mutate-every", "0", "--ood-cap", "0"],
     "D1 chunks without transactions in the last chunk (incoming Transfer receipts, new_transactions only, missing chunks) on D1 chains"),
    ("d2-actions", "D2", 80000, "d2", ["--chains", "3", "--blocks", "60", "--mutate-every", "0", "--ood-cap", "0", "--drop-cap", "0"],
     "D2 chunks with every non-WASM action kind, multi-action receipts, Delegate, refunds, data / yield receipts, no queue or epoch feature"),
    ("d2-queues", "D2", 60000, "d2", ["--chains", "3", "--blocks", "60", "--mutate-every", "0", "--ood-cap", "0", "--drop-cap", "0"],
     "D2 chunks with a non-empty delayed-receipt queue or outgoing buffer before or after the chunk (congestion, bandwidth requests)"),
    ("d2-epoch", "D2", 30000, "d2", ["--chains", "3", "--blocks", "60", "--mutate-every", "0", "--ood-cap", "0", "--drop-cap", "0"],
     "D2 chunks whose segment crosses an epoch boundary or applies a ValidatorAccountsUpdate (validator proposals, stakes)"),
    ("d3-calls", "D3a", 300000, "d3", ["--chains", "3", "--blocks", "60", "--mutate-every", "0", "--code-mutant-p", "0", "--ood-cap", "0", "--drop-cap", "0"],
     "D3a chunks executing >= 1 WASM FunctionCall without callbacks: storage reads/writes/removes, logs, value returns, cross-contract promises, deploy-and-call, gas exhaustion, failures"),
    ("d3-callbacks", "D3a", 150000, "d3", ["--chains", "3", "--blocks", "60", "--mutate-every", "0", "--code-mutant-p", "0", "--ood-cap", "0", "--drop-cap", "0"],
     "D3a chunks with callbacks (promise_then / promise_and joins, promise results, yields and resumes)"),
    ("d3-nonwasm", "D3a", 50000, "d3", ["--chains", "3", "--blocks", "60", "--mutate-every", "0", "--code-mutant-p", "0", "--ood-cap", "0", "--drop-cap", "0"],
     "D3a chunks that execute no WASM (D2 traffic around contract state: deploys, yield timeouts, forwarded FunctionCall receipts)"),
    ("d3-maxgas", "D3a", 150000, "d3", ["--chains", "3", "--blocks", "60", "--mutate-every", "0", "--code-mutant-p", "0", "--ood-cap", "0", "--drop-cap", "0"],
     "max-G_alpha class: D3a chunks whose function-call gas is >= G_alpha / 2 (the heaviest chunks a D3a proof must carry)"),
]
WEIGHT_SOURCE = (
    "Documented assumption (no measured per-chunk mix of these features exists in the repository yet): "
    "mainnet traffic is dominated by FunctionCalls, so the D3a classes carry 65% (calls 30%, callbacks 15%, "
    "max-G_alpha 15%, non-WASM chunks around contract state 5%); non-WASM receipts/queues/epochs (D2) 17%; "
    "plain transfer transactions (D1) 10%; quiet / transfer-receipt / missing-chunk D0 chunks 8%. To be replaced "
    "by a measured mix from mainnet replay (docs/HISTORICAL_REPLAY.md) in a versioned successor.")
TIERS = [("D0", 0, ".d0"), ("D1", 1, ".d1"), ("D2", 2, ".d2"), ("D3a", 3, ".d3a")]
TIER_RANK = {t: r for t, r, _ in TIERS}

ORACLE_TREES = {
    "d1": ["oracle/v3-d1/src", "oracle/v3-d1/Cargo.toml", "oracle/v3-d1/Cargo.lock", "oracle/v3/src"],
    "d2": ["oracle/v3-d1/src", "oracle/v3-d1/Cargo.toml", "oracle/v3-d1/Cargo.lock", "oracle/v3/src"],
    "d3": ["oracle/v3-d3/src", "oracle/v3-d3/Cargo.toml", "oracle/v3-d3/Cargo.lock", "oracle/v3-d3/contracts",
           "oracle/v3-d1/src", "oracle/v3/src"],
}
TOOLS = {"d1": "near-arena-oracle-v3-d1 gen", "d2": "near-arena-oracle-v3-d1 gen", "d3": "near-arena-oracle-v3-d3 gen"}
SPEC_DOCS = ["spec/near-chunk-validation-v0.md", "spec/near-chunk-validation-d1.md",
             "spec/near-chunk-validation-d2.md", "spec/near-chunk-validation-d3.md"]


def generator_spec(cid, dom, args):
    return {
        "schema": "near-arena-workload-generator-v1",
        "challenge": "near-chunk-v3",
        "class": cid,
        "tool": TOOLS[dom],
        "args": ["--domain", dom, "--fixtures-layout", "--class", cid, *args],
        "seed": "judge-chosen per run (season-secret HMAC, BENCHMARK_SPEC §11.1); --d0-target = number of positives; held-out set: secret seed",
        "oracle_source_tree_digest": tree(*ORACLE_TREES[dom]),
        "oracle_source_tree": ORACLE_TREES[dom],
        "nearcore_commit": "44f7ae6cd7ef08bab604e20a473bf77e35d4c993",
        "statement_id": "near/pv86/chunk-validation/v0",
        "domain": {"d1": "D1", "d2": "D2", "d3": "D3a"}[dom],
        "class_predicate": "oracle/v3-d1/src/arena.rs class_of",
    }


def d0_generator(cid):
    spec = json.load(open(os.path.join(ROOT, D0_SPECS, cid + ".json")))
    return dig(spec)


CALIBRATION = {"workload": "arena-calibrate-v1",
               "binary_digest": "sha256:d434077860be66ff66d849dc58595134bbaad882c0761437d988551baeb65e37",
               "expected_checksum": "87a7f539b09c4e7b", "threads": 8, "steps_per_probe": 5,
               "edge_probes": 2, "max_step_ppm": 20000, "max_noise_ppm": 50000}

PRICE_MODEL = "challenges/price-models/pm-near-mainnet-2026q4.v2.json"


def scoring(a):
    pm = json.load(open(os.path.join(ROOT, PRICE_MODEL)))
    # bench-spec-v1.6 / contracts v1.8: paired baseline control (the reference re-run on the same
    # sampled batches in the same session, BENCHMARK_SPEC §6.2, §14.12)
    sc = {"kind": "cost_v1", "price_model": pm, "price_model_digest": dig(pm),
          "verify_statistic": "lower_quartile", "baseline_mode": "paired"}
    if a.baseline_summary and not a.measure:
        bs = json.load(open(a.baseline_summary))
        if "cost_baseline" in bs:
            sc["cost_baseline"] = bs["cost_baseline"]
    return sc


WEIGHTS_REF = "spec/challenge-inputs/near-chunk-v3-weights.json"


def write_weights():
    """The class weights and their source, as a record (spec/challenge-inputs/near-chunk-v3-weights.json);
    the challenge carries the source itself as workload_suite.weight_source (BENCHMARK_SPEC §17)."""
    w = {"schema": "near-arena-class-weights-v1", "challenge": "near-chunk-v3",
         "weight_source": WEIGHT_SOURCE,
         "classes": [{"id": c[0], "tier": c[1], "weight_ppm": c[2]} for c in CLASSES],
         "spec_docs": SPEC_DOCS}
    open(os.path.join(ROOT, WEIGHTS_REF), "w").write(json.dumps(w, indent=1) + "\n")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--freeze-commit", default=None)
    ap.add_argument("--heldout-commitment", default=None)
    ap.add_argument("--baseline-summary", default=None)
    ap.add_argument("--created-at", default="2026-10-06T18:00:00Z")
    ap.add_argument("--checker-image", default="sha256:66b014d4e05744bcf21771c469f93d119a0d24a5dc4288d28cb46126c4bf1867")
    ap.add_argument("--measure", action="store_true", help="baseline-measurement draft (no baseline)")
    ap.add_argument("--out", default=None)
    a = ap.parse_args()
    write_weights()
    wdir = os.path.join(ROOT, "spec/workloads/near-chunk-v3")
    os.makedirs(wdir, exist_ok=True)
    classes = []
    for cid, tier, w, dom, args, desc in CLASSES:
        if dom == "d0":
            g = d0_generator(cid)
        else:
            spec = generator_spec(cid, dom, args)
            open(os.path.join(wdir, cid + ".json"), "w").write(json.dumps(spec, indent=1) + "\n")
            g = dig(spec)
        classes.append({"id": cid, "description": f"[{tier}] {desc}", "weight_ppm": w, "batch_size": 8,
                        "generator": g})
    assert sum(c["weight_ppm"] for c in classes) == 1000000
    tiers = []
    for tid, rank, lean in TIERS:
        tiers.append({"id": tid, "rank": rank, "params": f"NearSpecV3.challengeParamsChunk {lean}",
                      "classes": [c[0] for c in CLASSES if TIER_RANK[c[1]] <= rank]})
    baseline_sub, baseline_ns = None, []
    if a.baseline_summary and not a.measure:
        bs = json.load(open(a.baseline_summary))
        baseline_sub = bs["reference_candidate"]["package_digest"]
        baseline_ns = bs["baseline_ns"]
    tree_digest = tree_at(a.freeze_commit, "spec/lean", "formal-core") if a.freeze_commit else tree("spec/lean", "formal-core")
    if a.freeze_commit:
        a.freeze_commit = subprocess.run(["git", "rev-parse", a.freeze_commit + "^{commit}"], capture_output=True,
                                         text=True, check=True, cwd=ROOT).stdout.strip()
    allowed = [] if not a.freeze_commit else [[p, a.freeze_commit] for p in ("ArenaCore", "NearSpec", "NearSpecV3")]
    rc = json.load(open(os.path.join(ROOT, "spec/challenge-inputs/runtime-config-pv86-v3-d2.json")))
    docs = b"".join(open(os.path.join(ROOT, p), "rb").read() for p in SPEC_DOCS)
    draft = {
        "schema": "arena-challenge-v1",
        "name": "near-chunk-v3",
        "season": "2026-s1",
        "tier": "formal",
        "nearcore": {"repo": "https://github.com/near/nearcore", "tag": "2.13.4",
                     "commit": "44f7ae6cd7ef08bab604e20a473bf77e35d4c993"},
        "protocol_version": 86,
        # synthetic-chain claims (nearcore TestEnv, chain_id arena-v3-local, mainnet parameters), as D0
        "chain_id": "arena-v3-local",
        "runtime_config_digest": dig(rc),
        "semantic_scope": {
            "name": "near/pv86/chunk-validation/v0#D3a",
            "kind": "subset",
            "granularity": "chunk_validation",
            "restrictions": RESTRICTIONS,
            "excludes": EXCLUDES,
            "formal_spec": {
                "relation_module": "NearSpecV3.ChallengeChunkV3",
                "relation_decl": "NearSpecV3.RelChunkV3",
                "tree_digest": tree_digest,
                "lean_toolchain": "leanprover/lean4:v4.34.1"},
            "spec_doc_digest": "sha256:" + hashlib.sha256(docs).hexdigest(),
        },
        "claim_encoding": {"format": "near-arena-claim-v3", "spec_digest": fdig("spec/claim-v3.md"),
                           # witness.bin = state witness (<= 8 MiB) + code blobs (<= 4,000,000 B by w.size)
                           "max_request_bytes": 1048576, "max_witness_bytes": 12582912,
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
        "hardware_profile": {"id": "nearproof-local-ryzen9-9950x3d",
                             "cpu_model": "AMD Ryzen 9 9950X3D 16-Core Processor (local operator host; 8 vCPUs pinned per run)",
                             "vcpus": 8, "ram_bytes": 34359738368, "gpu": None},
        "workload_suite": {
            "revision": "near-chunk-v3-r1",
            "classes": classes,
            "public_fixtures": tree("--relative-to", "oracle/fixtures/v3/public-chunk-v3", "oracle/fixtures/v3/public-chunk-v3")
            if os.path.isdir(os.path.join(ROOT, "oracle/fixtures/v3/public-chunk-v3")) else None,
            "heldout_commitment": a.heldout_commitment,
            "baseline_submission": baseline_sub,
            "baseline_ns": baseline_ns,
            # v1.7 (serialized only when present): the weights are a documented assumption
            "weight_source": {"status": "ASSUMED", "note": WEIGHT_SOURCE, "ref": WEIGHTS_REF}},
        "measurement": {"warmup_runs": 3, "measured_runs": 15, "aggregation": "median", "outlier_mad_k": 5,
                        "cold_runs": 1, "concurrency": 1, "per_run_timeout_ms": 600000,
                        "invocation_mode": "vm_per_batch",
                        # pinned calibration binary with in-session probes (bench-spec-v1.6 §6.1)
                        "calibration": CALIBRATION},
        # caps: as D0 except verify: the D3a re-execution reference runs checkD3 once per needed code
        # blob plus once; measured on the public set (one case, 6 parallel jobs on CPUs 8-15,24-31):
        # verify median 0.04-0.37 s per class, max 3.1 s; prove max 2.4 s; proof <= 182 KB
        # (docs/e2e-results/v3-d3-reference). 60 s per 8-case batch leaves ~2.5x headroom over 8 x max.
        "resource_limits": {"max_proof_bytes": 67108864, "max_verify_ms": 60000, "max_prove_ms": 600000,
                            "max_ram_bytes": 17179869184, "max_vram_bytes": 0,
                            "max_public_artifact_bytes": 67108864, "max_prepare_ms": 600000,
                            "max_build_ms": 3600000},
        "supersedes": None,
        "created_at": a.created_at,
        "formal_params": {"verify_fuel": 1073741824, "max_proof_bytes": 67108864,
                          "max_reduction_fuel": 1073741824},
        # rank: declared coverage tier first, then cost_v1 (CONTRACTS §11, BENCHMARK_SPEC §14/§17);
        # cost_baseline comes from the reference measurement on CPUs 0-7 (--baseline-summary)
        "coverage": {
            "version": "coverage-v1",
            "statement_spec": "NearSpecV3.challengeSpecChunkTop",
            "soundness_lift": "NearSpecV3.sound_lift",
            "tiers": tiers,
        },
    }
    sc = scoring(a)
    if "cost_baseline" in sc:
        # cost_v1 needs a cost_baseline for every class (arena-admin policy): only once the reference
        # was measured on CPUs 0-7; until then the draft has no scoring section (placeholder)
        draft["scoring"] = sc
    if a.measure:
        draft["workload_suite"]["baseline_submission"] = None
        draft["workload_suite"]["baseline_ns"] = []
    out = a.out or os.path.join(ROOT, "challenges/drafts/near-chunk-v3" + (".measure" if a.measure else ".draft") + ".json")
    open(out, "w").write(json.dumps(draft, indent=2) + "\n")
    print(out)


if __name__ == "__main__":
    main()
