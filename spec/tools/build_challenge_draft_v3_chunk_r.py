#!/usr/bin/env python3
"""Build challenges/drafts/near-chunk-v3-1.draft.json (unsigned): `near-chunk-v3` v3.1.

Decision 2026-10-30 (owner, option 1 of docs/evidence/lean-chunk-completion/proof-debt/
d1-genesis-flag/README.md): the rungs of the statement are restrictions of the top relation,
`RelRungDk := RelD3 ∧ InRungDk` (spec/lean/v3/NearSpecV3/Rungs.lean). The statement becomes
`NearSpecV3.RelChunkV3R` (spec/lean/v3/NearSpecV3/ChallengeChunkV3R.lean, `relChunkV3R_iff : ↔ RelD3`),
the tiers are admitted under `NearSpecV3.challengeParamsChunkR <tier>` and soundness lifts by
`NearSpecV3.sound_liftR`.

Everything else (workload classes and their generator pins, restrictions, fixtures, profiles,
limits, runtime config) is carried over unchanged from challenges/drafts/near-chunk-v3.draft.json,
which this draft supersedes; only the formal statement fields, `formal_spec.tree_digest`
(TreeDigest(spec/lean formal-core) of the working tree's tracked files: commit spec/ first) and
`supersedes` change. The published/signed challenge files are not touched.

UQ-010 item 6(c) (user decision 2026-10-30, lane 6): the raised `max_witness_bytes` (=
`ChallengeChunkV3.maxWitnessChunk` = 75,497,501) and the dropped resharding / storage-proof / secp
restrictions are applied by `near_chunk_v3_uq010.apply` (spec/tools/near_chunk_v3_uq010.py).

usage: build_challenge_draft_v3_chunk_r.py [--out PATH]
"""
import argparse, json, os, subprocess, sys

ROOT = subprocess.run(["git", "rev-parse", "--show-toplevel"], capture_output=True, text=True,
                      check=True, cwd=os.path.dirname(os.path.abspath(__file__))).stdout.strip()


def tree(*paths):
    return subprocess.run([sys.executable, os.path.join(ROOT, "spec/tools/tree_digest.py"), *paths],
                          capture_output=True, text=True, check=True, cwd=ROOT).stdout.strip()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=os.path.join(ROOT, "challenges/drafts/near-chunk-v3-1.draft.json"))
    a = ap.parse_args()
    base = json.load(open(os.path.join(ROOT, "challenges/drafts/near-chunk-v3.draft.json")))
    d = json.loads(json.dumps(base))
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import near_chunk_v3_uq010
    near_chunk_v3_uq010.apply(d)
    d["name"] = "near-chunk-v3-1"
    d["supersedes"] = "near-chunk-v3 (challenges/drafts/near-chunk-v3.draft.json, unsigned draft)"
    fs = d["semantic_scope"]["formal_spec"]
    fs["relation_module"] = "NearSpecV3.ChallengeChunkV3R"
    fs["relation_decl"] = "NearSpecV3.RelChunkV3R"
    fs["tree_digest"] = tree("spec/lean", "formal-core")
    cov = d["coverage"]
    cov["statement_spec"] = "NearSpecV3.challengeSpecChunkTopR"
    cov["soundness_lift"] = "NearSpecV3.sound_liftR"
    for t in cov["tiers"]:
        assert t["params"].startswith("NearSpecV3.challengeParamsChunk "), t
        t["params"] = t["params"].replace("NearSpecV3.challengeParamsChunk ", "NearSpecV3.challengeParamsChunkR ")
    json.dump(d, open(a.out, "w"), indent=2, ensure_ascii=False)
    open(a.out, "a").write("\n")
    print(a.out, fs["tree_digest"])


if __name__ == "__main__":
    main()
