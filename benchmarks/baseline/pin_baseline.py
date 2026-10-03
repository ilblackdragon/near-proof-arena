#!/usr/bin/env python3
"""Write the draft of a successor challenge that pins measured baselines.

The draft is the superseded challenge verbatim except:
  name                                   --name
  workload_suite.baseline_submission     the reference package digest (summary.json)
  workload_suite.baseline_ns             per-class steady-state medians (summary.json), sorted by class id
  supersedes                             the old challenge id
  created_at                             --created-at (must be later than the old one)

Every semantic field (nearcore pin, protocol version, runtime config, scope,
formal spec, claim encoding, security profile, toolchain, workloads,
measurement, limits) is left untouched, and the script checks that.
Then sign it with `arena-admin supersede` (see benchmarks/baseline/README.md).
"""
import argparse, hashlib, json, sys


def jcs(v):
    return json.dumps(v, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


ap = argparse.ArgumentParser()
ap.add_argument("--old", required=True)
ap.add_argument("--summary", required=True)
ap.add_argument("--name", required=True)
ap.add_argument("--created-at", required=True)
ap.add_argument("--out", required=True)
a = ap.parse_args()

old = json.load(open(a.old))
old_id = "chl_" + hashlib.sha256(jcs(old).encode()).hexdigest()[:32]
s = json.load(open(a.summary))
if s["challenge_id"] != old_id:
    sys.exit(f"summary measured {s['challenge_id']}, not {old_id}")
if s["suite_revision"] != old["workload_suite"]["revision"]:
    sys.exit("suite revision mismatch")
classes = {c["id"] for c in old["workload_suite"]["classes"]}
base = sorted((cid, ns) for cid, ns in s["baseline_ns"])
if {c for c, _ in base} != classes or any(ns <= 0 for _, ns in base):
    sys.exit(f"baseline_ns {base} does not cover classes {sorted(classes)}")

new = json.loads(json.dumps(old))
new["name"] = a.name
new["workload_suite"]["baseline_submission"] = s["reference_candidate"]["package_digest"]
new["workload_suite"]["baseline_ns"] = [[c, ns] for c, ns in base]
new["supersedes"] = old_id
new["created_at"] = a.created_at

changed = sorted(k for k in set(old) | set(new) if old.get(k) != new.get(k))
assert changed == sorted(["name", "workload_suite", "supersedes", "created_at"]), changed
ws_changed = sorted(k for k in old["workload_suite"] if old["workload_suite"][k] != new["workload_suite"][k])
assert ws_changed == ["baseline_ns", "baseline_submission"], ws_changed
open(a.out, "w").write(json.dumps(new, indent=2, ensure_ascii=False) + "\n")
print(a.out, "supersedes", old_id, "baseline_ns", base)
