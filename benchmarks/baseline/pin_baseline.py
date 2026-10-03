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

# Mode 2 (`--base`): the session measured an unsigned successor draft whose
# baseline is still null (e.g. one that also changes the procedure or the
# checker pin); the output is that draft with ONLY the baseline filled in.
if "--base" in sys.argv:
    ap = argparse.ArgumentParser()
    ap.add_argument("--base", required=True)
    ap.add_argument("--summary", required=True)
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    jcs = lambda v: json.dumps(v, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    base = json.load(open(a.base))
    bid = "chl_" + hashlib.sha256(jcs(base).encode()).hexdigest()[:32]
    s = json.load(open(a.summary))
    if s["challenge_id"] != bid:
        sys.exit(f"summary measured {s['challenge_id']}, not the draft {bid}")
    ws = base["workload_suite"]
    if ws["baseline_submission"] is not None or ws["baseline_ns"]:
        sys.exit("draft already has a baseline")
    if s["calibration"]["ok"] is not True:
        sys.exit(f"session calibration failed ({s['calibration']['reasons']}): infra-invalid, refusing to pin")
    if s.get("flags"):
        sys.exit(f"session flags {s['flags']}: refusing to pin")
    if any(g["status"] != "PASS" for g in s["gates"].values()):
        sys.exit(f"gates not PASS: {s['gates']}")
    classes = {c["id"] for c in ws["classes"]}
    b = sorted((cid, ns) for cid, ns in s["baseline_ns"])
    if {c for c, _ in b} != classes or any(ns <= 0 for _, ns in b):
        sys.exit(f"baseline_ns {b} does not cover {sorted(classes)}")
    new = json.loads(json.dumps(base))
    new["workload_suite"]["baseline_submission"] = s["reference_candidate"]["package_digest"]
    new["workload_suite"]["baseline_ns"] = [[c, ns] for c, ns in b]
    open(a.out, "w").write(json.dumps(new, indent=2, ensure_ascii=False) + "\n")
    print(a.out, "measured on", bid, "baseline_ns", b)
    sys.exit(0)


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
# a procedure change (bench-spec-v1.1 invocation mode) is carried from the session
mode = s.get("invocation_mode", "vm_per_invocation")
old_mode = old["measurement"].get("invocation_mode") or "vm_per_invocation"
if mode != old_mode:
    new["measurement"]["invocation_mode"] = mode
new["created_at"] = a.created_at

changed = sorted(k for k in set(old) | set(new) if old.get(k) != new.get(k))
expect = ["name", "workload_suite", "supersedes", "created_at"] + (["measurement"] if mode != old_mode else [])
assert changed == sorted(expect), changed
if mode != old_mode:
    m_changed = sorted(k for k in set(old["measurement"]) | set(new["measurement"])
                       if old["measurement"].get(k) != new["measurement"].get(k))
    assert m_changed == ["invocation_mode"], m_changed
ws_changed = sorted(k for k in old["workload_suite"] if old["workload_suite"][k] != new["workload_suite"][k])
assert set(ws_changed) <= {"baseline_ns", "baseline_submission"} and "baseline_ns" in ws_changed, ws_changed
open(a.out, "w").write(json.dumps(new, indent=2, ensure_ascii=False) + "\n")
print(a.out, "supersedes", old_id, "baseline_ns", base)
