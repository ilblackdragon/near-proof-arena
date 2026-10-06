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

`--price-model PM.json` (either mode) also writes `scoring` (cost_v1,
BENCHMARK_SPEC §14.6): the model inline + its JCS digest, and `cost_baseline`
from the same session (prove_ns = the pinned baseline_ns). It refuses unless
the summary carries at least one passing verify drift control
(`run_baseline.py --control-sessions N`, §14.4) and the model is `governed`.
"""
import argparse, hashlib, json, sys


def with_cost_scoring(new, summary, pm_path):
    """Fill `scoring` (cost_v1) from the session that supplied baseline_ns."""
    pm = json.load(open(pm_path))
    if pm.get("status") != "governed":
        sys.exit(f"price model {pm.get('id')}@v{pm.get('version')} is {pm.get('status')!r}, not governed")
    if summary["calibration"]["ok"] is not True or summary.get("flags"):
        sys.exit("the pinned session is infra-invalid (calibration/flags): refusing to pin a cost baseline")
    # infra-invalid control sessions (§6.1 calibration failed, flagged) do not count
    vc = [v for v in summary.get("verify_control") or [] if v.get("valid")]
    if not vc:
        sys.exit("no valid verify drift control in the summary (run_baseline.py --control-sessions N): refusing to pin a cost baseline")
    if not all(v["ok"] for v in vc):
        sys.exit(f"verify drift control failed {[(v['session'], v['reasons']) for v in vc]}: re-measure, refusing to pin")
    cb = sorted(summary["cost_baseline"], key=lambda c: c["class_id"])
    base = dict(new["workload_suite"]["baseline_ns"])
    if {c["class_id"] for c in cb} != set(base) or any(base[c["class_id"]] != c["prove_ns"] for c in cb):
        sys.exit("cost_baseline does not match the pinned baseline_ns (one session must supply both)")
    if any(c["verify_ns"] is None or c["verify_ns"] <= 0 or c["proof_bytes"] is None for c in cb):
        sys.exit(f"cost_baseline incomplete: {cb}")
    jcs_ = lambda v: json.dumps(v, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    new["scoring"] = {
        "kind": "cost_v1",
        "price_model": pm,
        "price_model_digest": "sha256:" + hashlib.sha256(jcs_(pm).encode()).hexdigest(),
        "cost_baseline": [{k: c[k] for k in ("class_id", "prove_ns", "verify_ns", "proof_bytes")} for c in cb],
    }
    return new


# Mode 2 (`--base`): the session measured an unsigned successor draft whose
# baseline is still null (e.g. one that also changes the procedure or the
# checker pin); the output is that draft with ONLY the baseline filled in.
if "--base" in sys.argv:
    ap = argparse.ArgumentParser()
    ap.add_argument("--base", required=True)
    ap.add_argument("--summary", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--price-model", default=None)
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
    if a.price_model:
        new = with_cost_scoring(new, s, a.price_model)
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
ap.add_argument("--price-model", default=None)
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
if a.price_model:
    new = with_cost_scoring(new, s, a.price_model)

changed = sorted(k for k in set(old) | set(new) if old.get(k) != new.get(k))
expect = (["name", "workload_suite", "supersedes", "created_at"] + (["measurement"] if mode != old_mode else [])
          + (["scoring"] if a.price_model else []))
assert changed == sorted(expect), changed
if mode != old_mode:
    m_changed = sorted(k for k in set(old["measurement"]) | set(new["measurement"])
                       if old["measurement"].get(k) != new["measurement"].get(k))
    assert m_changed == ["invocation_mode"], m_changed
ws_changed = sorted(k for k in old["workload_suite"] if old["workload_suite"][k] != new["workload_suite"][k])
assert set(ws_changed) <= {"baseline_ns", "baseline_submission"} and "baseline_ns" in ws_changed, ws_changed
open(a.out, "w").write(json.dumps(new, indent=2, ensure_ascii=False) + "\n")
print(a.out, "supersedes", old_id, "baseline_ns", base)
