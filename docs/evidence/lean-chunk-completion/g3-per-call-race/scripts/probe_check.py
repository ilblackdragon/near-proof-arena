#!/usr/bin/env python3
"""probe_check.py BASE.jsonl AFTER.jsonl OUT.json

For the pipeline-race family: join each case with its regenerated copy under probe/ (same seed and
command, NEAR_SCHEDULE_PROBE_ALL=1, byte-identical claim/witness checked here), whose meta carries
nearcore's forced eager and lazy verdicts (`nearcore_schedule`). Asserts:
  R1  every race exclusion after the change has eager and lazy verdicts that differ;
  R2  every case the change decides (was race-excluded, now accept/reject) has the same verdict
      under eager, lazy and the cold judge, and Lean's verdict equals it;
  R3  no accept of a case any schedule rejects."""
import hashlib, json, os, sys, collections

SRC = "/data/illia/nearproof-deps/w12-runs/"
PRB = "/data/illia/nearproof-deps/g3-uncertain/probe/"
RACE = "out of domain (e.code_prep_race)"


def load(p):
    d = {}
    for line in open(p):
        if line.strip():
            r = json.loads(line)
            d[os.path.realpath(r["case"])] = r
    return d


def h(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()


def main():
    base, after = load(sys.argv[1]), load(sys.argv[2])
    out = {"R1_violations": [], "R2_violations": [], "R3_violations": [], "missing_probe": [],
           "bytes_differ": [], "remaining_races": [], "newly_decided": collections.Counter()}
    for c, a in sorted(after.items()):
        rel = os.path.relpath(c, SRC)
        pc = os.path.join(PRB, rel)
        try:
            m = json.load(open(os.path.join(pc, "meta.json")))
        except OSError:
            out["missing_probe"].append(rel)
            continue
        for f in ("claim.bin", "witness.bin"):
            if h(os.path.join(c, f)) != h(os.path.join(pc, f)):
                out["bytes_differ"].append(rel)
        s = m.get("nearcore_schedule")
        if not isinstance(s, dict):
            out["missing_probe"].append(rel)
            continue
        e_ok, l_ok = s["eager"] == "ok", s["lazy"] == "ok"
        cold_ok = m.get("nearcore") == "ok"
        b = base[c]
        if a["verdict"] == "out_of_domain" and a["reason"].startswith(RACE):
            out["remaining_races"].append({"case": rel, "eager": s["eager"][:80], "lazy": s["lazy"][:80]})
            if e_ok == l_ok:
                out["R1_violations"].append(rel)
        if a["verdict"] == "accept" and not (e_ok and l_ok and cold_ok):
            out["R3_violations"].append(rel)
        if b["verdict"] == "out_of_domain" and b["reason"].startswith(RACE) and a["verdict"] != "out_of_domain":
            want = "accept" if cold_ok else "reject"
            out["newly_decided"][f"{a['verdict']} eager={'ok' if e_ok else 'err'} lazy={'ok' if l_ok else 'err'}"] += 1
            if not (e_ok == l_ok == cold_ok and a["verdict"] == want):
                out["R2_violations"].append(rel)
    out["newly_decided"] = dict(out["newly_decided"])
    out["cases"] = len(after)
    json.dump(out, open(sys.argv[3], "w"), indent=1)
    print({k: (len(v) if isinstance(v, list) else v) for k, v in out.items()})


if __name__ == "__main__":
    main()
