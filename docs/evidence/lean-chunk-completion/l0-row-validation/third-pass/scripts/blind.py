"""Run a checker in normal and --blind mode over the honest gas-key cases; write overrides.json
(the --blind outputs of every honest case that the checker rejects in normal mode but evaluates
under --blind). Usage: blind.py CHECKER TIER OUT_PREFIX"""
import json, subprocess, sys
from pathlib import Path
chk, tier, pre = sys.argv[1], sys.argv[2], sys.argv[3]
G = Path("/data/illia/nearproof-deps/l0-validate/b4/gk")
cases = [l for l in (G / "honest-p1.txt").read_text().split() if l]
def run(extra):
    rows = {}
    for i in range(0, len(cases), 20):
        p = subprocess.run([chk, "--tier", tier, *extra, *cases[i:i + 20]], capture_output=True, text=True)
        for l in p.stdout.splitlines():
            if l.startswith("{"):
                r = json.loads(l); rows[r["case"]] = r
    return rows
norm, blind = run([]), run(["--blind"])
ov = {}
summary = []
for c in cases:
    n, b = norm.get(c, {}), blind.get(c, {})
    summary.append({"case": c, "verdict": n.get("verdict"), "reason": n.get("reason"),
                    "blind": b.get("verdict"), "blind_reason": b.get("reason")})
    if n.get("verdict") == "reject" and b.get("verdict") == "accept" and b.get("outputs"):
        o = b["outputs"]
        ov.setdefault(Path(c).parent.parent.name.replace("p1-", "", 1), {})[Path(c).name] = {k: o[k] for k in ("stateRoot", "outcomeRoot", "gasUsed", "balanceBurnt", "outgoingReceiptsRoot")}
(G / f"{pre}-honest.json").write_text(json.dumps(summary, indent=1) + "\n")
if pre == "before-allFeatures":
    for run, o in ov.items():
        (G / f"overrides-{run}.json").write_text(json.dumps(o, indent=1) + "\n")
import collections
print(collections.Counter((s["case"].split("/gk/")[1].split("-")[1], s["verdict"], (s["reason"] or "")[:60], s["blind"]) for s in summary))
print("overrides", {k: len(v) for k, v in ov.items()})
