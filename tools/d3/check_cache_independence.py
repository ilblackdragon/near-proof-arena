#!/usr/bin/env python3
"""UQ-001 test: inside the Lean domain, nearcore's verdict does not depend on a coherent compiled cache.

Input: case directories whose `meta.json` carries `nearcore` (the cold reference judge) and
`nearcore_probe` = {"warm", "poisoned"} (oracle/v3-successor `code-cache` scenario,
src/cachejudge.rs), and the Lean rows of one tier (`nearspec-v3-check-successor --tier T` JSONL).

The statement under test (docs/evidence/lean-chunk-completion/w08-warm-cache/README.md):
  * Lean accept                                 => warm == cold == accept;
  * Lean reject, reason not missing contract code => warm == cold == reject;
  * Lean reject `MissingTrieValue (contract code)` / `w.code_complete`: the cold-cache class; warm
    may differ (this is the class the statement assigns to the cold cache, and the positive control
    that the probe sees cache effects at all);
  * Lean out of domain: not compared.
Breakage control: the poisoned (incoherent) cache must differ from cold on some in-domain case, or
the probe could not detect a cache-dependent verdict. The script exits non-zero when the statement
fails or the control detects nothing.
"""
import argparse
import collections
import json
import sys
from pathlib import Path

MISSING = ("invalid: MissingTrieValue (contract code)", "invalid witness (w.code_complete)")


def ok(v):
    return v == "ok"


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--lean", type=Path, required=True, help="Lean JSONL rows (case, verdict, reason)")
    ap.add_argument("--out", type=Path, required=True)
    a = ap.parse_args()
    rows = [json.loads(l) for l in a.lean.read_text().splitlines() if l.strip()]
    tab = collections.Counter()
    bad, poison_hits, warm_hits, examples = [], 0, 0, {}
    for r in rows:
        m = json.loads((Path(r["case"]) / "meta.json").read_text())
        p = m.get("nearcore_probe")
        if not p:
            tab["no_probe"] += 1
            continue
        cold, warm, poison = ok(m["nearcore"]), ok(p["warm"]), ok(p["poisoned"])
        v, reason = r["verdict"], r.get("reason") or ""
        if v == "out_of_domain":
            cls = "lean_ood"
        elif v == "accept":
            cls = "lean_accept"
        elif reason.startswith(MISSING):
            cls = "lean_reject_missing_code"
        else:
            cls = "lean_reject_other"
        key = (cls, "cold_" + ("ok" if cold else "err"), "warm_" + ("ok" if warm else "err"),
               "poisoned_" + ("ok" if poison else "err"))
        tab[key] += 1
        examples.setdefault(key, r["case"])
        if cls in ("lean_accept", "lean_reject_other"):
            if warm != cold or (cls == "lean_accept") != cold:
                bad.append({"case": r["case"], "class": cls, "cold": m["nearcore"], "warm": p["warm"]})
            if poison != cold:
                poison_hits += 1
        if cls == "lean_reject_missing_code" and warm != cold:
            warm_hits += 1
    report = {
        "lean_rows": a.lean.name, "cases": len(rows),
        "table": [{"key": list(k) if isinstance(k, tuple) else [k], "n": n, "example": examples.get(k)}
                  for k, n in sorted(tab.items(), key=lambda kv: -kv[1])],
        "statement_violations": bad,
        "control_poisoned_differs_in_domain": poison_hits,
        "positive_control_warm_differs_on_missing_code": warm_hits,
        "status": "pass" if not bad and poison_hits > 0 else "fail",
    }
    a.out.write_text(json.dumps(report, indent=1) + "\n")
    print(json.dumps({k: report[k] for k in ("cases", "status", "control_poisoned_differs_in_domain",
                                            "positive_control_warm_differs_on_missing_code")}),
          "violations", len(bad))
    return 0 if report["status"] == "pass" else 1


if __name__ == "__main__":
    sys.exit(main())
