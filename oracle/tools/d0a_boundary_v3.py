#!/usr/bin/env python3
"""Boundary conformance of the measured D0a bounds (A7 `w.unfolded`, A9 `e.chacha_words`,
A10 `w.path_depth`).

For every case that is in D0a at the challenge bounds (Lean verdict `accept`), with V the
case's own measured value (Lean: `unfold`, `chacha_words`, `max_path_depth`), both checkers
are run with that bound set to V (must accept: just in domain) and, when V >= 1, to V - 1
(must report out_of_domain naming that family: just out of domain). This exercises the exact
comparison of each conjunct (`unfoldBytes <= B`, `chachaWords <= W`, every path `<= Dp`) at
its boundary on real witnesses. Cases are grouped by value so each checker runs once per
(bound, value) group. The constant bounds themselves (B0, W0 = 770,000, Dp0 = 32) are far
above every generated case except for the A10 path-depth mutants, which sit at Dp0 and
Dp0 + 1 (see difftest_v3_d0a.py).

usage: d0a_boundary_v3.py --lean EXE --python FILE [--report OUT.json] [--lean-jsonl F]
                          [--families w.unfolded,e.chacha_words,w.path_depth] CASE_DIR...
       (--lean-jsonl: reuse a Lean run at the default bounds to select the cases)
"""
import argparse, collections, json, subprocess, sys

BOUNDS = {  # family -> (checker flag, Lean/Python JSON field)
    "w.unfolded": ("--bound", "unfold"),
    "e.chacha_words": ("--words-bound", "chacha_words"),
    "w.path_depth": ("--depth-bound", "max_path_depth"),
}


def run(cmd, dirs, chunk=300):
    out = {}
    for i in range(0, len(dirs), chunk):
        p = subprocess.run(cmd + dirs[i:i + chunk], capture_output=True, text=True, check=True)
        for line in p.stdout.splitlines():
            j = json.loads(line)
            out[j["case"]] = j
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--lean", required=True)
    ap.add_argument("--python", required=True)
    ap.add_argument("--report")
    ap.add_argument("--lean-jsonl", nargs="*")
    ap.add_argument("--families", default=",".join(BOUNDS))
    ap.add_argument("cases", nargs="+")
    a = ap.parse_args()
    if a.lean_jsonl:
        base = {}
        for f in a.lean_jsonl:
            for line in open(f):
                j = json.loads(line)
                base[j["case"]] = j
    else:
        base = run([a.lean], a.cases)
    inside = [d for d in a.cases if base.get(d, {}).get("verdict") == "accept"]
    report = {"cases": len(a.cases), "in_d0a": len(inside), "families": {}}
    ok_all = True
    for fam, (flag, field) in BOUNDS.items():
        if fam not in a.families.split(","):
            continue
        groups = collections.defaultdict(list)
        for d in inside:
            groups[base[d][field]].append(d)
        st = {"cases": len(inside), "values": len(groups), "at_bound_ok": 0,
              "below_tested": 0, "below_ok": 0, "below_skipped_zero": len(groups.get(0, [])),
              "failures": []}
        for v, ds in sorted(groups.items()):
            for name, cmd in (("lean", [a.lean]), ("python", [sys.executable, a.python])):
                at = run(cmd + [flag, str(v)], ds)
                for d in ds:
                    if at[d]["verdict"] != "accept":
                        st["failures"].append({"case": d, "impl": name, "bound": v, "got": at[d]})
                if v >= 1:
                    below = run(cmd + [flag, str(v - 1)], ds)
                    for d in ds:
                        j = below[d]
                        if not (j["verdict"] == "out_of_domain" and fam in j["reason"]):
                            st["failures"].append({"case": d, "impl": name, "bound": v - 1, "got": j})
            # count per case (both checkers)
            bad = {f["case"] for f in st["failures"]}
            st["at_bound_ok"] += sum(1 for d in ds if d not in bad)
            if v >= 1:
                st["below_tested"] += len(ds)
                st["below_ok"] += sum(1 for d in ds if d not in bad)
        st["failure_count"] = len(st["failures"])
        ok_all &= not st["failures"]
        report["families"][fam] = st
    summary = {fam: {k: v for k, v in st.items() if k != "failures"} for fam, st in report["families"].items()}
    print(json.dumps({"cases": report["cases"], "in_d0a": report["in_d0a"], "families": summary}, indent=1))
    if a.report:
        open(a.report, "w").write(json.dumps(report, indent=1, sort_keys=True) + "\n")
    return 0 if ok_all else 1


if __name__ == "__main__":
    sys.exit(main())
