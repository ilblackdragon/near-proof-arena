#!/usr/bin/env python3
"""Full-runtime difftest of RuntimeD3: the Lean checker `nearspec-v3-check-d3` (checkD3) and, with
--python, the independent Python checker `oracle/tools/spec_check_v3_d3.py` vs nearcore's verdicts in
a D3 corpus (oracle/v3-d3; meta.json `expected_rel` = nearcore, `in_d3`).

  difftest_d3.py CORPUS [--sample N] [--shards K] [--only d3|mutants|ood] [--python] [--no-lean]
                        [--save DIR] [--lean-from FILE] [--python-from FILE]

A case disagrees with nearcore when (in D3α by the oracle) the checker's verdict differs from
nearcore (accept vs reject), or when the checker says out_of_domain for an in-D3α case, or when it
decides an oracle-out-of-D3α case differently from nearcore. The oracle's classifier marks the two
§10.0 domain conditions (spec/near-chunk-validation-d3.md §10.0-§10.1): `e.code_cache` (code mutants,
meta `in_d3` / `d3_violations`) and `e.g_alpha`. The checker must agree with it on both: a checker
`out_of_domain (e.g_alpha)` / code-cache verdict must coincide with the oracle's violation (an
earlier checker out-of-domain or reject may pre-empt the G_α check, which runs after the main
transition), and a checker never accepts a case the oracle puts above G_α. With --python the Lean-vs-Python
verdict differences (accept / reject / out_of_domain) are listed as a third comparison.

Checkers run as K parallel processes with file-based input lists and outputs (no pipes).
--save DIR keeps the per-case JSON lines (lean.jsonl, python.jsonl); --lean-from / --python-from reuse
such a file instead of running that checker."""
import collections
import json
import os
import random
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.environ.get("D3_CHECK", os.path.join(HERE, "../../wasm-d3/lean/.lake/build/bin/nearspec-v3-check-d3"))
PY = os.path.join(HERE, "../../tools/spec_check_v3_d3.py")


def run_checker(name, dirs, shards, td):
    """Lean takes case dirs as arguments; Python takes --list FILE. Both print one JSON line per case."""
    procs = []
    for s in range(shards):
        part = dirs[s::shards]
        if not part:
            continue
        lst = os.path.join(td, f"{name}-in{s}")
        with open(lst, "w") as f:
            f.write("\n".join(part) + "\n")
        out = open(os.path.join(td, f"{name}-out{s}"), "w")
        err = open(os.path.join(td, f"{name}-err{s}"), "w")
        if name == "lean":
            cmd = [LEAN] + part
        else:
            cmd = [sys.executable, PY, "--list", lst]
        procs.append((subprocess.Popen(cmd, stdout=out, stderr=err, stdin=subprocess.DEVNULL), out, err))
    for p, out, err in procs:
        p.wait()
        out.close()
        err.close()
    got = {}
    for s in range(shards):
        fn = os.path.join(td, f"{name}-out{s}")
        if os.path.exists(fn):
            for line in open(fn):
                line = line.strip()
                if line.startswith("{"):
                    j = json.loads(line)
                    got[j["case"]] = j
        en = os.path.join(td, f"{name}-err{s}")
        if os.path.exists(en) and os.path.getsize(en):
            txt = open(en).read()
            if "INTERNAL ERROR" in txt or "Traceback" in txt:
                print(f"[{name} shard {s} stderr]\n" + txt[:4000], file=sys.stderr)
    return got


def boundary(reason):
    r = reason or ""
    if "code_cache" in r or "compiled-contract cache" in r:
        return "code_cache"
    if "g_alpha" in r or "gAlpha" in r or "G_α" in r or "e_alpha" in r:
        return "g_alpha"
    return None


def compare(label, dirs, metas, got):
    stats = collections.Counter()
    bad = []
    for d in dirs:
        m = metas[d]
        fam = os.path.basename(os.path.dirname(d))
        g = got.get(d, {"verdict": "missing", "reason": ""})
        v = g["verdict"]
        near = m.get("expected_rel")
        ind3 = m.get("in_d3", m.get("expected_rel_d3") is not None and not m.get("d3_violations"))
        stats[(fam, v, "nearcore_ok" if near else "nearcore_rej")] += 1
        viol = m.get("d3_violations") or []
        b = boundary(g.get("reason")) if v == "out_of_domain" else None
        # the two §10.0 conditions: oracle classifier and checker must agree
        o_ga, c_ga = "e.g_alpha" in viol, b == "g_alpha"
        if o_ga or c_ga:
            stats[("g_alpha", "oracle" if o_ga else "-", label if c_ga else v)] += 1
        if (c_ga and not o_ga) or (o_ga and v == "accept"):
            bad.append((d, f"G_α: oracle {o_ga}, {label} {v}", g.get("reason"),
                        m.get("features", {}).get("fc_gas_burnt_for_function_call")))
            continue
        o_cc, c_cc = "e.code_cache" in viol, b == "code_cache"
        if o_cc or c_cc:
            stats[("code_cache", "oracle" if o_cc else "-", label if c_cc else v, "nearcore_ok" if near else "nearcore_rej")] += 1
        if o_cc != c_cc:
            bad.append((d, f"code cache: oracle {o_cc}, {label} {v}", g.get("reason"), m.get("nearcore")))
            continue
        if v == "out_of_domain":
            if ind3 and fam != "ood":
                bad.append((d, f"{label} out_of_domain on an in-D3α case", g.get("reason"), m.get("nearcore")))
            continue
        if v == "missing" or (v == "accept") != bool(near):
            if fam == "ood" and v != "missing":
                stats[(f"ood_decided_by_{label}", v, str(near))] += 1
                bad.append((d, f"{label} {v} vs nearcore {near} (oracle: out of D3α)", g.get("reason"),
                            m.get("nearcore")))
                continue
            bad.append((d, f"{label} {v} vs nearcore {near}", g.get("reason"), m.get("nearcore")))
        elif fam == "ood":
            stats[(f"ood_decided_by_{label}", v, str(near))] += 1
    return stats, bad


def main():
    corpus = sys.argv[1]
    arg = lambda n, d: sys.argv[sys.argv.index(n) + 1] if n in sys.argv else d  # noqa: E731
    sample = int(arg("--sample", "0"))
    shards = int(arg("--shards", "8"))
    only = arg("--only", "")
    save = arg("--save", "")
    use_py = "--python" in sys.argv
    use_lean = "--no-lean" not in sys.argv
    dirs = []
    for fam in ("d3", "mutants", "ood"):
        if only and fam != only:
            continue
        p = os.path.join(corpus, fam)
        if os.path.isdir(p):
            dirs += [os.path.join(p, d) for d in sorted(os.listdir(p))]
    if sample and sample < len(dirs):
        random.Random(1).shuffle(dirs)
        dirs = sorted(dirs[:sample])
    metas = {d: json.load(open(os.path.join(d, "meta.json"))) for d in dirs}
    results = {}
    def load(fn):
        got = {}
        for line in open(fn):
            j = json.loads(line)
            got[j["case"]] = j
        return got
    lean_from, py_from = arg("--lean-from", ""), arg("--python-from", "")
    with tempfile.TemporaryDirectory(dir=os.environ.get("TMPDIR")) as td:
        if lean_from:
            results["lean"] = load(lean_from)
        elif use_lean:
            results["lean"] = run_checker("lean", dirs, shards, td)
        if py_from:
            results["python"] = load(py_from)
        elif use_py:
            # shuffle so that expensive cases spread over the shards
            pd = list(dirs)
            random.Random(7).shuffle(pd)
            results["python"] = run_checker("python", pd, shards, td)
    if save:
        os.makedirs(save, exist_ok=True)
        for name, got in results.items():
            with open(os.path.join(save, f"{name}.jsonl"), "w") as f:
                for d in dirs:
                    if d in got:
                        f.write(json.dumps(got[d]) + "\n")
    total_bad = 0
    for name, got in results.items():
        stats, bad = compare(name, dirs, metas, got)
        print(f"==== {name} vs nearcore")
        for k, c in sorted(stats.items(), key=str):
            print(k, c)
        print(f"{name}: cases={len(dirs)} disagreements_with_nearcore={len(bad)}")
        for b in bad[:20]:
            print("DISAGREE", *b, sep="\n  ")
        total_bad += len(bad)
    if "lean" in results and "python" in results:
        L, P = results["lean"], results["python"]
        pairs = collections.Counter()
        diff = []
        for d in dirs:
            lv = L.get(d, {}).get("verdict", "missing")
            pv = P.get(d, {}).get("verdict", "missing")
            pairs[(lv, pv)] += 1
            if lv != pv:
                diff.append((d, lv, pv, L.get(d, {}).get("reason"), P.get(d, {}).get("reason")))
        print("==== lean vs python")
        for k, c in sorted(pairs.items()):
            print(f"lean={k[0]} python={k[1]}: {c}")
        print(f"lean-vs-python: cases={len(dirs)} disagreements={len(diff)}")
        for x in diff[:20]:
            print("LEAN≠PY", x[0], f"lean={x[1]} ({x[3]})", f"python={x[2]} ({x[4]})", sep="\n  ")
        total_bad += len(diff)
    sys.exit(1 if total_bad else 0)


main()
