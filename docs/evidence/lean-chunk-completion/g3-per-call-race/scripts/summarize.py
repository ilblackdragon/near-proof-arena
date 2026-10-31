#!/usr/bin/env python3
"""summarize.py OUT.json : base (main, ee00c918) vs after (G3) on every population and tier."""
import collections, hashlib, json, os, sys

D = os.environ.get("REP", "/data/illia/nearproof-deps/g3-uncertain/rep")
POPS = ["fixtures", "census", "race", "raceprobe", "w08", "ethw", "shard13", "corpus"]
RACE = "out of domain (e.code_prep_race)"


def short(r):
    v = r["verdict"]
    if v == "out_of_domain":
        return "ood(race)" if r["reason"].startswith(RACE) else "ood"
    return v


def rows(path):
    d = {}
    for line in open(path):
        if line.strip():
            r = json.loads(line)
            d[os.path.realpath(r["case"])] = r
    return d


def near(case):
    try:
        m = json.load(open(os.path.join(case, "meta.json")))
    except OSError:
        return None
    n = m.get("nearcore")
    return None if n is None else ("ok" if n == "ok" else "err")


def sha(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()


def main():
    out = {}
    for pop in POPS:
        for t in ("allFeatures", "signed"):
            res = {}
            paths = {}
            for b in ("base", "after"):
                p = f"{D}/{b}-{pop}-{t}/results.jsonl"
                if pop == "shard13":
                    p = f"{D}/{b}-{pop}-{t}.jsonl"
                if not os.path.exists(p):
                    break
                paths[b] = p
                res[b] = rows(p)
            if len(res) < 2:
                continue
            b, a = res["base"], res["after"]
            assert set(b) == set(a), (pop, t)
            moves = collections.Counter()
            unsound = 0
            for c in b:
                nv = near(c)
                sb, sa = short(b[c]), short(a[c])
                if sa == "accept" and nv == "err":
                    unsound += 1
                if sb != sa or b[c]["reason"] != a[c]["reason"]:
                    moves[f"{sb} -> {sa} (nearcore {nv})"] += 1
            rep = {}
            for k in ("base", "after"):
                rp = f"{D}/{k}-{pop}-{t}/report.json"
                if os.path.exists(rp):
                    r = json.load(open(rp))
                    rep[k] = {"status": r.get("status"), "partition": r.get("partition")}
            out[f"{pop}/{t}"] = {
                "cases": len(b),
                "verdicts": {k: dict(collections.Counter(short(r) for r in v.values())) for k, v in res.items()},
                "moves": dict(moves), "after_accepts_of_nearcore_rejects": unsound,
                "harness": rep, "results_sha256": {k: sha(p) for k, p in paths.items()}}
    json.dump(out, open(sys.argv[1], "w"), indent=1, sort_keys=True)
    for k, v in out.items():
        print(k, v["cases"], v["verdicts"], v["moves"], "unsound", v["after_accepts_of_nearcore_rejects"],
              {x: y.get("status") for x, y in v["harness"].items()})


if __name__ == "__main__":
    main()
