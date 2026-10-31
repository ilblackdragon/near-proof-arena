#!/usr/bin/env python3
"""cmp.py BEFORE.jsonl AFTER.jsonl [--out OUT.json]

Per-case verdict moves between two checker runs on the same population, against nearcore's cold
verdict and (where the oracle recorded it) nearcore's forced eager/lazy schedules
(`nearcore_schedule`, oracle/v3-successor/src/cachejudge.rs)."""
import json, sys, collections, os

RACE = "out of domain (e.code_prep_race)"


def load(p):
    d = {}
    for line in open(p):
        line = line.strip()
        if not line:
            continue
        r = json.loads(line)
        d[os.path.realpath(r["case"])] = r
    return d


def short(r):
    v = r["verdict"]
    if v == "out_of_domain":
        if r["reason"].startswith(RACE):
            return "ood(race)"
        return "ood"
    return v


def meta(case):
    try:
        return json.load(open(os.path.join(case, "meta.json")))
    except Exception:
        return {}


def near(m):
    n = m.get("nearcore")
    if n is None:
        e = m.get("expected_rel")
        return None if e is None else ("ok" if e else "err")
    return "ok" if n == "ok" else "err"


def sched(m):
    s = m.get("nearcore_schedule")
    if not isinstance(s, dict):
        return None
    e, l = s.get("eager"), s.get("lazy")
    if (e == "ok") != (l == "ok"):
        return "verdict_races"
    if e != l:
        return "failure_point_races"
    return "same"


def main():
    b, a = load(sys.argv[1]), load(sys.argv[2])
    out = sys.argv[sys.argv.index("--out") + 1] if "--out" in sys.argv else None
    assert set(b) == set(a), (len(b), len(a), len(set(b) ^ set(a)))
    moves = collections.Counter()
    unsound = []
    moved_rows = []
    race_after = collections.Counter()
    race_rows = []
    for c in sorted(b):
        m = meta(c)
        nv = near(m)
        sb, sa = short(b[c]), short(a[c])
        moves[(sb, sa, nv)] += 1
        if sa == "accept" and nv == "err":
            unsound.append(c)
        if sb != sa or b[c]["reason"] != a[c]["reason"]:
            moved_rows.append({"case": c, "before": [b[c]["verdict"], b[c]["reason"]],
                               "after": [a[c]["verdict"], a[c]["reason"]], "nearcore": nv,
                               "schedule": sched(m), "labels": m.get("d3_violations")})
        if sa == "ood(race)":
            race_after[(nv, sched(m), tuple(m.get("d3_violations") or ()))] += 1
            race_rows.append({"case": c, "nearcore": nv, "schedule": sched(m),
                              "nearcore_schedule": m.get("nearcore_schedule"),
                              "labels": m.get("d3_violations")})
    res = {"cases": len(b),
           "moves": [{"before": k[0], "after": k[1], "nearcore": k[2], "n": v}
                     for k, v in sorted(moves.items(), key=lambda kv: (str(kv[0])))],
           "after_accept_of_nearcore_reject": unsound,
           "race_exclusions_after": [{"nearcore": k[0], "schedule": k[1], "labels": list(k[2]), "n": v}
                                     for k, v in sorted(race_after.items(), key=lambda kv: str(kv[0]))],
           "race_rows_after": race_rows,
           "moved_rows": moved_rows}
    if out:
        json.dump(res, open(out, "w"), indent=1)
    print(f"cases {len(b)}; moved {len(moved_rows)}; accepts of nearcore rejects after: {len(unsound)}")
    for k, v in sorted(moves.items(), key=lambda kv: str(kv[0])):
        if k[0] != k[1]:
            print(f"  {k[0]:>10} -> {k[1]:<10} nearcore {k[2]}: {v}")
    print("race exclusions after:")
    for k, v in sorted(race_after.items(), key=lambda kv: str(kv[0])):
        print(f"  nearcore {k[0]} schedule {k[1]} labels {list(k[2])}: {v}")


if __name__ == "__main__":
    main()
