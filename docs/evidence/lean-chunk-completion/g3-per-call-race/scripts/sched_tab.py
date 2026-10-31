#!/usr/bin/env python3
"""sched_tab.py RESULTS.jsonl : (Lean verdict, nearcore forced schedules, cold nearcore ok) counts."""
import json, os, sys, collections
c = collections.Counter()
for line in open(sys.argv[1]):
    r = json.loads(line)
    m = json.load(open(os.path.join(r["case"], "meta.json")))
    s = m.get("nearcore_schedule")
    if isinstance(s, dict):
        e, l = s["eager"] == "ok", s["lazy"] == "ok"
        k = "races" if e != l else ("ok" if e else "err")
    else:
        k = "none"
    v = r["verdict"]
    if v == "out_of_domain":
        v = "race" if "code_prep_race" in r["reason"] else "ood"
    c[(v, "schedules=" + k, "cold=" + ("ok" if m.get("nearcore") == "ok" else "err"))] += 1
for k, n in sorted(c.items()):
    print(*k, n)
