#!/usr/bin/env python3
"""Before/after per-case verdict comparison of two replay `results.jsonl` files, with nearcore's
expectation (`meta.json` expected_rel). Usage: beforeafter.py NAME BEFORE AFTER [CASES_FILE]"""
import collections
import json
import sys
from pathlib import Path

name, before, after = sys.argv[1:4]
only = None
if len(sys.argv) > 4:
    only = {str(Path(l).resolve()) for l in Path(sys.argv[4]).read_text().splitlines() if l}


def load(p):
    out = {}
    for l in Path(p).read_text().splitlines():
        if l:
            r = json.loads(l)
            out[str(Path(r["case"]).resolve())] = (r["verdict"], r["reason"])
    return out


b, a = load(before), load(after)
keys = sorted(set(a) if only is None else (set(a) & only))
missing = [k for k in keys if k not in b]
moved = collections.Counter()
ex = {}
agree = collections.Counter()
for k in keys:
    if k not in b:
        continue
    e = json.loads((Path(k) / "meta.json").read_text()).get("expected_rel")
    vb, va = b[k], a[k]
    for tag, v in (("before", vb), ("after", va)):
        if v[0] != "out_of_domain" and type(e) is bool:
            agree[f"{tag}: {'agree' if (v[0] == 'accept') == e else 'DISAGREE'} (lean {v[0]}, nearcore {'accept' if e else 'reject'})"] += 1
        else:
            agree[f"{tag}: out_of_domain"] += 1
    if vb != va:
        key = f"{vb[0]} -> {va[0]} (nearcore {'accept' if e else 'reject'})"
        moved[key] += 1
        ex.setdefault(key, (k, vb[1][:100], va[1][:100]))
out = dict(name=name, cases=len(keys), missing_before=len(missing),
           verdict_counts=dict(sorted(agree.items())), moved=dict(moved),
           moved_examples={k: list(v) for k, v in ex.items()},
           lean_accept_nearcore_reject_after=sum(v for k, v in agree.items()
                                                 if k.startswith("after: DISAGREE (lean accept")))
print(json.dumps(out, indent=1))
