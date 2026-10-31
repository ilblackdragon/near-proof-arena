#!/usr/bin/env python3
"""race_rows.py REPORT.json... : harness classification of every race-exclusion row."""
import collections, json, sys
for f in sys.argv[1:]:
    r = json.load(open(f))
    c = collections.Counter(x.get("classification") for x in r.get("comparisons") or r.get("records") or []
                            if "code_prep_race" in (x.get("reason") or ""))
    print(f.split("/")[-2], dict(c))
