#!/usr/bin/env python3
"""Render the gate tables and the judge-measured side-by-side table for
docs/e2e-results/sp1-pipeline/ from the raw submission views written by
tests/e2e/sp1-pipeline.sh. Prints Markdown to stdout."""
import json
import os
import sys

res = sys.argv[1] if len(sys.argv) > 1 else "docs/e2e-results/sp1-pipeline"
order = ["sp1-A1", "sp1-A2", "sp1-B", "reexec-B", "sp1-M"]
found = sorted(f[:-len(".submission.json")] for f in os.listdir(res) if f.endswith(".submission.json"))
labels = [l for l in order if l in found] + [l for l in found if l not in order]
views = {l: json.load(open(os.path.join(res, f"{l}.submission.json"))) for l in labels}


def esc(s):
    return s.replace("|", "\\|").replace("\n", " ")


out = []
for l in labels:
    v = views[l]
    out += [f"### {l}: `{v['id']}`", "",
            f"challenge `{v['challenge_id']}` · stage **{v['stage']}** · decision **{v['decision']}** · "
            f"accepted {v['accepted']} · tier `{v['tier']}` · score {v.get('score_milli')} · "
            f"run reason codes {', '.join(v.get('reason_codes') or []) or '—'}", "",
            "| gate | status | reasons | summary |", "|---|---|---|---|"]
    for g in v["gates"]:
        out.append(f"| {g['gate']} | {g['status']} | {', '.join(g['reason_codes'])} | {esc(g['summary'])[:600]} |")
    out.append("")


def ms(ns):
    return "—" if ns in (None, 0) else f"{ns / 1e6:,.0f}" if ns >= 1e8 else f"{ns / 1e6:,.1f}"


def gib(b):
    return "—" if not b else f"{b / 2**30:.2f} GiB" if b >= 2**30 else f"{b / 2**20:.0f} MiB"


pair = [l for l in ("sp1-M", "sp1-B", "reexec-B") if l in views and views[l].get("benchmark")]
if pair:
    out += ["### Judge-measured benchmark (BENCHMARK job, same worker, same procedure)", "",
            "| class | candidate (challenge) | prove median ms (runs) | MAD ms | cold ms | verify median ms | max proof bytes | peak guest mem |",
            "|---|---|---|---|---|---|---|---|"]
    classes = [c["class_id"] for c in views[pair[0]]["benchmark"]["classes"]]
    for cid in classes:
        for l in pair:
            b = views[l]["benchmark"]
            c = next((x for x in b["classes"] if x["class_id"] == cid), None)
            if not c:
                continue
            runs = ", ".join(ms(x) for x in c["runs_ns"])
            out.append(f"| {cid} | {l} (`{views[l]['challenge_id'][:12]}…`) | {ms(c['median_ns'])} ({runs}) | {ms(c['mad_ns'])} | "
                       f"{ms(c['cold_ns'])} | {ms(c['verify_median_ns'])} | {c['proof_bytes_max']:,} | {gib(c['peak_rss_bytes'])} |")
    out.append("")
    for l in pair:
        b = views[l]["benchmark"]
        out.append(f"* {l}: prepare {ms(b.get('prepare_ns'))} ms, public artifacts {b.get('public_artifact_bytes')} bytes, "
                   f"measured_by `{b.get('measured_by')}`, score {b.get('score_milli')}")
    out.append("")
print("\n".join(out))
