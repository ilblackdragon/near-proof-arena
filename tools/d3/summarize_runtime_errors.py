#!/usr/bin/env python3
"""Summarize `runtime-errors` scenario runs (W03, UQ-014) for the evidence directory.

Inputs per run (`--col DIR` holding one `re<seed>` directory per run): the collector's
`manifest.json` / `honest.txt` (tools/d3/collect_xfam.py), the `allFeatures` verdict replay of the
family population (`rep-main/report.json`, tools/d3/replay_successor.py), the blind replay of the
honest cases (`blind/report.json`, tools/mainnet-replay/blind_corpus.py) and the deliberate-breakage
replay of the honest cases (`rep-ablate/report.json`, a checker built without the loading check and
with every import linking).

Every outcome kind comes from nearcore's recorded outcome trees, never from Lean or a label. A
case is attributed to a runtime-error kind when nearcore applied a receipt of that kind in the chunk
the case validates. Output: `summary.json` and, with `--steps`, a per-step Markdown table.
"""
import argparse
import collections
import json
from pathlib import Path
import sys

KINDS = ("LoadingError", "LinkError", "PrepareError(Instantiate)", "PrepareError(Memory)", "HostError(GasExceeded)")


def kind_of(r):
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from collect_xfam import rt_failure_kind
    return rt_failure_kind(r["failure"]) if r.get("status") == "failure" else r.get("status")


def run_summary(d):
    m = json.loads((d / "manifest.json").read_text())
    case_kinds = collections.defaultdict(set)
    for s in m["steps"]:
        for r in s.get("receipts", []):
            if r.get("case"):
                case_kinds[str((Path(m["run"]) / r["case"]).resolve())].add(kind_of(r))
    out = dict(run=Path(m["run"]).name, chain_params=m["chain_params"], population=m["population"],
               receipt_kind_counts=m["facts"]["receipt_kind_counts"], problems=m["problems"])
    rep = json.loads((d / "rep-main" / "report.json").read_text())["comparisons"]
    part = collections.Counter(x["classification"] for x in rep)
    out["verdict_rows"] = len(rep)
    out["verdict_partition"] = dict(part)
    out["verdict_disagreements"] = [x["case"] for x in rep if x["verdict_compared"] and not x["verdict_agrees"]]
    out["verdict_by_nearcore"] = dict(collections.Counter(f"nearcore {'accept' if x['expected_rel'] else 'reject'} / lean {x['verdict']}" for x in rep))
    by_kind = {}
    for k in KINDS:
        cases = {c for c, ks in case_kinds.items() if k in ks}
        rows = [x for x in rep if x["case"] in cases]
        by_kind[k] = dict(honest_cases=len(cases), agree=sum(x["verdict_agrees"] for x in rows))
    blind = json.loads((d / "blind" / "report.json").read_text())
    out["blind"] = dict(pass_=blind["pass"], cases=blind["cases"], graded=blind["graded"], counts=blind["counts"],
                        compared_outputs=blind["compared_outputs"])
    abl = json.loads((d / "rep-ablate" / "report.json").read_text())["comparisons"]
    det = collections.Counter()
    for x in abl:
        ks = case_kinds.get(x["case"], set())
        for k in KINDS:
            if k in ks:
                det[(k, "detected" if not x["verdict_agrees"] else "missed")] += 1
    out["ablation"] = dict(rows=len(abl), detected=sum(not x["verdict_agrees"] for x in abl),
                           per_kind={f"{k}/{v}": n for (k, v), n in sorted(det.items())})
    out["honest_by_kind"] = by_kind
    return out, m


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--col", type=Path, required=True)
    ap.add_argument("--runs", nargs="+", required=True)
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--steps", type=Path, help="write a per-step table (from the first run) here")
    a = ap.parse_args()
    runs, first = [], None
    for r in a.runs:
        s, m = run_summary(a.col / r)
        runs.append(s)
        first = first or m
    tot = dict(verdict_rows=sum(r["verdict_rows"] for r in runs),
               disagreements=sum(len(r["verdict_disagreements"]) for r in runs),
               honest=sum(r["population"]["honest"] for r in runs),
               mutants=sum(r["population"]["mutants"] for r in runs),
               blind_graded=sum(r["blind"]["graded"] for r in runs),
               blind_pass=all(r["blind"]["pass_"] for r in runs),
               ablation_rows=sum(r["ablation"]["rows"] for r in runs),
               ablation_detected=sum(r["ablation"]["detected"] for r in runs))
    a.out.write_text(json.dumps(dict(total=tot, runs=runs), indent=1) + "\n")
    print(json.dumps(tot))
    if a.steps:
        lines = ["| step | signer → receiver | actions | nearcore receipt kinds |", "|---|---|---|---|"]
        for s in first["steps"]:
            ks = collections.Counter(kind_of(r) for r in s.get("receipts", []) if r.get("executed", True) is not False)
            lines.append(f"| `{s['label'].split('.', 2)[2]}` | {s.get('signer')} → {s.get('receiver')} | {s.get('actions', '')} | "
                         + ", ".join(f"{k} ×{n}" for k, n in sorted(ks.items())) + " |")
        a.steps.write_text("\n".join(lines) + "\n")
    return 1 if tot["disagreements"] else 0


if __name__ == "__main__":
    sys.exit(main())
