#!/usr/bin/env python3
"""Summarize cross-family fixture replays (`collect_xfam.py` + `replay_successor.py` +
`blind_corpus.py` outputs, one directory per run) into the committed verdict/blind summaries.

For each run directory `COL/<run>` it reads `manifest.json`, `honest.txt`, `mutants.txt`,
`rep-<tier>/report.json` + `results.jsonl` and `blind/report.json` + `results.jsonl`, and reports
per tier: the comparison partition split by honest/mutant and by mutation family, every
disagreement, and the blind categories. `--out` gets `summary.json` (all runs and per-scenario
totals) and, with `--rows`, gzipped per-case rows.
"""
import argparse
import collections
import gzip
import json
from pathlib import Path


def family(mutation):
    return ".".join(mutation.split(".")[:2]).split("(")[0]


def strip(path, prefix):
    return "runs/" + path[len(prefix):] if prefix and path.startswith(prefix) else path


def run_summary(col):
    m = json.loads((col / "manifest.json").read_text())
    honest = set(l for l in (col / "honest.txt").read_text().splitlines() if l)
    out = dict(run=Path(m["run"]).name, scenario=m["scenario"], chain_params=m["chain_params"],
               population=m["population"], facts={k: v for k, v in m["facts"].items() if k != "callbacks"},
               problems=m["problems"], tiers={}, rows={})
    for rep in sorted(col.glob("rep-*/report.json")):
        tier = rep.parent.name[4:]
        r = json.loads(rep.read_text())
        t = dict(status=r["status"], cases=r.get("cases"), verdicts=r.get("verdicts"), partition=r.get("partition"),
                 checker_sha256=r["package"]["sha256"], disagreements=r.get("disagreements", []),
                 mutants_replayed="sampled" if (col / "mutants-sampled.txt").exists() else "all")
        res = [json.loads(l) for l in (rep.parent / "results.jsonl").read_text().splitlines()] if (rep.parent / "results.jsonl").exists() else []
        comps = {c["case"]: c for c in r.get("comparisons", [])}
        split = collections.Counter()
        fams = collections.Counter()
        for row in res:
            c = comps.get(row["case"], {})
            kind = "honest" if row["case"] in honest else "mutant"
            split[(kind, row["verdict"], c.get("classification"))] += 1
            if kind == "mutant":
                meta = json.loads((Path(row["case"]) / "meta.json").read_text())
                fams[(family(meta["mutation"]), row["verdict"], meta["nearcore"] == "ok")] += 1
        t["split"] = {" ".join(map(str, k)): v for k, v in sorted(split.items())}
        t["mutant_families"] = {f"{k[0]} lean={k[1]} nearcore_ok={k[2]}": v for k, v in sorted(fams.items())}
        out["tiers"][tier] = t
        out["rows"][tier] = res
    b = col / "blind" / "report.json"
    if b.exists():
        r = json.loads(b.read_text())
        out["blind"] = {k: r[k] for k in ("cases", "graded", "counts", "pass", "matched_cases_exercising", "field_diffs", "reasons")}
        out["blind"]["checker_sha256"] = r["identities"]["lean_binary_sha256"]
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--col", type=Path, required=True)
    ap.add_argument("--runs", nargs="+", required=True)
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--rows", action="store_true")
    ap.add_argument("--strip", default="", help="case path prefix replaced by `runs/` in the outputs")
    a = ap.parse_args()
    a.out.mkdir(parents=True, exist_ok=True)
    runs = [run_summary(a.col / r) for r in a.runs]
    totals = collections.defaultdict(lambda: collections.Counter())
    for r in runs:
        tot = totals[r["scenario"]]
        tot["runs"] += 1
        tot["honest"] += r["population"]["honest"]
        tot["mutants"] += r["population"]["mutants"]
        for tier, t in r["tiers"].items():
            tot[f"{tier}.cases"] += t["cases"] or 0
            tot[f"{tier}.disagreements"] += len(t["disagreements"])
            for k, v in (t["partition"] or {}).items():
                tot[f"{tier}.{k}"] += v
        for k, v in r.get("blind", {}).get("counts", {}).items():
            tot[f"blind.{k}"] += v
        if a.rows:
            with gzip.open(a.out / f"rows-{r['run']}.jsonl.gz", "wt") as f:
                for tier, rows in r["rows"].items():
                    for row in rows:
                        row = dict(row, case=strip(row["case"], a.strip))
                        f.write(json.dumps(row, sort_keys=True) + "\n")
    for r in runs:
        r.pop("rows")
        for t in r["tiers"].values():
            t["disagreements"] = [[strip(d[0], a.strip)] + list(d[1:]) for d in t["disagreements"]]
    (a.out / "summary.json").write_text(json.dumps(dict(totals={k: dict(v) for k, v in totals.items()}, runs=runs), indent=1) + "\n")
    print(json.dumps({k: dict(v) for k, v in totals.items()}, indent=1))


if __name__ == "__main__":
    main()
