#!/usr/bin/env python3
"""Copy a small, deterministic sample of a collected cross-family run (`collect_xfam.py --out`)
into a fixture directory: the honest cases that apply the most scenario steps (receipts and
inclusions, at most `--honest` of them) and, per picked case, up to `--mutants-per-case` mutants of
distinct mutation families (the scenario's own `g.*` mutants first). Case bytes and metadata are
copied unchanged; `index.json` records origin, kind, nearcore verdict, steps and file hashes.
"""
import argparse
import collections
import hashlib
import json
from pathlib import Path
import shutil


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def family(mutation):
    return ".".join(mutation.split(".")[:2]).split("(")[0]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--collected", type=Path, action="append", required=True)
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--honest", type=int, default=12)
    ap.add_argument("--mutants-per-case", type=int, default=2)
    a = ap.parse_args()
    a.out.mkdir(parents=True, exist_ok=False)
    index = []
    for col in a.collected:
        m = json.loads((col / "manifest.json").read_text())
        run = Path(m["run"])
        refs = collections.defaultdict(set)
        for s in m["steps"]:
            if ".flood." in s["label"]:
                continue
            for c in s.get("included_cases", []):
                refs[c].add(s["label"] + ":included")
            for r in s.get("receipts", []):
                if r.get("case"):
                    refs[r["case"]].add(s["label"] + ":applied")
        if m["scenario"] == "GenesisTx":
            for meta_path in sorted(run.glob("*/*/meta.json")):
                meta = json.loads(meta_path.read_text())
                if meta.get("kind") == "honest" and meta.get("features", {}).get("xfam", {}).get("b2_genesis"):
                    refs[str(meta_path.parent.relative_to(run))].add("genesis-b2")
        mutants = collections.defaultdict(list)
        for d in sorted((run / "mutants").iterdir()):
            mutants[d.name.split("-", 3)[0] + "-" + d.name.split("-", 3)[1] + "-" + d.name.split("-", 3)[2]].append(d)
        # genesis-B2 cases first, then cases with mutants, then by the number of scenario steps
        ranked = sorted(refs, key=lambda c: ("genesis-b2" not in refs[c], not mutants.get(Path(c).name), -len(refs[c]), c))[:a.honest]
        for case in sorted(ranked):
            src = run / case
            picks = [(src, "honest")]
            seen = set()
            ms = sorted(mutants.get(src.name, []), key=lambda d: (not d.name.split("-", 3)[3].startswith("g."), d.name))
            for d in ms:
                mm = json.loads((d / "meta.json").read_text())
                f = family(mm["mutation"])
                if f in seen or len(seen) >= a.mutants_per_case:
                    continue
                seen.add(f)
                picks.append((d, "mutant"))
            for d, kind in picks:
                meta = json.loads((d / "meta.json").read_text())
                name = f"{run.name}-{d.name}"
                shutil.copytree(d, a.out / name)
                index.append(dict(case_dir=name, kind=kind, scenario=m["scenario"], source=f"{run.name}/{d.relative_to(run)}",
                                  nearcore=meta["nearcore"], expected_rel=meta["expected_rel"],
                                  mutation=meta.get("mutation"), verdict_source=meta.get("verdict_source", "nearcore(cold)"),
                                  steps=sorted(refs[case]) if kind == "honest" else [],
                                  files={f.name: sha(f) for f in sorted((a.out / name).iterdir())}))
    (a.out / "index.json").write_text(json.dumps(index, indent=1) + "\n")
    print(json.dumps(collections.Counter((x["scenario"], x["kind"]) for x in index).most_common()))


if __name__ == "__main__":
    main()
