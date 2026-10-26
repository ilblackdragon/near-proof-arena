#!/usr/bin/env python3
"""Copy the honest cases a scenario manifest maps (collect_successor_scenarios.py) and a small,
deterministic, family-diverse sample of their nearcore-judged mutants into a fixture directory.

Case bytes and metadata are copied unchanged; `index.json` records each case's origin, sha256 of
every file, the recorded nearcore verdict and the scenario steps that map to it.
"""
import argparse
import collections
import hashlib
import json
from pathlib import Path
import shutil


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def referenced(manifest):
    """case dir -> [step labels] for every honest case a manifest maps."""
    refs = collections.defaultdict(list)
    def add(case, why):
        if case:
            refs[case].append(why)
    for st in manifest.get("steps", []):
        c = st["cases"]
        for x in c["included"]:
            add(x, st["label"] + ":included")
        add(c["fc"], st["label"] + ":executed")
        for x in c["callbacks"]:
            add(x, st["label"] + ":callback")
        for x in c["notes"]:
            add(x, st["label"] + ":cross-shard-note")
        add(c.get("timeout"), st["label"] + ":timeout-loop")
    for lane in manifest.get("lanes", []):
        for p in lane["probes"]:
            if "search" in p["label"]:
                continue
            add(p["case"], f"{lane['kind']}.{p['label']}:probe")
            for x in p["deferred_case"]:
                add(x, f"{lane['kind']}.{p['label']}:deferred-incoming")
            if p.get("anchor"):
                add(p["anchor"]["callback_case"], f"{lane['kind']}.{p['label']}:timeout-callback")
    for m in manifest.get("misc", []):
        for x in m["cases"]:
            add(x, m["label"])
    return refs


def family(mutation):
    return ".".join(mutation.split(".")[:2]).split("(")[0]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--manifest", type=Path, action="append", required=True)
    ap.add_argument("--out", type=Path, required=True, help="fixture cases directory (created)")
    ap.add_argument("--mutants-per-case", type=int, default=4)
    ap.add_argument("--prefix", action="append", default=[], help="case name prefix per manifest")
    a = ap.parse_args()
    a.out.mkdir(parents=True, exist_ok=False)
    index = []
    for i, mpath in enumerate(a.manifest):
        manifest = json.loads(mpath.read_text())
        run = Path(manifest["run"])
        prefix = a.prefix[i] if i < len(a.prefix) else run.name
        refs = referenced(manifest)
        mutants = collections.defaultdict(list)
        for d in sorted((run / "mutants").iterdir()) if (run / "mutants").exists() else []:
            meta = json.loads((d / "meta.json").read_text())
            mutants[meta["base"]].append((d, meta))
        for case in sorted(refs):
            src = run / case
            meta = json.loads((src / "meta.json").read_text())
            picks = [(src, meta, "honest")]
            seen = set()
            for d, mm in mutants.get(src.name, []):
                f = family(mm["mutation"])
                if f in seen or len(seen) >= a.mutants_per_case:
                    continue
                seen.add(f)
                picks.append((d, mm, "mutant"))
            for d, mm, kind in picks:
                name = f"{prefix}-{d.name}"
                dst = a.out / name
                shutil.copytree(d, dst)
                index.append(dict(
                    case_dir=name, kind=kind, source=str(d), expected_rel=mm["expected_rel"],
                    nearcore=mm["nearcore"], mutation=mm.get("mutation"),
                    verdict_source=mm.get("verdict_source", "nearcore(cold)"),
                    steps=sorted(set(refs[case])) if kind == "honest" else [],
                    files={f.name: sha(f) for f in sorted(dst.iterdir())}))
    (a.out / "index.json").write_text(json.dumps(index, indent=1) + "\n")
    print(json.dumps(collections.Counter(x["kind"] for x in index)))


if __name__ == "__main__":
    main()
