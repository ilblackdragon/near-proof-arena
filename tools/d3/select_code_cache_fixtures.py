#!/usr/bin/env python3
"""Select a small portable subset of `code-cache` scenario cases (oracle/v3-successor, W08/UQ-001).

Classes (from the generator's own metadata, never from Lean):
  honest; code mutant without a code label (missing code no deploy serves, or extra blobs);
  `e.code_deploy_served` accepted / rejected by cold nearcore; `e.code_prep_race`.
Takes the first N of each class per run (sorted names), copies claim.bin/witness.bin/meta.json and
writes index.json with the source path and sha256 of every file.
"""
import argparse
import hashlib
import json
import shutil
from pathlib import Path


def klass(m):
    v = m.get("d3_violations") or []
    if m["kind"] == "honest":
        return "honest"
    ok = "accept" if m["nearcore"] == "ok" else "reject"
    if "e.code_prep_race" in v:
        return "race"
    if "e.code_deploy_served" in v:
        return "deploy_served_" + ok
    return "unlabelled_mutant_" + ok


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--run", type=Path, action="append", required=True)
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--per-class", type=int, default=2)
    a = ap.parse_args()
    a.out.mkdir(parents=True, exist_ok=True)
    index = []
    for run in a.run:
        taken = {}
        for meta in sorted(run.glob("*/*/meta.json")):
            m = json.loads(meta.read_text())
            k = klass(m)
            if taken.get(k, 0) >= a.per_class:
                continue
            taken[k] = taken.get(k, 0) + 1
            name = f"{run.name}-{meta.parent.name}"
            dest = a.out / name
            dest.mkdir(exist_ok=True)
            files = {}
            for f in ("claim.bin", "witness.bin", "meta.json"):
                shutil.copyfile(meta.parent / f, dest / f)
                files[f] = hashlib.sha256((dest / f).read_bytes()).hexdigest()
            index.append({"case_dir": name, "class": k, "source": f"{run.name}/{meta.parent.parent.name}/{meta.parent.name}",
                          "nearcore": m["nearcore"], "files": files})
    (a.out / "index.json").write_text(json.dumps(index, indent=1) + "\n")
    print(len(index), "cases")


if __name__ == "__main__":
    main()
