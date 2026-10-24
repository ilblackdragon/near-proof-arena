#!/usr/bin/env python3
"""Independent module generation and full-output comparison for W03 loading limits.

Oracle runtime-full uses pinned runtime's LoadingError -> zero-gas VMOutcome conversion.
The modules vary imports, table metadata, escaped functions, globals, start and aliases.
"""
import argparse
import collections
import hashlib
import json
from pathlib import Path
import random
import subprocess
import tempfile

from replay_successor import REPO, sha256


def leb(n):
    out = bytearray()
    while n >= 128:
        out.append((n & 127) | 128)
        n >>= 7
    return bytes(out + bytes([n]))


def vec(xs):
    return leb(len(xs)) + b"".join(xs)


def string(s):
    b = s.encode()
    return leb(len(b)) + b


def section(tag, b):
    return bytes([tag]) + leb(len(b)) + b


def module(globals_count, imports=0, tables=0, functions=1, aliases=0, start=False, elements=False, method="main", import_name="prepaid_gas"):
    # Types: () -> (), () -> i64 (prepaid_gas imports).
    sections = [section(1, vec([b"\x60\0\0", b"\x60\0\x01\x7e"]))]
    if imports:
        sections.append(section(2, vec([string("env") + string(import_name) + b"\0\x01"] * imports)))
    sections.append(section(3, vec([b"\0"] * functions)))
    if tables:
        sections.append(section(4, vec([b"\x70\0" + leb(functions)])))
    sections.append(section(5, vec([b"\0\x01"])))
    sections.append(section(6, vec([b"\x7f\x01\x41\0\x0b"] * globals_count)))
    exports = [string("memory") + b"\x02\0", string(method) + b"\0" + leb(imports)]
    # Extra defined functions escape via elements OR exports; alias exports do not create new refs.
    if not elements:
        exports += [string(f"f{i}") + b"\0" + leb(imports + i) for i in range(1, functions)]
    exports += [string(f"alias{i}") + b"\0" + leb(imports) for i in range(aliases)]
    sections.append(section(7, vec(exports)))
    if start:
        sections.append(section(8, leb(imports)))
    if elements:
        # Declarative segment: all functions declared, independent of table initialization.
        sections.append(section(9, vec([b"\x03\0" + vec([leb(imports + i) for i in range(functions)])])))
    sections.append(section(10, vec([b"\x02\0\x0b"] * functions)))
    return b"\0asm\x01\0\0\0" + b"".join(sections)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--harness", type=Path, default=Path("/data/illia/nearproof-deps/target-wasm-d3/release/near-wasm-d3-harness"))
    ap.add_argument("--lean", type=Path, default=REPO / "spec/lean/v3/.lake/build/bin/nearspec-v3-runtime")
    ap.add_argument("--generated-per-seed", type=int, default=0)
    ap.add_argument("--out", type=Path, required=True)
    a = ap.parse_args()
    if a.generated_per_seed < 0:
        ap.error("generated count must be nonnegative")
    a.out.mkdir(parents=True, exist_ok=True)
    directed = [
        dict(globals_count=n, imports=i, tables=t, functions=f, aliases=2,
             start=True, elements=e)
        for n in (1000, 65500, 65505, 65506, 66000)
        for i, t, f, e in ((0,0,1,False), (1,0,1,False), (0,1,1,False),
                           (0,0,4,False), (0,0,4,True), (7,1,3,True))
    ]
    cases = [(None, c) for c in directed]
    for seed in (17, 29, 43, 71):
        rng = random.Random(seed)
        for _ in range(a.generated_per_seed):
            cases.append((seed, dict(globals_count=rng.randrange(65420,65520),
                                    imports=rng.randrange(8), tables=rng.randrange(2),
                                    functions=rng.randrange(1,8), aliases=rng.randrange(4),
                                    start=bool(rng.randrange(2)), elements=bool(rng.randrange(2)))))
    rows = []
    binaries = {k: {"path": str(p), "sha256": sha256(p)}
                for k,p in (("nearcore",a.harness),("lean",a.lean))}
    with tempfile.TemporaryDirectory(prefix="runtime-limits-") as tmp:
        path = Path(tmp) / "module.wasm"
        for index,(seed,params) in enumerate(cases):
            code = module(**params)
            path.write_bytes(code)
            oracle = subprocess.run([str(a.harness), "runtime-full"],
                                    input=f"300000000000000 {code.hex()}\n",
                                    text=True,capture_output=True,check=True,timeout=60).stdout.strip()
            lean = subprocess.run([str(a.lean),str(path)],text=True,capture_output=True,
                                  check=True,timeout=60).stdout.strip()
            row = dict(index=index, seed=seed, parameters=params,
                       input_sha256=hashlib.sha256(code).hexdigest(),
                       nearcore=oracle, lean=lean, same=oracle==lean)
            rows.append(row)
            if oracle != lean:
                (a.out / "failure.wasm").write_bytes(code)
                print(json.dumps(row), flush=True)
                break
            if index % 25 == 0:
                print(f"{index+1}/{len(cases)} compared", flush=True)
    (a.out/"results.jsonl").write_text("".join(json.dumps(r,sort_keys=True)+"\n" for r in rows))
    report = dict(schema="near-runtime-limits-v1", binaries=binaries, requested=len(cases),
                  compared=len(rows), matches=sum(r["same"] for r in rows),
                  generated_per_seed=a.generated_per_seed,
                  loading_failures=sum("LoadingError" in r["nearcore"] for r in rows),
                  successes=sum(r["nearcore"].startswith("ok ") for r in rows),
                  results_sha256=sha256(a.out/"results.jsonl"))
    report["per_seed"] = {str(seed): sum(r["seed"] == seed for r in rows)
                          for seed in (17,29,43,71)}
    # Deliberately remove the new check: the previously diverging module must disagree.
    with tempfile.TemporaryDirectory(prefix="runtime-ablation-") as tmp:
        path = Path(tmp) / "oversized.wasm"
        path.write_bytes(module(66000))
        ablated = subprocess.run([str(a.lean), str(path), "main", "--ablate-loading-limits"],
                                 text=True,capture_output=True,check=True,timeout=60).stdout.strip()
        report["ablation_detected"] = ablated.startswith("ok ")
    report["pass"] = (report["matches"] == report["requested"]
                      and report["loading_failures"] > 0 and report["successes"] > 0
                      and report["ablation_detected"])
    (a.out/"report.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(report,indent=2))
    return int(not report["pass"])


if __name__ == "__main__":
    raise SystemExit(main())
