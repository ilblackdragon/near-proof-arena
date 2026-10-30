#!/usr/bin/env python3
"""Replay an explicit successor tier, binding evidence to inputs and the built executable.

No zero-case run, missing/duplicate/foreign output, I/O error, crash or timeout passes.
This is verdict validation; unavailable transition observables remain explicitly unvalidated.
"""
import argparse
import collections
from concurrent.futures import ThreadPoolExecutor
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

REPO = Path(__file__).resolve().parents[2]
# Labels the successor generator (oracle/v3-successor, 2026-10-29) gives a code mutant whose pre-state
# call only an earlier in-chunk deploy can serve. They replace the baseline's `e.code_cache`, which
# named the wrong cause (validator cache history) and did not separate races from the rest:
#   `e.code_deploy_served` nearcore serves the call through the deploy under both forced preparation
#                          schedules (src/cachejudge.rs): deterministic, compared on every whole-state
#                          tier;
#   `e.code_prep_race`     the forced eager and lazy schedules give different verdicts: a thread race,
#                          the named exclusion `out of domain (e.code_prep_race)` of every tier.
CODE = ("e.code_cache", "e.code_deploy_served")
TIERS = {
    # The code labels are widened on every whole-state tier: an in-chunk deploy serves a pre-state
    # call through the deploy tracker or the deploy's precompile (`Successor/CodeResolution.lean`).
    # Since 2026-10-29 `completeCodeGlobal` resolves these exactly as the cold validator does.
    "globalActions": ("c.not_genesis", "e.float", "e.g_alpha", "e.eth_implicit_local") + CODE,
    "completeCodeGlobal": ("c.not_genesis", "e.float", "e.g_alpha", "e.eth_implicit_local") + CODE,
    # W05 curve hosts: the widest tier. A curve-host case is in domain here, so the tier declares
    # no curve exclusion; it still carries the genesis/float/gas ones the narrower tiers carry.
    "curveHosts": ("c.not_genesis", "e.float", "e.g_alpha", "e.eth_implicit_local") + CODE,
    # The widest tier: curve hosts plus resharding. The resharding guards (`c.same_layout`,
    # `c.no_split_gate`) are lifted, so those labels are no longer exclusion labels here.
    "resharding": ("c.not_genesis", "e.float", "e.g_alpha", "e.eth_implicit_local") + CODE,
    # The genuinely cumulative tier: global actions and curve hosts and resharding together. The
    # named wide tiers are NOT cumulative (`curveHosts`/`resharding` omit `globalActions`), so this
    # is the only tier whose domain contains every other wide tier's decided cases. It is also the
    # Gate-B tier: the arena-only `c.segment`, `w.size` (8 MiB) and `c.layout` (64 shards) bounds
    # and the per-chunk gas bound are lifted (docs/evidence/lean-chunk-completion/gate-b-caps).
    "allFeatures": ("c.not_genesis", "e.float", "e.g_alpha", "e.eth_implicit_local") + CODE +
                   ("c.segment", "w.size", "c.layout"),
    "storageResolution": ("c.not_genesis", "e.float", "e.g_alpha", "e.eth_implicit_local") + CODE,
    "runtimeLimits": ("c.not_genesis", "e.float", "e.g_alpha"),
    "signed": (),
    "floats": ("e.float",),
    "protoGas": ("e.g_alpha",),
    "floatsProtoGas": ("e.float", "e.g_alpha"),
    "genesis": ("c.not_genesis",),
    "genesisFloatsProtoGas": ("c.not_genesis", "e.float", "e.g_alpha"),
}


def sha256(path):
    with open(path, "rb") as f:
        return hashlib.file_digest(f, "sha256").hexdigest()


def parse_rows(stdout, cases, tier=None):
    expected = {str(Path(c).resolve()) for c in cases}
    if not expected or len(expected) != len(cases):
        raise ValueError("empty or duplicate input population")
    rows = {}
    for line in stdout.splitlines():
        row = json.loads(line)
        if not isinstance(row, dict) or not isinstance(row.get("case"), str):
            raise ValueError("invalid result object")
        case = str(Path(row["case"]).resolve())
        if case not in expected or case in rows:
            raise ValueError(f"foreign or duplicate result: {case}")
        if row.get("verdict") not in ("accept", "reject", "out_of_domain"):
            raise ValueError(f"invalid verdict: {row.get('verdict')}")
        if not isinstance(row.get("reason"), str):
            raise ValueError("missing reason")
        if tier is not None and row.get("tier") != tier:
            raise ValueError("wrong/missing tier")
        rows[case] = {**row, "case": case}
    if set(rows) != expected:
        raise ValueError(f"missing {len(expected - set(rows))} results")
    return rows


def run_batch(command, cases, timeout, tier=None):
    result = subprocess.run([*command, *map(str, cases)], capture_output=True,
                            text=True, timeout=timeout, check=True)
    return parse_rows(result.stdout, cases, tier)


def load_compare():
    spec = importlib.util.spec_from_file_location(
        "successor_compare", REPO / "oracle/v3-d3/tools/difftest_d3.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def licenses(compare):
    """The pinned harness's exclusion licences plus the successor generator's code labels. The
    signed tier's cold-cache exclusion (`code_cache`) is licensed by either new label; the race
    exclusion `e.code_prep_race` only by the race label."""
    table = dict(compare.EXCLUSION_LICENSES)
    table["code_cache"] = table["code_cache"] | {"e.code_deploy_served", "e.code_prep_race"}
    table["e.code_prep_race"] = frozenset({"e.code_prep_race"})
    return table


def _replay(binary, tier, cases, out, batch=100, timeout=600, jobs=1):
    if tier not in TIERS or batch <= 0 or timeout <= 0 or jobs <= 0:
        raise ValueError("invalid tier, batch size or timeout")
    cases = [Path(c).resolve() for c in cases]
    if not cases or len(set(cases)) != len(cases):
        raise ValueError("empty or duplicate input population")
    binary = Path(binary).resolve()
    package = {"binary": str(binary), "sha256": sha256(binary), "tier": tier}
    # Hash exact input bytes before execution; check again before publishing a pass.
    inputs = [{"case": str(c), "files": {n: sha256(c / n)
               for n in ("claim.bin", "witness.bin", "meta.json")}} for c in cases]
    metas = {str(c): json.loads((c / "meta.json").read_text()) for c in cases}
    for m in metas.values():
        if type(m.get("expected_rel")) is not bool:
            raise ValueError("missing boolean nearcore expectation")
    out = Path(out)
    out.mkdir(parents=True, exist_ok=True)
    report = {"schema": "near-successor-replay-v1", "status": "running",
              "package": package, "inputs": inputs, "cases": len(cases),
              "comparison": "verdict-and-domain-only", "workers": jobs,
              "harness_sources": {str(p.relative_to(REPO)): sha256(p) for p in (
                  Path(__file__).resolve(), REPO / "oracle/v3-d3/tools/difftest_d3.py")}}
    report_path = out / "report.json"
    def save():
        report_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    save()
    try:
        got = {}
        batches = [cases[start:start + batch] for start in range(0, len(cases), batch)]
        def execute(part):
            return run_batch([str(binary), "--tier", tier], part, timeout, tier)
        with ThreadPoolExecutor(max_workers=jobs) as executor:
            for result in executor.map(execute, batches):
                got.update(result)
        if sha256(binary) != package["sha256"] or any(
            sha256(Path(row["case"]) / n) != digest
            for row in inputs for n, digest in row["files"].items()
        ):
            raise ValueError("executable or input changed during replay")
        compare = load_compare()
        _, bad, partition, records = compare.compare(
            tier, list(metas), metas, got,
            domain="baseline" if tier == "signed" else "successor", widen=TIERS[tier],
            licenses=licenses(compare))
        if sum(partition.values()) != len(cases):
            raise ValueError("comparison does not account for every input")
        result_path = out / "results.jsonl"
        result_path.write_text("".join(json.dumps(got[str(c)], sort_keys=True) + "\n" for c in cases))
        report.update(status="fail" if bad else "pass", disagreements=bad,
                      partition=dict(partition), output_sha256=sha256(result_path),
                      verdicts=dict(collections.Counter(r["verdict"] for r in got.values())),
                      checked=compare.OBSERVABLES_CHECKED,
                      unavailable=compare.OBSERVABLES_UNAVAILABLE, comparisons=records)
        save()
        return report
    except Exception as e:
        report.update(status="fail", failure=type(e).__name__, detail=str(e))
        save()
        raise


def replay(binary, tier, cases, out, batch=100, timeout=600, jobs=1):
    # Invalidate any older pass before even input/executable validation. A failed rerun must
    # not leave an apparently current successful report behind.
    out = Path(out)
    out.mkdir(parents=True, exist_ok=True)
    report_path = out / "report.json"
    report_path.write_text(json.dumps({"schema": "near-successor-replay-v1",
                                      "status": "running"}) + "\n")
    try:
        return _replay(binary, tier, cases, out, batch, timeout, jobs)
    except Exception as e:
        report = json.loads(report_path.read_text())
        report.update(status="fail", failure=type(e).__name__, detail=str(e))
        report_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
        raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, default=REPO / "spec/lean/v3/.lake/build/bin/nearspec-v3-check-successor")
    parser.add_argument("--tier", required=True, choices=TIERS)
    parser.add_argument("--cases-file", required=True, type=Path, help="one case directory per line")
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--batch", type=int, default=100)
    parser.add_argument("--timeout", type=float, default=600)
    parser.add_argument("--jobs", type=int, default=1, help="bounded independent checker processes")
    args = parser.parse_args()
    try:
        cases = [line for line in args.cases_file.read_text().splitlines() if line]
        report = replay(args.binary, args.tier, cases, args.out, args.batch, args.timeout, args.jobs)
        print(json.dumps({k: report[k] for k in ("status", "cases", "verdicts", "partition")}))
        return int(report["status"] != "pass")
    except (OSError, ValueError, subprocess.SubprocessError) as e:
        print(f"FAIL: {e}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
