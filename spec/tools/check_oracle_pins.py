#!/usr/bin/env python3
"""Guard: the D0 oracle source pinned by the signed challenge must not drift.

The live challenge `near-chunk-validation-d0` (challenges/chl_640ed008….json) pins each
workload class's generator spec by digest (`workload_suite.classes[].generator =
sha256(JCS(spec/workloads/near-chunk-validation-d0/<class>.json))`, spec/tools/
build_challenge_draft_v3.py), and every generator spec pins
`oracle_source_tree_digest = TreeDigest(oracle/v3/src oracle/v3/Cargo.toml oracle/v3/Cargo.lock)`.
This check fails if
  * a generator spec no longer hashes to the digest the signed challenge carries, or
  * the tracked oracle/v3 source no longer has the pinned TreeDigest.
New oracle features belong in their own crates (e.g. oracle/v3-d1), never in oracle/v3.

usage: check_oracle_pins.py          (exit 0 = pins hold)
"""
import glob, hashlib, json, os, subprocess, sys

ROOT = subprocess.run(["git", "rev-parse", "--show-toplevel"], capture_output=True, text=True,
                      check=True).stdout.strip()
SIGNED = {
    # signed challenge -> directory of its generator specs
    "challenges/chl_640ed008467448706236fc727f759ecc.json": "spec/workloads/near-chunk-validation-d0",
}
ORACLE_TREE = ["oracle/v3/src", "oracle/v3/Cargo.toml", "oracle/v3/Cargo.lock"]


def jcs(v):
    return json.dumps(v, separators=(",", ":"), sort_keys=True, ensure_ascii=False)


def tree(*paths):
    return subprocess.run([sys.executable, os.path.join(ROOT, "spec/tools/tree_digest.py"), *paths],
                          capture_output=True, text=True, check=True, cwd=ROOT).stdout.strip()


def main():
    bad = []
    actual = tree(*ORACLE_TREE)
    for chl, wdir in SIGNED.items():
        c = json.load(open(os.path.join(ROOT, chl)))
        gens = {cl["id"]: cl.get("generator") for cl in c["workload_suite"]["classes"]}
        specs = {}
        for f in sorted(glob.glob(os.path.join(ROOT, wdir, "*.json"))):
            spec = json.load(open(f))
            specs["sha256:" + hashlib.sha256(jcs(spec).encode()).hexdigest()] = (f, spec)
        for cid, g in gens.items():
            if g is None:
                continue
            if g not in specs:
                bad.append(f"{chl}: class {cid}: no generator spec in {wdir} hashes to {g}")
                continue
            f, spec = specs[g]
            pin = spec.get("oracle_source_tree_digest")
            if pin is None:
                continue
            if pin != actual:
                bad.append(f"{os.path.relpath(f, ROOT)} pins oracle_source_tree_digest {pin}, "
                           f"but TreeDigest({' '.join(ORACLE_TREE)}) = {actual}")
            else:
                print(f"ok  {chl} class {cid}: oracle/v3 source = {pin}")
    for b in bad:
        print("PIN DRIFT: " + b, file=sys.stderr)
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
