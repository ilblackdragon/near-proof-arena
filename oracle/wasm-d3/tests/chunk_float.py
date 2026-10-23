#!/usr/bin/env python3
"""L2 whole-chunk float tests: honest float chunks through the checker, plus tamper cases.

The operator-level difftests (`difftest_float.py`, `float_nearcore.py`) anchor `evalFloatOp` to
pinned nearcore. This script covers the other half of the L2 obligation (§5 item 4): that lifting
the four float guards lets *whole chunks* through, that a remaining exclusion is never a float one,
and that a tampered claim/witness is still rejected.

Source of honest cases: the recorded corpus, under `CORPUS/<chain>/<family>/<case>/`, where the
metadata names the `d3float` contract, records nearcore's verdict as `ok`, and tags `e.float` — a
chunk that *executed a float contract* and that nearcore accepted.

Assertions on an honest case:

  1. `checkD3` (`nearspec-v3-check-d3`) is `out_of_domain` with a **float** reason (the exclusion
     really is the float guard, not some other condition);
  2. `checkD3F` (`nearspec-v3-check-d3f`) is not excluded for a float reason — the guard is gone;
     if it is `accept`, the case counts as *lifted*; a remaining exclusion must have a different
     reason (another lane's row: `gAlpha` gas, ETH-implicit local contract, ...);
  3. the recorded nearcore verdict is `ok`, so `accept` is the right answer, not a looser checker.

Tamper cases (each must be `reject`, i.e. necessary conditions, not decorative ones):

  `-claim`     one byte inside the claim's `chunk_inner` flipped → the witness's chunk header no
               longer matches the claim;
  `-witness`   one byte inside the witness's chunk header flipped → same condition, other side;
  `-code`      one byte inside the *appended contract-code blob list* flipped → the executed
               contract's code no longer hashes to the deployed hash.

  chunk_float.py [--corpus DIR] [--sample N] [--tamper-dir DIR]

Exit 1 on any failure.
"""
import argparse
import glob
import json
import os
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN_DIR = os.path.join(HERE, "../lean")
D3 = os.path.join(LEAN_DIR, ".lake/build/bin/nearspec-v3-check-d3")
D3F = os.path.join(LEAN_DIR, ".lake/build/bin/nearspec-v3-check-d3f")
DEFAULT_CORPUS = "/data/illia/nearproof-deps/corpora/d3c9"

FLOAT_MARKERS = ("float type or operator", "float in an imported function type", "float global",
                 "float (out of domain)")


def is_float_reason(reason):
    return any(m in reason for m in FLOAT_MARKERS)


def verdicts(exe, dirs):
    p = subprocess.run([exe, *dirs], capture_output=True, text=True)
    if p.returncode != 0:
        raise SystemExit(f"{exe} exited {p.returncode}: {p.stderr[:400]}")
    out = {}
    for line in p.stdout.splitlines():
        if line.startswith("{"):
            j = json.loads(line)
            out[os.path.normpath(j["case"])] = j
    return out


def candidates(corpus):
    """Corpus cases that name `d3float`, are recorded nearcore accepts, and are tagged `e.float`."""
    for meta in sorted(glob.glob(os.path.join(corpus, "*", "*", "meta.json"))):
        try:
            m = json.load(open(meta))
        except Exception:  # noqa: BLE001
            continue
        names = {c.get("name") for c in m.get("codes", []) if isinstance(c, dict)}
        v = set()
        for k in ("d0_violations", "d1_violations", "d2_violations", "d3_violations"):
            v |= set(m.get(k, []))
        if "d3float" in names and m.get("nearcore") == "ok" and "e.float" in v:
            yield os.path.dirname(meta), m


# Byte offsets verified against the recorded d3float cases: a flip there produces a *semantic*
# rejection (a mismatched chunk header / a missing code blob), never a decode error, which is what
# makes the mutant discriminating rather than trivially invalid.
OFFSETS = {"claim": 100, "witness": 100, "code": -9}


def tamper(src, dst, kind):
    os.makedirs(dst, exist_ok=True)
    claim = bytearray(open(os.path.join(src, "claim.bin"), "rb").read())
    wit = bytearray(open(os.path.join(src, "witness.bin"), "rb").read())
    buf, off = (claim, OFFSETS["claim"]) if kind == "claim" else \
               (wit, OFFSETS["witness"]) if kind == "witness" else (wit, OFFSETS["code"])
    if len(buf) + off < 0 or off >= len(buf):
        return None
    buf[off] ^= 0x01
    open(os.path.join(dst, "claim.bin"), "wb").write(bytes(claim))
    open(os.path.join(dst, "witness.bin"), "wb").write(bytes(wit))
    shutil.copy(os.path.join(src, "meta.json"), os.path.join(dst, "meta.json"))
    return dst


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--corpus", default=DEFAULT_CORPUS)
    ap.add_argument("--sample", type=int, default=0, help="0 = every candidate")
    ap.add_argument("--tamper-dir", default="/tmp/opencode/chunk-float")
    ap.add_argument("--no-tamper", action="store_true")
    a = ap.parse_args()
    for exe in (D3, D3F):
        if not os.path.exists(exe):
            raise SystemExit(f"missing checker {exe}; build oracle/wasm-d3/lean first")
    cases = list(candidates(a.corpus))
    if a.sample:
        cases = cases[:a.sample]
    if not cases:
        raise SystemExit(f"no d3float + e.float + nearcore-ok cases under {a.corpus}")
    dirs = [c for c, _ in cases]
    d3 = verdicts(D3, dirs)
    d3f = verdicts(D3F, dirs)
    bad = 0
    lifted = 0
    still = []
    other = []
    for case_dir, m in cases:
        k = os.path.normpath(case_dir)
        name = os.path.basename(os.path.dirname(case_dir)) + "/" + os.path.basename(case_dir)
        v3, vf = d3[k], d3f[k]
        if m.get("nearcore") != "ok":
            print(f"FAIL {name}: nearcore={m.get('nearcore')!r}, not an accept")
            bad += 1
        # Preparation reports the *first* exclusion it meets, so a case tagged `e.float` can be
        # rejected earlier for an unrelated reason (`w.shape`, `e.g_alpha`, `e.eth_implicit_local`).
        # Such a case is not evidence about floats either way and is counted separately; only a
        # case that D3α actually excludes *for a float* must be lifted.
        float_blocked = (v3["verdict"] == "out_of_domain" and is_float_reason(v3["reason"]))
        if not float_blocked:
            if v3["verdict"] == "accept":
                print(f"FAIL {name}: D3α accepts a e.float case — the corpus and the checker "
                      f"disagree about the guard")
                bad += 1
            else:
                other.append((name, v3["reason"]))
            continue
        if vf["verdict"] == "accept":
            lifted += 1
        elif is_float_reason(vf["reason"]):
            print(f"FAIL {name}: float reason survives floatPv86: {vf['reason']!r}")
            bad += 1
        else:
            still.append((name, vf["reason"]))
    print(f"family=float-chunk candidates={len(cases)} float_blocked_and_lifted={lifted} "
          f"blocked_earlier_by_other_lane={len(other)} still_excluded_other_reason={len(still)} "
          f"failures={bad}")
    for name, why in other:
        print(f"  earlier exclusion (not float): {name}: {why}")
    for name, why in still:
        print(f"  other lane after lift: {name}: {why}")

    if a.no_tamper:
        sys.exit(1 if bad else 0)
    shutil.rmtree(a.tamper_dir, ignore_errors=True)
    os.makedirs(a.tamper_dir, exist_ok=True)
    muts = []
    for kind in ("claim", "witness", "code"):
        for case_dir, m in cases:
            # a case excluded for a second reason would report that reason, not the tamper
            if d3f[os.path.normpath(case_dir)]["verdict"] != "accept":
                continue
            d = tamper(case_dir, os.path.join(a.tamper_dir,
                                              f"{os.path.basename(case_dir)}-{kind}"), kind)
            if d:
                muts.append((kind, d))
    if muts:
        res = verdicts(D3F, [d for _, d in muts])
        mb = 0
        per = {}
        for kind, d in muts:
            v = res[os.path.normpath(d)]["verdict"]
            per[f"{kind}:{v}"] = per.get(f"{kind}:{v}", 0) + 1
            if v != "reject":
                mb += 1
                if mb <= 15:
                    print(f"TAMPER NOT REJECTED {kind} {d}: {v} {res[os.path.normpath(d)].get('reason')}")
        print(f"family=float-chunk-tamper mutants={len(muts)} failures={mb} {dict(sorted(per.items()))}")
        bad += mb
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
