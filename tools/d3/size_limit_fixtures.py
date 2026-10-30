#!/usr/bin/env python3
"""W02 size-limit fixtures at the 48 MiB `MAX_COMPRESSED_STATE_WITNESS_SIZE` boundary.

For each whole-chunk case (an in-the-clear `witness.bin` judged by the cold nearcore validator, its
verdict in `meta.json["nearcore"]`), `ncref witness` (nearcore 2.13.4's own `near-primitives`, built
without `test_features`, docs/evidence/lean-chunk-completion/size-limit-fixtures/ncref) encodes the
`ChunkStateWitness` with the producer codec (`EncodedChunkStateWitness::encode`) and reports, for the
encoding padded with one zstd skippable frame to exactly 48 MiB − 1, 48 MiB and 48 MiB + 1 bytes:

* the partial-witness size check `encoded_length > MAX_COMPRESSED_STATE_WITNESS_SIZE`
  (`chain/client/src/stateless_validation/validate.rs:82-88`, the first check a validator applies), and
* `EncodedChunkStateWitness::decode` of the padded bytes, `identical` when it yields the very
  `ChunkStateWitness` bytes the cold validator judged.

nearcore's verdict of a variant is therefore: reject when the size check fires; otherwise, when the
decode is identical, the case's cold verdict (validation is a function of the decoded witness); any
other decode result is recorded and the variant is not graded. This script writes each variant as
a `near-arena-cwitness-v3` case (the padded bytes regenerated here and checked against ncref's
sha256), runs the Lean checker on it, compares, and deletes the large file.

  python3 tools/d3/size_limit_fixtures.py --ncref NCREF --checker CHECKER --cases-file LIST \
      --variants plain,under48,at48,over48 --work DIR --out OUT.json [--jobs N]
"""
import argparse
import hashlib
import json
import shutil
import struct
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

OLD_TAG = b"near-arena-witness-v3"
NEW_TAG = b"near-arena-cwitness-v3"
SKIP_MAGIC = 0x184D2A50
CAP = 48 * 1024 * 1024
TARGETS = {"under48": CAP - 1, "at48": CAP, "over48": CAP + 1}


def codes_region(raw):
    (tl,) = struct.unpack_from("<I", raw, 0)
    assert raw[4:4 + tl] == OLD_TAG
    off = 4 + tl
    (sl,) = struct.unpack_from("<I", raw, off)
    return raw[off + 4 + sl:]


def pad(enc, target):
    body = target - len(enc) - 8
    assert body >= 0
    return enc + struct.pack("<II", SKIP_MAGIC, body) + bytes(body)


def lean(checker, case_dir, tier):
    t0 = time.time()
    r = subprocess.run(["/usr/bin/time", "-f", "MAXRSS %M CPU %U %S", checker, "--tier", tier, str(case_dir)],
                       capture_output=True, text=True, timeout=7200)
    wall = time.time() - t0
    rss = cpu = None
    for line in r.stderr.splitlines():
        if line.startswith("MAXRSS "):
            f = line.split()
            rss, cpu = int(f[1]) * 1024, round(float(f[3]) + float(f[4]), 2)
    if r.returncode != 0 or not r.stdout.strip():
        return {"verdict": "error", "reason": r.stderr[-400:], "wall_s": wall, "cpu_s": cpu, "max_rss": rss}
    row = json.loads(r.stdout.strip().splitlines()[-1])
    return {"verdict": row["verdict"], "reason": row["reason"], "wall_s": round(wall, 2), "cpu_s": cpu,
            "max_rss": rss}


def one(a, case):
    case = Path(case)
    meta = json.loads((case / "meta.json").read_text())
    nc = meta["nearcore"]
    work = Path(a.work) / case.parent.parent.name / case.parent.name / case.name
    work.mkdir(parents=True, exist_ok=True)
    rep = subprocess.run([a.ncref, "witness", str(case / "witness.bin"), str(work)],
                         capture_output=True, text=True, check=True)
    info = json.loads(rep.stdout)
    rows = []
    if "undecodable" in info:
        shutil.rmtree(work, ignore_errors=True)
        return [{"case": str(case), "variant": v, "skipped": "witness bytes are not a ChunkStateWitness"}
                for v in a.variants]
    enc = (work / "enc.zst").read_bytes()
    raw = (case / "witness.bin").read_bytes()
    codes = codes_region(raw)
    for v in a.variants:
        if v == "plain":
            data, dec, cap_rejects = enc, info["plain"]["decode"], False
        else:
            vi = info["variants"].get(v)
            if vi is None:
                rows.append({"case": str(case), "variant": v, "skipped": "encoding too large to pad"})
                continue
            data = pad(enc, TARGETS[v])
            if hashlib.sha256(data).hexdigest() != vi["sha256"]:
                raise SystemExit(f"{case} {v}: padded bytes differ from ncref's")
            dec, cap_rejects = vi["decode"], vi["cap_rejects"]
        if cap_rejects:
            expected = "reject"
            nc_reason = "InvalidPartialChunkStateWitness: encoded_length exceeds witness size cap"
        elif dec == "identical":
            expected = "accept" if nc == "ok" else "reject"
            nc_reason = nc
        else:
            rows.append({"case": str(case), "variant": v, "skipped": f"decode {dec}"})
            continue
        vdir = work / v
        vdir.mkdir(exist_ok=True)
        wb = struct.pack("<I", len(NEW_TAG)) + NEW_TAG + struct.pack("<I", len(data)) + data + codes
        (vdir / "witness.bin").write_bytes(wb)
        shutil.copy(case / "claim.bin", vdir / "claim.bin")
        del wb, data
        res = lean(a.checker, vdir, a.tier)
        shutil.rmtree(vdir, ignore_errors=True)
        lv = res["verdict"]
        if lv == "accept" and expected == "reject":
            cls = "UNSOUND_lean_accepts_nearcore_reject"
        elif lv == "out_of_domain":
            cls = "out_of_domain"
        elif lv == "error":
            cls = "error"
        elif lv == expected:
            cls = "agree"
        else:
            cls = "lean_rejects_nearcore_accept"
        rows.append({"case": str(case), "variant": v, "encoded_len": len(enc) if v == "plain" else TARGETS[v],
                     "sw_len": info["sw_len"], "nearcore": expected, "nearcore_reason": nc_reason[:300],
                     "lean": lv, "lean_reason": res["reason"][:300], "class": cls,
                     "wall_s": res["wall_s"], "cpu_s": res["cpu_s"], "max_rss": res["max_rss"]})
    shutil.rmtree(work, ignore_errors=True)
    return rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--ncref", required=True)
    ap.add_argument("--checker", required=True)
    ap.add_argument("--tier", default="allFeatures")
    ap.add_argument("--cases-file", required=True)
    ap.add_argument("--variants", default="plain,under48,at48,over48")
    ap.add_argument("--work", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--jobs", type=int, default=1)
    a = ap.parse_args()
    a.variants = a.variants.split(",")
    cases = [l for l in Path(a.cases_file).read_text().splitlines() if l.strip()]
    rows = []
    with ThreadPoolExecutor(a.jobs) as ex:
        for rs in ex.map(lambda c: one(a, c), cases):
            rows.extend(rs)
            for r in rs:
                print(json.dumps(r), flush=True)
    summ = {}
    for r in rows:
        k = (r["variant"], r.get("class", "skipped"))
        summ[f"{k[0]}:{k[1]}"] = summ.get(f"{k[0]}:{k[1]}", 0) + 1
    out = {"cases": len(cases), "variants": a.variants, "checker": a.checker,
           "checker_sha256": hashlib.sha256(Path(a.checker).read_bytes()).hexdigest(),
           "summary": summ, "rows": rows}
    Path(a.out).write_text(json.dumps(out, indent=1))
    print(json.dumps(summ, indent=1))
    if any(r.get("class", "").startswith("UNSOUND") for r in rows):
        sys.exit(1)


if __name__ == "__main__":
    main()
