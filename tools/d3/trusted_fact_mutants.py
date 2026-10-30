#!/usr/bin/env python3
"""UQ-013: which trusted claim facts does the relation itself pin down, and which must the
admission contract bind?

claim-v3 §2.4 classifies T1..T14 as *trusted*: answers of the verifier's own epoch manager / store
that no hash in the claim determines. `Rel` checks only their internal consistency. This script
measures that split on real chunks: it takes honest cases (nearcore accept, decided by the tier),
rewrites exactly one trusted value per mutant (everything else byte-identical) and runs the
successor checker. A mutant the checker still **accepts** is a fact only the admission contract can
bind (the proof alone is not evidence of it). A mutant it rejects is pinned by the relation, at
least on that chunk.

Usage: trusted_fact_mutants.py --checker BIN --tier allFeatures --cases LIST --out DIR
"""
import argparse
import collections
import json
import os
import shutil
import struct
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from claim_schema import R, header  # noqa: E402


def field_offsets(data):
    """Byte spans (start, end) of the trusted claim fields of a legacy/versioned v3 claim."""
    kind, v, _, _, off = header(data)
    assert kind == "claim" and v == 3
    r = R(data)
    r.i = off
    spans = {}
    r.bytes_("statement_id")
    spans["T2.protocol_version"] = (r.i, r.i + 4); r.u(4, "pv")
    s = r.i; ln = r.u(4, "chain_id len"); spans["T3.chain_id"] = (s, r.i + ln); r.take(ln, "chain_id")
    spans["T1.epoch_id"] = (r.i, r.i + 32); epoch_id = r.take(32, "epoch_id")
    r.bytes_("chunk_inner")
    n = r.u(4, "n_blocks")
    for _ in range(n):
        r.u(1, "hv"); r.take(32, "ph"); r.bytes_("il"); r.bytes_("ir")
        r.vec("slots", lambda: (r.bytes_("si"), r.u(8, "hi")))
    spans["T4.rs_parts"] = (r.i, r.i + 4); r.u(2, "d"); r.u(2, "t")
    k = r.u(4, "epochs")
    for _ in range(k):
        eid = r.take(32, "eid")
        pv_at = r.i; r.u(4, "pv")
        h_at = r.i; r.u(8, "height")
        r.bytes_("layout")
        nv = r.u(4, "validators")
        for j in range(nv):
            r.bytes_("acct")
            if eid == epoch_id and j == 0:
                spans["T8.validator_stake"] = (r.i, r.i + 16)
            r.u(16, "stake")
        if eid == epoch_id:
            spans["T5.epoch_protocol_version"] = (pv_at, pv_at + 4)
            spans["T7.epoch_height"] = (h_at, h_at + 8)
    nb = r.u(4, "esa"); spans["T9.epoch_start_after[0]"] = (r.i, r.i + 1); r.take(nb, "esa")
    na = r.u(4, "apply_facts")
    for i in range(na):
        t = r.u(1, "vu tag")
        if t == 1:
            for _ in range(2):
                for _ in range(r.u(4, "si")):
                    r.bytes_("a"); r.u(16, "s")
            if r.u(1, "treasury tag") == 1:
                r.bytes_("treasury")
        if i == 0:
            spans["T11.minimum_stake"] = (r.i, r.i + 16)
        r.u(16, "min stake")
        if r.u(1, "split tag") == 1:
            r.u(8, "a"); r.u(8, "b"); r.u(8, "c")
            r.vec("f", lambda: r.u(8, "x")); r.vec("g", lambda: r.u(8, "x"))
    nt = r.u(4, "tx_valid")
    if nt:
        spans["T13.tx_valid[0]"] = (r.i, r.i + 1)
    return spans


def mutate(data, field, span):
    a, b = span
    old = data[a:b]
    if field == "T3.chain_id":
        new_id = b"arena-uq013" if old[4:] != b"arena-uq013" else b"arena-uq014"
        new = struct.pack("<I", len(new_id)) + new_id
    elif field in ("T2.protocol_version", "T5.epoch_protocol_version"):
        new = struct.pack("<I", 87)
    elif field == "T4.rs_parts":
        d, t = struct.unpack("<HH", old)
        t2 = t + 3
        d2 = 1 if t2 <= 3 else (t2 - 1) // 3
        new = struct.pack("<HH", d2, t2)
    elif field in ("T9.epoch_start_after[0]", "T13.tx_valid[0]"):
        new = bytes([old[0] ^ 1])
    elif field == "T1.epoch_id":
        new = bytes([old[0] ^ 1]) + old[1:]
    else:  # little-endian integers: +1
        n = len(old)
        new = ((int.from_bytes(old, "little") + 1) % (1 << (8 * n))).to_bytes(n, "little")
    return data[:a] + new + data[b:]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--checker", required=True)
    ap.add_argument("--tier", default="allFeatures")
    ap.add_argument("--cases", required=True)
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    cases = [l.strip() for l in open(a.cases) if l.strip()]
    jobs = []
    for c in cases:
        data = open(os.path.join(c, "claim.bin"), "rb").read()
        for field, span in field_offsets(data).items():
            # corpus name + case name: case names repeat across corpora
            tag = os.path.basename(os.path.dirname(os.path.dirname(os.path.abspath(c)))) + "-" + os.path.basename(c)
            d = os.path.join(a.out, tag + "." + field)
            os.makedirs(d, exist_ok=True)
            open(os.path.join(d, "claim.bin"), "wb").write(mutate(data, field, span))
            dst = os.path.join(d, "witness.bin")
            if os.path.lexists(dst):
                os.unlink(dst)
            os.symlink(os.path.join(os.path.abspath(c), "witness.bin"), dst)
            jobs.append((field, d))

    def run(chunk):
        p = subprocess.run([a.checker, "--tier", a.tier, *[d for _, d in chunk]], capture_output=True, text=True)
        return p.stdout.splitlines()
    rows = []
    with ThreadPoolExecutor(4) as ex:
        for out in ex.map(run, [jobs[i:i + 10] for i in range(0, len(jobs), 10)]):
            rows += [json.loads(l) for l in out]
    field_of = {d: f for f, d in jobs}
    table = collections.defaultdict(collections.Counter)
    reasons = collections.defaultdict(collections.Counter)
    for r in rows:
        f = field_of[r["case"]]
        table[f][r["verdict"]] += 1
        if r["verdict"] != "accept":
            reasons[f][r["reason"].split(":")[0] + ":" + r["reason"].split(":")[1][:60] if ":" in r["reason"] else r["reason"]] += 1
    doc = {"cases": len(cases), "mutants": len(jobs), "rows": len(rows), "tier": a.tier,
           "by_field": {f: dict(c) for f, c in sorted(table.items())},
           "top_reasons": {f: c.most_common(3) for f, c in sorted(reasons.items())}}
    json.dump(doc, open(os.path.join(a.out, "summary.json"), "w"), indent=1)
    print(json.dumps(doc, indent=1))
    return 0 if len(rows) == len(jobs) else 1


if __name__ == "__main__":
    sys.exit(main())
