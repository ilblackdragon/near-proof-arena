#!/usr/bin/env python3
"""A7 evidence: how far does unfolding (per path copy) exceed the recorded bytes?

For every case directory, every recorded `PartialState` of the witness (main and implicit
transitions) is unfolded from its roots (stored nodes no other stored node references):
`full_unfold` = Σ over every reachable node *occurrence* of its bytes, plus every reachable
value occurrence — an upper bound of `unfoldBytes`' pre part for any key set. Reports the
recorded bytes, the full unfold, and their ratio (1.0 = no shared subtree). Works on D0 and
D1 witnesses (no relation semantics needed). Also aggregates the `unfold` field of checker
JSONL files given with --jsonl.

usage: a7_measure_v3.py [--jsonl F ...] CASE_DIR...
"""
import argparse, collections, json, os, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import spec_check_v3 as d0  # noqa: E402
from v3lib.prim import decode_node, sha  # noqa: E402

sys.setrecursionlimit(10000)


def full(store, h, memo):
    if h in memo:
        return memo[h]
    raw = store.get(h)
    if raw is None:
        return 0
    try:
        n = decode_node(raw)
    except Exception:
        return 0
    tot = len(raw)
    if n.vref is not None and n.vref[1] in store:
        tot += len(store[n.vref[1]])
    if n.kind == 'ext':
        tot += full(store, n.child, memo)
    elif n.kind == 'branch':
        tot += sum(full(store, c, memo) for c in n.children.values())
    memo[h] = tot
    return tot


def roots(store):
    ref = set()
    for raw in store.values():
        try:
            n = decode_node(raw)
        except Exception:
            continue
        if n.vref is not None:
            ref.add(n.vref[1])
        if n.kind == 'ext':
            ref.add(n.child)
        elif n.kind == 'branch':
            ref.update(n.children.values())
    out = []
    for h, raw in store.items():
        if h in ref:
            continue
        try:
            decode_node(raw)
            out.append(h)
        except Exception:
            pass
    return out


def measure(d):
    wb = open(os.path.join(d, "witness.bin"), "rb").read()
    r = d0.R(wb); r.bytes(); sw = r.bytes()
    try:
        W = d0.decode_state_witness(sw)
        trs = [W['main']] + W['implicit']
    except d0.OOD:
        # D1 witnesses (transactions): the implicit transitions follow the transactions; take
        # the main transition only
        r = d0.R(sw); r.u8(); r.hash(); r.u8(); d0.read_inner(r); r.u64(); d0.read_signature(r)
        trs = [d0.read_transition(r)]
    rec = unf = 0
    for T in trs:
        store = {sha(v): v for v in T['base_state']}
        rec += sum(len(v) for v in store.values())
        memo = {}
        unf += sum(full(store, h, memo) for h in roots(store))
    return rec, unf


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--jsonl", nargs="*", default=[])
    ap.add_argument("cases", nargs="*")
    a = ap.parse_args()
    ratios, recs, unfs, bad = [], [], [], 0
    for d in a.cases:
        try:
            rec, unf = measure(d)
        except Exception:
            bad += 1
            continue
        recs.append(rec); unfs.append(unf)
        ratios.append(unf / rec if rec else 1.0)
    out = {"cases": len(recs), "undecodable": bad}
    if recs:
        out.update(recorded_max=max(recs), full_unfold_max=max(unfs), ratio_max=round(max(ratios), 4),
                   cases_with_sharing=sum(1 for x in ratios if x > 1.0))
    vals = []
    for f in a.jsonl:
        for line in open(f):
            j = json.loads(line)
            if j.get("unfold") is not None and j.get("verdict") in ("accept", "out_of_domain"):
                vals.append(j["unfold"])
    if vals:
        vals.sort()
        q = lambda p: vals[min(len(vals) - 1, int(p * len(vals)))]
        out["unfold_bytes"] = {"n": len(vals), "min": vals[0], "p50": q(.5), "p90": q(.9),
                               "p99": q(.99), "max": vals[-1]}
    print(json.dumps(out))


if __name__ == "__main__":
    main()
