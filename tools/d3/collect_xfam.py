#!/usr/bin/env python3
"""Bind a cross-family scenario run (`oracle/v3-successor` `src/xfam.rs`, `NEAR_SUCCESSOR_SCENARIO`
= yield-congestion | curve-callbacks | genesis-tx | gaskey-target | rollback-refund) to nearcore's
recorded outcomes and to its cases.

Input: a run directory with `summary.json`, `xfam-<chain>.json` (every scenario transaction with
nearcore's outcome tree, the per-height chunk-header congestion info) and the case directories.
Every fact reported comes from nearcore's own outcomes or chunk headers, never from a label or from
Lean. The collection fails (exit 1) if a planned step was never submitted, a submitted step has no
executed outcome, an honest witness was rejected by the cold validator, or a family's defining
condition does not hold (listed per scenario in `check_family`).

Output (`--out DIR`): `manifest.json` (per step: inclusion height, every receipt with executor,
shard, height, status and the congestion of its shard around it; per family: the defining facts),
`honest.txt` / `mutants.txt` (absolute case paths of the family population: every honest case with
scenario activity and every mutant of one).
"""
import argparse
import bisect
import collections
import hashlib
import json
from pathlib import Path
import re
import sys


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def status_of(o):
    st = o.get("status")
    if isinstance(st, dict) and "SuccessValue" in st:
        return "value", st["SuccessValue"]
    if isinstance(st, dict) and "SuccessReceiptId" in st:
        return "receipt", st["SuccessReceiptId"]
    return "failure", st


def index_cases(run):
    """(chain, shard) -> sorted [(height, rel)], label -> [rel], rel -> meta, base -> [mutant rel]"""
    by_shard = collections.defaultdict(list)
    by_label = collections.defaultdict(list)
    metas, mutants = {}, collections.defaultdict(list)
    for meta_path in sorted(run.glob("*/*/meta.json")):
        meta = json.loads(meta_path.read_text())
        rel = str(meta_path.parent.relative_to(run))
        if meta.get("kind") == "mutant":
            mutants[meta["base"]].append(rel)
            continue
        m = re.fullmatch(r"(\d+)-h(\d+)-s(\d+)", meta_path.parent.name)
        by_shard[(int(m.group(1)), m.group(3))].append((int(m.group(2)), rel))
        metas[rel] = meta
        for label in meta.get("tx_labels", []) + meta.get("new_tx_labels", []):
            by_label[label].append(rel)
    for v in by_shard.values():
        v.sort()
    return by_shard, by_label, metas, mutants


def case_after(by_shard, chain, shard, height):
    """The first honest case of the shard created after `height` (its witness validates the
    application of the chunk at `height`; missing chunks shift this to the next produced one)."""
    v = by_shard.get((chain, shard), [])
    i = bisect.bisect_right(v, (height, "￿"))
    return v[i][1] if i < len(v) else None


def shard_of(account, shards):
    """Shard id of an account in the static layout `s1 < s2 < ...` (boundaries); `shards` maps
    `s<i>` to the id of shard index i."""
    bounds = sorted((k for k in shards if re.fullmatch(r"s\d", k)), key=lambda k: int(k[1:]))
    idx = 0
    for b in bounds[1:]:
        if account >= b:
            idx = int(b[1:])
    return shards[f"s{idx}"]


class Headers:
    def __init__(self, rows):
        self.by = {}
        self.new = collections.defaultdict(list)
        for r in rows:
            self.by[(r["shard"], r["height"])] = r
            if r["new"]:
                self.new[r["shard"]].append(r["height"])
        for v in self.new.values():
            v.sort()

    def around(self, shard, height):
        """Congestion of the shard before (header of the chunk at `height`, i.e. after the previous
        chunk was applied) and after (header of the next new chunk) applying the chunk at `height`."""
        pre = self.by.get((shard, height))
        nxt = [h for h in self.new.get(shard, []) if h > height]
        post = self.by.get((shard, nxt[0])) if nxt else None
        f = lambda r: None if r is None else dict(delayed=int(r["delayed_receipts_gas"]), buffered=int(r["buffered_receipts_gas"]),
                                                    receipt_bytes=r["receipt_bytes"], bandwidth_requests=r["bandwidth_requests"])
        return f(pre), f(post)


def steps_of(sc, chain, by_shard, by_label, headers):
    shards = sc["shards"]
    rows, problems = [], []
    planned = {p["label"] for p in sc["planned"]}
    submitted = {s["label"] for s in sc["submitted"]}
    for missing in sorted(planned - submitted):
        problems.append(f"chain {chain}: step {missing} never submitted")
    for sub in sc["submitted"]:
        outs = sub["outcomes"]
        tx = outs[0] if outs else {"executed": False}
        if not tx.get("executed"):
            rows.append(dict(label=sub["label"], chain=chain, executed=False, submitted_height=sub["height"]))
            # a transaction dropped by the pool / chunk producer: recorded, never counted as a match
            continue
        receipts = []
        for o in outs[1:]:
            if not o.get("executed"):
                receipts.append(dict(id=o["id"], executed=False))
                continue
            sh = shard_of(o["executor"], shards)
            kind, val = status_of(o)
            pre, post = headers.around(sh, o["height"])
            receipts.append(dict(id=o["id"], executor=o["executor"], shard=sh, height=o["height"], status=kind,
                                 value=val if kind == "value" else None, failure=val if kind == "failure" else None,
                                 gas_burnt=o["gas_burnt"], tokens_burnt=o.get("tokens_burnt"),
                                 congestion_before=pre, congestion_after=post,
                                 case=case_after(by_shard, chain, sh, o["height"])))
        rows.append(dict(label=sub["label"], chain=chain, executed=True, submitted_height=sub["height"],
                         signer=sub["signer"], receiver=sub["receiver"], actions=sub["actions"],
                         signed_with=sub["signed_with"], tx_height=tx["height"], tx_status=status_of(tx)[0],
                         signer_shard=shard_of(sub["signer"], shards), receiver_shard=shard_of(sub["receiver"], shards),
                         receipts=receipts, included_cases=sorted(set(by_label.get(sub["label"], [])))))
    return rows, problems


def check_family(scenario, steps, headers_rows, metas, sc_list):
    """The defining facts of the family, from nearcore's outcomes and headers only."""
    facts, problems = {}, []
    executed = [s for s in steps if s["executed"]]
    if scenario == "YieldCongestion":
        ysh = {sc["shards"]["s0xyield"] for sc in sc_list}
        csh = {sc["shards"]["s1xcall"] for sc in sc_list}
        delayed = [r for r in headers_rows if r["shard"] in ysh and int(r["delayed_receipts_gas"]) > 0]
        buffered = [r for r in headers_rows if int(r["buffered_receipts_gas"]) > 0]
        facts["yield_shard_headers_with_delayed_gas"] = len(delayed)
        facts["max_delayed_receipts_gas"] = max((int(r["delayed_receipts_gas"]) for r in delayed), default=0)
        facts["headers_with_buffered_gas"] = len(buffered)
        facts["caller_shard_headers_with_buffered_gas"] = len([r for r in buffered if r["shard"] in csh])
        facts["max_buffered_receipts_gas"] = max((int(r["buffered_receipts_gas"]) for r in buffered), default=0)
        # yield receipts applied while the yield shard had a non-empty delayed queue
        under = []
        for s in executed:
            if ".flood." in s["label"]:
                continue
            for r in s["receipts"]:
                if r.get("executor") == "s0xyield" and r.get("congestion_before") and r["congestion_before"]["delayed"] > 0:
                    under.append((s["label"], r["height"], r["status"], r.get("value")))
        facts["yield_receipts_applied_with_delayed_queue"] = len(under)
        cb = {}
        for s in executed:
            if "create" not in s["label"].split(".")[3] or ".flood." in s["label"]:
                continue
            ys = [r for r in s["receipts"] if r.get("executor") == "s0xyield" and r.get("status") == "value" and r.get("value")
                  and len(r["value"]) != 64]
            cb[s["label"]] = [dict(height=r["height"], value=r["value"][:40], congestion_before=r["congestion_before"]) for r in ys]
        facts["callbacks"] = cb
        if len(delayed) < 10:
            problems.append("fewer than 10 yield-shard headers with a non-empty delayed queue")
        if not buffered:
            problems.append("no header with nonzero buffered receipts gas")
        if not under:
            problems.append("no yield receipt applied while the delayed queue was non-empty")
    elif scenario == "GenesisTx":
        g = [m for m in metas.values() if m.get("features", {}).get("xfam", {}).get("b2_genesis")]
        facts["genesis_b2_cases"] = len(g)
        facts["genesis_b2_with_new_transactions"] = len([m for m in g if m["features"]["xfam"]["n_new_transactions"] > 0])
        facts["genesis_b2_with_main_transactions"] = len([m for m in g if m["features"]["xfam"]["n_transactions"] > 0])
        facts["genesis_b2_n_implicit"] = dict(collections.Counter(str(m["features"]["n_implicit"]) for m in g))
        facts["genesis_b2_nearcore"] = dict(collections.Counter(m["nearcore"] for m in g))
        if not g:
            problems.append("no genesis-B2 case")
        if facts["genesis_b2_with_main_transactions"]:
            problems.append("a genesis-B2 witness with main-transition transactions (genesis chunks have none)")
    else:
        kinds = collections.Counter()
        for s in executed:
            for r in s["receipts"]:
                if r.get("executed", True) is False:
                    continue
                kinds[r["status"]] += 1
        facts["receipt_status_counts"] = dict(kinds)
        facts["cross_shard_steps"] = len([s for s in executed if s["signer_shard"] != s["receiver_shard"]])
    unexecuted = [s["label"] for s in steps if not s["executed"]]
    facts["unexecuted_transactions"] = unexecuted
    return facts, problems


def collect(run):
    summary = json.loads((run / "summary.json").read_text())
    by_shard, by_label, metas, mutants = index_cases(run)
    out = dict(run=str(run), chain_params=summary["chains"], honest=summary["honest_witnesses"],
               honest_accepted_by_nearcore=summary["honest_accepted_by_nearcore"], mutants=summary["mutants"])
    problems = []
    if summary["honest_witnesses"] != summary["honest_accepted_by_nearcore"]:
        problems.append("an honest witness was rejected by the cold validator")
    steps, hdr_rows, scs, scenario = [], [], [], None
    for p in sorted(run.glob("xfam-*.json")):
        chain = int(re.fullmatch(r"xfam-(\d+)\.json", p.name).group(1))
        sc = json.loads(p.read_text())
        scenario = sc["scenario"]
        scs.append(sc)
        out.setdefault("xfam_json_sha256", {})[p.name] = sha(p)
        out.setdefault("shards", {})[chain] = sc["shards"]
        out.setdefault("contracts", sc["contracts"])
        headers = Headers(sc["chunk_headers"])
        hdr_rows += [dict(r, chain=chain) for r in sc["chunk_headers"]]
        rows, p2 = steps_of(sc, chain, by_shard, by_label, headers)
        steps += rows
        problems += p2
    if scenario is None:
        problems.append("no xfam-<chain>.json")
    out["scenario"] = scenario
    facts, p3 = check_family(scenario, steps, hdr_rows, metas, scs)
    problems += p3
    out["facts"] = facts
    out["steps"] = steps
    # the family population: honest cases with scenario activity, and every mutant of one
    active = set()
    for rel, m in metas.items():
        x = m.get("features", {}).get("xfam")
        labels = m.get("tx_labels", []) + m.get("new_tx_labels", [])
        ran = any(e.get("name") in ("xfam", "xcurve") for e in m.get("executed_contracts", []))
        if scenario == "GenesisTx":
            if x and (x.get("b2_genesis") or int(re.search(r"-h(\d+)-", rel).group(1)) <= 10004):
                active.add(rel)
        elif ran or any(l.startswith("successor.") for l in labels):
            active.add(rel)
    for s in steps:
        for r in s.get("receipts", []):
            if r.get("case"):
                active.add(r["case"])
        active.update(s.get("included_cases", []))
    honest = sorted(active)
    muts = sorted(x for rel in honest for x in mutants.get(Path(rel).name, []))
    out["population"] = dict(honest=len(honest), mutants=len(muts),
                             honest_nearcore=dict(collections.Counter(metas[r]["nearcore"] for r in honest)))
    out["problems"] = problems
    return out, [str((run / r).resolve()) for r in honest], [str((run / r).resolve()) for r in muts]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--source", type=Path, required=True)
    ap.add_argument("--out", type=Path, required=True)
    a = ap.parse_args()
    out, honest, muts = collect(a.source)
    a.out.mkdir(parents=True, exist_ok=True)
    (a.out / "manifest.json").write_text(json.dumps(out, indent=1) + "\n")
    (a.out / "honest.txt").write_text("".join(x + "\n" for x in honest))
    (a.out / "mutants.txt").write_text("".join(x + "\n" for x in muts))
    print(json.dumps(dict(scenario=out["scenario"], population=out["population"], facts={k: v for k, v in out["facts"].items() if k != "callbacks"})))
    for p in out["problems"]:
        print("PROBLEM:", p, file=sys.stderr)
    return 1 if out["problems"] else 0


if __name__ == "__main__":
    sys.exit(main())
