#!/usr/bin/env python3
"""A9 word-count cross-check on nearcore's scheduler vectors.

For every case of oracle/fixtures/v3/vectors/scheduler.json (nearcore's own scheduler runs on
random inputs), computes the ChaCha20 words the run draws with the independent Python checker
(spec_check_v3_d0a.sched_words: v3lib/sched.py with a counting RNG), checks the run's new state
against the vector's post_state_borsh, and compares the count with
  * the oracle's nearcore-replica count (oracle/fixtures/v3/vectors-d0a/scheduler_words.json,
    `near-arena-oracle-v3-d0a sched-words`), and
  * optionally the Lean count (`nearspec-v3-test-words` JSON lines, --lean-jsonl).

usage: sched_words_v3.py [--lean-jsonl F] [--report OUT.json]
"""
import argparse, json, os, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import spec_check_v3_d0a as d0a  # noqa: E402

d0 = d0a.d0
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "fixtures", "v3")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--lean-jsonl")
    ap.add_argument("--report")
    a = ap.parse_args()
    sc = json.load(open(os.path.join(ROOT, "vectors", "scheduler.json")))
    oracle = json.load(open(os.path.join(ROOT, "vectors-d0a", "scheduler_words.json")))["cases"]
    lean = {}
    if a.lean_jsonl:
        for line in open(a.lean_jsonl):
            j = json.loads(line)
            lean[j["index"]] = j
    stats = {"cases": len(sc["cases"]), "state_mismatch": 0, "oracle_mismatch": 0,
             "lean_compared": 0, "lean_mismatch": 0, "nonzero": 0, "max_words": 0, "problems": []}
    for i, cs in enumerate(sc["cases"]):
        L = d0.decode_layout(bytes.fromhex(cs["shard_layout_borsh"]))
        prev = bytes.fromhex(cs["prev_state_borsh"]) if cs.get("prev_state_borsh") else None
        cong = {x["shard_id"]: ((int(x["delayed_receipts_gas"]), int(x["buffered_receipts_gas"]),
                                 x["receipt_bytes"], x["allowed_shard"]), x["missed_chunks_count"])
                for x in cs["congestion"]}
        bw = {}
        for x in cs["bandwidth_requests"]:
            r = d0.R(bytes.fromhex(x["requests_borsh"]))
            bw[x["shard_id"]] = d0.read_bw_requests(r)
            r.end()
        d0a._RNGS.clear()
        new, _ = d0.sched.run(L, d0.sched.decode_state(prev) if prev else None, cong, bw,
                              bytes.fromhex(cs["prev_block_hash"]))
        k = sum(r.words for r in d0a._RNGS)
        if new.hex() != cs["post_state_borsh"]:
            stats["state_mismatch"] += 1
            stats["problems"].append({"index": i, "problem": "python state"})
        o = oracle[i]
        if o["index"] != i or o["words"] != k or not o["replica_state_matches"]:
            stats["oracle_mismatch"] += 1
            stats["problems"].append({"index": i, "python": k, "oracle": o})
        if i in lean:
            stats["lean_compared"] += 1
            if lean[i]["words"] != k or not lean[i]["state_ok"]:
                stats["lean_mismatch"] += 1
                stats["problems"].append({"index": i, "python": k, "lean": lean[i]})
        stats["nonzero"] += k > 0
        stats["max_words"] = max(stats["max_words"], k)
    print(json.dumps({k: v for k, v in stats.items() if k != "problems"}))
    if a.report:
        open(a.report, "w").write(json.dumps(stats, indent=1, sort_keys=True) + "\n")
    return 0 if not (stats["state_mismatch"] or stats["oracle_mismatch"] or stats["lean_mismatch"]) else 1


if __name__ == "__main__":
    sys.exit(main())
