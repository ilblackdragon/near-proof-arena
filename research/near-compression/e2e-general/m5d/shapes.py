#!/usr/bin/env python3
"""FINAL-template shape census (lane G, G-2 item 4).

For every corpus case, run the Lean checker's FINAL (`m5d-tool dump`) and record the features
that select a FINAL template class: header version, transactions, validator proposals, bandwidth
requests, proposed split, Reed-Solomon (d, t), shard count and id width, |chain_id|, receipts,
outcomes, body length. Then tally the classes by corpus frequency.

  shapes.py CORPUS_DIR[,DIR…] OUT.jsonl [--jobs 4] [--limit N] [--resume]    # run
  shapes.py --report OUT.jsonl                              # tally only
"""
import json, os, subprocess, sys, tempfile, collections
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
TOOL = os.path.join(HERE, "lean/.lake/build/bin/m5d-tool")
TMP = "/data/illia/nearproof-deps/e2e-m5d/g2shape"


def shape(case):
    os.makedirs(TMP, exist_ok=True)
    fd, out = tempfile.mkstemp(suffix=".json", dir=TMP)
    os.close(fd)
    try:
        r = subprocess.run([TOOL, "dump", case, out], capture_output=True, text=True, timeout=600)
        if r.returncode != 0:
            return {"case": case, "error": (r.stderr or r.stdout).strip()[-200:]}
        d = json.load(open(out))
    except Exception as e:  # noqa: BLE001
        return {"case": case, "error": repr(e)[-200:]}
    finally:
        if os.path.exists(out):
            os.remove(out)
    h, fi = d["header"], d["finIn"]
    pre = bytes.fromhex(d["pre"])
    # pre = borsh tag ‖ borsh statement id ‖ u32 pv ‖ borsh chain id ‖ …
    o = 0
    for _ in range(2):
        n = int.from_bytes(pre[o:o + 4], "little"); o += 4 + n
    o += 4
    chain_len = int.from_bytes(pre[o:o + 4], "little")
    sids = [int(s) for s in fi["shardIds"]]
    return {
        "case": case,
        "tag": int(h["tag"]), "txs": len(fi["txs"]), "props": int(h["nProposals"]),
        "bw": int(h["nBw"]), "split": h["split"] in (True, "true", "True", 1),
        "rs": [int(d["rsD"]), int(d["rsT"])], "nshards": len(sids),
        "sidmax": max(sids) if sids else 0, "chain": chain_len,
        "rcpts": len(fi["outgoing"]), "outcomes": len(fi["outcomeLeaves"]),
        "n": int(d["outputs"]["encodedLength"]), "implicit": int(d.get("implicit", 0)),
    }


def klass(s):
    """The FINAL class a case needs (F1 = the built one)."""
    if "error" in s:
        return "dump-failed"
    feats = []
    if s["tag"] != 4: feats.append(f"hdrV{s['tag'] + 1}")
    if s["txs"]: feats.append("tx")
    if s["props"]: feats.append("proposals")
    if s["bw"]: feats.append("bw")
    if s["split"]: feats.append("split")
    if s["rs"] != [5, 16]: feats.append(f"rs{s['rs'][0]}/{s['rs'][1]}")
    if s["nshards"] != 6: feats.append(f"shards{s['nshards']}")
    if s["sidmax"] >= 1 << 16: feats.append("sid>u16")
    if s["chain"] != 14: feats.append(f"chain{s['chain']}")
    return "F1" if not feats else "+".join(feats)


def report(path):
    rows = [json.loads(l) for l in open(path)]
    c = collections.Counter(klass(s) for s in rows)
    ok = [s for s in rows if "error" not in s]
    print(f"cases {len(rows)}, dumped {len(ok)}")
    for k, v in c.most_common():
        print(f"  {v:6d}  {100.0 * v / len(rows):6.2f} %  {k}")
    feat = collections.Counter()
    for s in ok:
        for f in klass(s).split("+"):
            feat[f] += 1
    print("single features (dumped cases, a case can have several):")
    for k, v in feat.most_common():
        print(f"  {v:6d}  {100.0 * v / max(1, len(ok)):6.2f} %  {k}")
    errs = collections.Counter(s["error"][:60] for s in rows if "error" in s)
    print("dump failures (top):")
    for k, v in errs.most_common(8):
        print(f"  {v:6d}  {k}")
    if ok:
        def q(xs, p): xs = sorted(xs); return xs[min(len(xs) - 1, int(p * len(xs)))]
        for key in ("rcpts", "outcomes", "n", "txs"):
            xs = [s[key] for s in ok]
            print(f"  {key}: p50 {q(xs, .5)}  p99 {q(xs, .99)}  max {max(xs)}")


def main():
    if sys.argv[1] == "--report":
        report(sys.argv[2]); return
    corpus, out = sys.argv[1], sys.argv[2]
    jobs = int(sys.argv[sys.argv.index("--jobs") + 1]) if "--jobs" in sys.argv else 4
    cases = sorted(os.path.join(cd, c) for cd in corpus.split(",") for c in os.listdir(cd)
                   if os.path.isdir(os.path.join(cd, c)))
    if "--limit" in sys.argv:
        cases = cases[:int(sys.argv[sys.argv.index("--limit") + 1])]
    done = set()
    if "--resume" in sys.argv and os.path.exists(out):
        done = {json.loads(l)["case"] for l in open(out) if l.strip()}
        cases = [c for c in cases if c not in done]
    with open(out, "a" if done else "w") as f, ThreadPoolExecutor(jobs) as ex:
        for s in ex.map(shape, cases):
            f.write(json.dumps(s) + "\n"); f.flush()
    report(out)


if __name__ == "__main__":
    main()
