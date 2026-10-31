#!/usr/bin/env python3
"""Compare the Lean spec run of one call (`wasmbase-tool prepIf` JSON) with the chunk's outcome for
that call as the independent clean-room checker computed it (`extract_calls.py` JSON), and, given
a HOSTB dump of the generated trace, the bytes the trace sends for `log_utf8` and `value_return`.

    compare.py CALLS_JSON INDEX PREP_JSON [HOSTB_LOG]

Exit status 0 only if every compared field matches. Compared fields:
  * status: spec `fin` <-> chunk outcome not aborted;
  * gas: chunk `burnt` == loading fee + (prepaid - spec gFinal), i.e. the Wasm run's gas (instruction
    gas plus host ext costs) plus the loading fee charged before instantiation;
  * with HOSTB_LOG: the log payloads (hid 45 = log_utf8) and the return payload (hid 50 =
    value_return) carried by the trace's request bytes equal the chunk's logs and return value.
"""
import collections
import json
import sys

LOG_UTF8, VALUE_RETURN = 45, 50


def hostb_payloads(path):
    """{(ts, hid): bytes} from `nearproof-wasm-base hostb-dump` lines (request direction only)."""
    rows = collections.defaultdict(dict)
    for ln in open(path):
        if not ln.startswith("HOSTB "):
            continue
        f = dict(kv.split("=") for kv in ln.split()[1:])
        if f["dir"] != "0":
            continue
        rows[(int(f["ts"]), int(f["hid"]))][int(f["pos"])] = int(f["byte"])
    return {k: bytes(v[i] for i in sorted(v)) for k, v in sorted(rows.items())}


def main():
    calls, idx, prep = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    c = json.load(open(calls))["calls"][idx]
    p = json.load(open(prep))
    ok = True

    def rep(name, a, b):
        nonlocal ok
        m = a == b
        ok &= m
        print("%-8s %s  chunk=%s  spec/trace=%s" % ("MATCH" if m else "DIFFER", name, a, b))

    print("call: code %s method %s prepaid %d input %s" % (c["code_sha256"], c["method"], c["prepaid"], c["input"]))
    if not p.get("eligible"):
        print("NOT ELIGIBLE for the Wasm AIR:", p)
        sys.exit(1)
    rep("status", "fin" if c["aborted"] is None else c["aborted"], p["status"])
    rep("burnt gas", c["burnt"], c["loading_fee"] + c["prepaid"] - p["gFinal"])
    print("         (loading fee %d, spec Wasm gas %d, steps %d)" % (c["loading_fee"], c["prepaid"] - p["gFinal"], p["steps"]))
    if len(sys.argv) > 4:
        pl = hostb_payloads(sys.argv[4])
        logs = [v.hex() for (ts, hid), v in pl.items() if hid == LOG_UTF8]
        rets = [v.hex() for (ts, hid), v in pl.items() if hid == VALUE_RETURN]
        rep("logs", c["logs"], logs)
        rep("return", c["ret"], rets[-1] if rets else None)
    print("ALL MATCH" if ok else "MISMATCH")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
