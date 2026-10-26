#!/usr/bin/env python3
"""Per-step nearcore outcome tables of cross-family runs (`collect_xfam.py` manifests).

For every step label (without the run-specific step index of curve steps it is kept), each run's
outcome is summarized from nearcore's outcome tree: the status of the first receipt (`ok:<value
prefix>` or `fail:<error kind>`), the number of receipts that failed, and for yield steps the
callback return. A cell lists the distinct summaries across runs with their run counts.
"""
import argparse
import collections
import json
import re
from pathlib import Path


def kind_of(failure):
    if not failure:
        return ""
    m = re.search(r"(ExecutionError\(\"[^\"]{0,40}|[A-Z][A-Za-z]+\s*\{|[A-Z][a-zA-Z]+\()", failure)
    if "does not exist" in failure:
        return "key/account does not exist"
    if "too high to burn" in failure:
        return "GasKeyBalanceTooHigh"
    if "insufficient balance" in failure:
        return "insufficient gas-key balance"
    if "not found" in failure and "Global contract" in failure:
        return "global contract not found"
    if "enough balance to cover storage" in failure:
        return "LackBalanceForState"
    if "Exceeded the account balance" in failure:
        return "BalanceExceeded"
    if "CodeDoesNotExist" in failure:
        return "CodeDoesNotExist"
    if "panicked" in failure:
        return "panic"
    e = re.search(r'ExecutionError\("([^"]{0,60})', failure)
    if e:
        return e.group(1).rstrip(".")
    e = re.search(r"Action #\d+: ([A-Za-z]+)", failure)
    if e:
        return e.group(1)
    return (m.group(1) if m else failure[:40]).strip(' "({')


def curve_outcome(step):
    """The host call's outcome in a curve-callbacks step: the u64 the host returned (`ret0`/`ret1`/
    `ret2`, the first 8 bytes of the returning receipt's value) or the failure of the receipt that
    called it. The host runs in the last curve-account receipt that fails or returns a value:
    dispatchers (`then`, `yield`, `yslot`) and refunds return nothing, and `echo` runs before the
    callback that consumes its result. `rslot` steps report the resume byte (`resume:01`)."""
    rets = {"0000000000000000": "ret0", "0100000000000000": "ret1", "0200000000000000": "ret2"}
    rs = [r for r in step["receipts"] if r.get("executor", "").endswith("xcurve")
          and (r["status"] == "failure" or r.get("value"))]
    if not rs:
        return "no host outcome (pending or resumed later)"
    r = rs[-1]
    if r["status"] == "failure":
        return "fail:" + kind_of(r.get("failure"))
    if len(r["value"]) == 2:
        return f"resume:{r['value']}"
    return rets.get(r["value"][:16], "value " + r["value"][:16])


def yield_outcome(step):
    """yield-congestion: a create step's callback (`cb:01<payload>` resumed / `cb:02` timeout, blocks
    after the create receipt, `Q` if the yield shard's delayed queue was non-empty when it was
    applied) or a resume step's return byte."""
    rs = [r for r in step["receipts"] if r.get("executor") == "s0xyield"]
    if not rs:
        return "pending at run end"
    first = rs[0]
    if first["status"] == "failure":
        return "fail:" + kind_of(first.get("failure"))
    q = lambda r: "Q" if (r.get("congestion_before") or {}).get("delayed", 0) > 0 else ""
    if ".create" not in step["label"]:
        return f"ret {first.get('value')}{q(first)}"
    cbs = [r for r in rs[1:] if r["status"] == "value" and (r.get("value") or "")[:2] in ("01", "02")]
    if not cbs:
        return f"created{q(first)}; callback pending at run end"
    cb = cbs[0]
    v = cb["value"]
    payload = bytes.fromhex(v[2:]).decode("ascii", "replace") if len(v) > 2 else ""
    return f"created{q(first)}; cb:{v[:2]}{(' ' + payload) if payload else ''} +{cb['height'] - first['height']}{q(cb)}"


def summarize(step):
    if not step["executed"]:
        return "tx not executed"
    rs = [r for r in step["receipts"] if r.get("executor")]
    if not rs:
        return "receipts pending at run end"
    if step["label"].startswith("successor.curve-callbacks."):
        return curve_outcome(step)
    if step["label"].startswith("successor.yield-congestion."):
        return yield_outcome(step)
    first = rs[0]
    s = f"ok:{(first.get('value') or '')[:8]}" if first["status"] != "failure" else f"fail:{kind_of(first.get('failure'))}"
    fails = [kind_of(r.get("failure")) for r in rs[1:] if r["status"] == "failure"]
    if fails:
        s += " +" + ",".join(sorted(set(fails)))
    pend = len([r for r in step["receipts"] if not r.get("executor")])
    if pend:
        s += f" ({pend} pending at run end)"
    return s


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("manifests", nargs="+", type=Path)
    ap.add_argument("--out", type=Path, required=True)
    a = ap.parse_args()
    rows = collections.OrderedDict()
    scen = None
    for p in a.manifests:
        m = json.loads(p.read_text())
        scen = m["scenario"]
        for s in m["steps"]:
            if ".flood." in s["label"]:
                continue
            rows.setdefault(s["label"].split(".", 2)[2], collections.Counter())[summarize(s)] += 1
    lines = [f"# {scen}: nearcore outcomes per step ({len(a.manifests)} runs)", "",
             "| step | nearcore (first receipt; later failures) × runs |", "|---|---|"]
    for k, c in rows.items():
        lines.append(f"| `{k}` | " + "; ".join(f"{v} ×{n}" for v, n in c.most_common()) + " |")
    a.out.write_text("\n".join(lines) + "\n")


if __name__ == "__main__":
    main()
