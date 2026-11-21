#!/usr/bin/env python3
"""E2E M6 (lane A, HOSTIF): host functions used by the corpus, by frequency.

Inputs (not in the repo):
  * the m3 call tape  (default /data/illia/nearproof-deps/e2e-laneA/m3/tape.jsonl): one line per
    call; eligible calls carry `prep.hosts` (one entry per dynamic host event, with its `hid`);
  * the code imports (default /data/illia/nearproof-deps/e2e-laneA/code/*.wat, plus any `.wasm`
    in --codes dirs): the static `(import "env" NAME)` list of every contract code;
  * the host-id table `WasmBase/HostChip.lean` (+ `ed25519_verify` = 61, `M2Check.hostFnsM2`).

Output: JSON (per host function: hid, eligible dynamic calls/events, static import weight over all
calls, and the observable dynamic lower bounds for non-eligible calls: `log_utf8` from the receipt
logs, `value_return` from a non-null return value) and a markdown table.

Usage: python3 host_freq.py [--tape T] [--wat-dir D] [--hostchip F] [--out-json J] [--out-md M]
"""
import argparse
import collections
import glob
import json
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", "..", "..", ".."))


def host_table(path):
    src = open(path).read()
    tab = {}
    for m in re.finditer(r'\((\d+), "([a-z0-9_]+)", (\d+), (\d+)\)', src):
        tab[int(m.group(1))] = m.group(2)
    tab[61] = "ed25519_verify"  # M2Check.hostFnsM2
    return tab


def wat_imports(path):
    return sorted(set(re.findall(r'\(import "env" "([a-z0-9_]+)"', open(path).read())))


def wasm_imports(path):
    """Imports of module "env" from a binary module (import section, id 2)."""
    b = open(path, "rb").read()
    i = 8
    out = set()

    def leb(j):
        r, s = 0, 0
        while True:
            x = b[j]
            j += 1
            r |= (x & 0x7F) << s
            s += 7
            if x < 0x80:
                return r, j

    while i < len(b):
        sid = b[i]
        n, j = leb(i + 1)
        end = j + n
        if sid == 2:
            cnt, j = leb(j)
            for _ in range(cnt):
                ml, j = leb(j)
                mod = b[j:j + ml].decode()
                j += ml
                nl, j = leb(j)
                name = b[j:j + nl].decode()
                j += nl
                kind = b[j]
                j += 1
                if kind == 0:
                    _, j = leb(j)
                elif kind == 1:
                    j += 1
                    fl, j = leb(j)
                    _, j = leb(j)
                    if fl & 1:
                        _, j = leb(j)
                elif kind == 2:
                    fl, j = leb(j)
                    _, j = leb(j)
                    if fl & 1:
                        _, j = leb(j)
                elif kind == 3:
                    j += 2
                if mod == "env":
                    out.add(name)
        i = end
    return sorted(out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--tape", default="/data/illia/nearproof-deps/e2e-laneA/m3/tape.jsonl")
    ap.add_argument("--wat-dir", default="/data/illia/nearproof-deps/e2e-laneA/code")
    ap.add_argument("--codes", nargs="*", default=["/data/illia/nearproof-deps/e2e-m1/codes",
                                                   "/data/illia/nearproof-deps/e2e-laneA/code"])
    ap.add_argument("--hostchip", default=os.path.join(
        REPO, "research/near-compression/wasm-base-lean/WasmBase/HostChip.lean"))
    ap.add_argument("--out-json", default=os.path.join(HERE, "host-freq.json"))
    ap.add_argument("--out-md", default=os.path.join(HERE, "host-freq.md"))
    a = ap.parse_args()

    tab = host_table(a.hostchip)
    name2hid = {v: k for k, v in tab.items()}

    # static imports per code prefix (8 hex) / full hash
    imports = {}
    for p in glob.glob(os.path.join(a.wat_dir, "*.wat")):
        imports[os.path.basename(p)[:-4]] = wat_imports(p)
    for d in a.codes:
        for p in glob.glob(os.path.join(d, "*.wasm")):
            h = os.path.basename(p)[:-5]
            try:
                imports[h[:8]] = wasm_imports(p)
            except Exception:  # noqa: BLE001
                pass

    calls = 0
    elig_calls = 0
    calls_by_code = collections.Counter()
    elig_by_code = collections.Counter()
    elig_nohost = collections.Counter()  # eligible calls with no host event
    ev = collections.Counter()          # eligible: events per hid
    ev_calls = collections.Counter()    # eligible: calls with >= 1 event of hid
    log_lb = 0                          # non-eligible: log lines (log_utf8/utf16 events, lower bound)
    log_calls_lb = 0
    ret_lb = 0                          # non-eligible: calls with a return value (value_return >= 1)
    for line in open(a.tape):
        d = json.loads(line)
        if "seq" not in d:
            continue
        calls += 1
        code = d.get("code_sha256", "")
        calls_by_code[code] += 1
        prep = d.get("prep") or {}
        if prep.get("eligible"):
            elig_calls += 1
            elig_by_code[code] += 1
            seen = set()
            if not prep.get("hosts"):
                elig_nohost[code] += 1
            for h in prep.get("hosts", []):
                ev[h["hid"]] += 1
                seen.add(h["hid"])
            for h in seen:
                ev_calls[h] += 1
        else:
            real = d.get("real") or {}
            nl = len(real.get("logs") or [])
            log_lb += nl
            log_calls_lb += 1 if nl else 0
            ret_lb += 1 if real.get("ret") is not None else 0

    static_w = collections.Counter()      # all calls
    static_w_ne = collections.Counter()   # non-eligible calls
    unknown_codes = {}
    for code, n in calls_by_code.items():
        imp = imports.get(code[:8])
        if imp is None:
            unknown_codes[code] = n
            continue
        for nm in imp:
            static_w[nm] += n
            static_w_ne[nm] += n - elig_by_code[code]

    names = set(static_w) | {tab.get(h, f"hid{h}") for h in ev}
    rows = []
    for nm in names:
        hid = name2hid.get(nm)
        rows.append({
            "name": nm,
            "hid": hid,
            "in_table": hid is not None,
            "eligible_calls_with": ev_calls.get(hid, 0) if hid is not None else 0,
            "eligible_events": ev.get(hid, 0) if hid is not None else 0,
            "static_import_calls_all": static_w.get(nm, 0),
            "static_import_calls_noneligible": static_w_ne.get(nm, 0),
        })
    rows.sort(key=lambda r: (-r["eligible_events"], -r["static_import_calls_all"], r["name"]))
    out = {
        "tape": a.tape,
        "calls": calls,
        "eligible_calls": elig_calls,
        "calls_by_code": dict(calls_by_code),
        "eligible_by_code": dict(elig_by_code),
        "imports_by_code": {k: v for k, v in imports.items()},
        "codes_without_imports": unknown_codes,
        "eligible_without_host_events_by_code": dict(elig_nohost),
        "noneligible_dynamic_lower_bounds": {
            "log_lines": log_lb, "calls_with_logs": log_calls_lb, "calls_with_return_value": ret_lb},
        "hosts": rows,
    }
    json.dump(out, open(a.out_json, "w"), indent=1)

    md = []
    md.append("# Corpus host functions by frequency (E2E M6, generated by `host_freq.py`)\n")
    md.append(f"Tape: `{a.tape}` — {calls} calls, {elig_calls} eligible (dynamic host events "
              "recorded in `prep.hosts`).  Non-eligible calls: static imports of the call's code, "
              "weighted by calls (an upper bound on the calls that *can* reach the function); "
              f"observable dynamic lower bounds: {log_lb} log lines in {log_calls_lb} calls "
              f"(`log_utf8`/`log_utf16`), {ret_lb} calls with a return value (`value_return`).  "
              f"Eligible calls with no host event at all: {sum(elig_nohost.values())} ("
              + ", ".join(f"`{k[:8]}` {v}" for k, v in elig_nohost.items()) + ").\n")
    md.append("| host | hid | eligible calls using it | eligible events | calls importing it (all) | of which non-eligible |")
    md.append("|---|---|---|---|---|---|")
    for r in rows:
        md.append(f"| `{r['name']}` | {r['hid'] if r['hid'] is not None else '— (not in table)'} | "
                  f"{r['eligible_calls_with']} | {r['eligible_events']} | {r['static_import_calls_all']} | "
                  f"{r['static_import_calls_noneligible']} |")
    if unknown_codes:
        md.append("\nCodes without an import list (no `.wat`/`.wasm` found): " +
                  ", ".join(f"`{k[:8]}` ({v} calls)" for k, v in unknown_codes.items()))
    md.append("\nImports by code: " + "; ".join(f"`{k}`: {', '.join(v)}" for k, v in sorted(imports.items())))
    open(a.out_md, "w").write("\n".join(md) + "\n")
    print("\n".join(md[:40]))


if __name__ == "__main__":
    main()
