#!/usr/bin/env python3
"""E2E milestone M3: replay every corpus FunctionCall with the chunk's own host answers.

    sweep.py TAPE.jsonl OUT_DIR [--jobs N] [--tool WASMBASE_TOOL] [--prover NEARPROOF_WASM_BASE]

TAPE.jsonl is the output of `wasmbase-tape` (research/near-compression/wasm-base-lean/Tape.lean): the
unmodified Lean checker `Schema.checkVersioned (Tier.cfg .allFeatures)` run on the cases, one line per
Wasm call it made, with the call's host tape (`prep`, the `wasmbase-tool prepIf` format) recorded from
the checker's own CallCtx and trie-backed store.

For every call whose code the current Wasm AIR covers (`prep.eligible`: `checkModuleM2` since E2E M2, `checkModuleIfH` before), this
script writes the prep, exports `wasmBaseIfRegAir` for its (nloc, ngl), and runs
`nearproof-wasm-base check-tape`: the Rust trace generator builds the trace from the tape, the full
constraint and bus pre-check runs, and the trace's own final budget and HOSTB payloads are read back.
It then compares, per call, against the checker's own outcome of that call (`real`):

  * status       trace finished  <-> checker `err` is null;
  * burnt gas    preSync.burnt + preSync.remaining - g_final_trace == real.burnt
                 (`sync` burns `remaining - g`; `g_final_trace` is the trace's g_after
                 resynchronisation plus R per charged unit);
  * logs         the `log_utf8` payloads on HOSTB == real.logs;
  * return       the last `value_return` payload on HOSTB == real.ret.

Prints a summary table (also written to OUT_DIR/summary.json) and writes per-call rows to
OUT_DIR/rows.jsonl.
"""
import collections
import json
import os
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", "..", ".."))
TOOL = os.path.join(ROOT, "research/near-compression/wasm-base-lean/.lake/build/bin/wasmbase-tool")
PROVER = "/data/illia/nearproof-deps/e2e-laneA/target/release/nearproof-wasm-base"
D3TINY = "8152bed25554d521d3fcdd919f4457b66e06b720906fdd40fd6fd0723ed36bf9"


def trace_logs(t):
    """The trace's logs in order: `log_utf8` payloads as they are, `log_utf16` payloads decoded from
    UTF-16LE (the host's `String::from_utf16`) and re-encoded as UTF-8, as the outcome stores them."""
    if "logx" not in t:
        return t["logs"]
    out = []
    for hid, h in t["logx"]:
        b = bytes.fromhex(h)
        out.append(h if hid == 45 else b.decode("utf-16-le").encode("utf-8").hex())
    # E2E M3: `abort` logs `ABORT: {msg}, filename: "{file}" line: {line} col: {col}` (Host.lean)
    # from the UTF-16 strings it read (HOSTB) and its line/col arguments (the HOST row)
    if t.get("abortx"):
        m, f, line, col = t["abortx"]
        try:
            msg = bytes.fromhex(m).decode("utf-16-le")
            fil = bytes.fromhex(f).decode("utf-16-le")
            s = 'ABORT: %s, filename: "%s" line: %d col: %d' % (msg, fil, line % 2**32, col % 2**32)
            out.append(s.encode("utf-8").hex())
        except UnicodeDecodeError:
            pass
    return out


def main():
    args = sys.argv[1:]
    jobs, tool, prover, airc = 8, TOOL, PROVER, "airM2"
    for flag in ("--jobs", "--tool", "--prover", "--air"):
        if flag in args:
            i = args.index(flag)
            val = args[i + 1]
            del args[i:i + 2]
            if flag == "--jobs":
                jobs = int(val)
            elif flag == "--tool":
                tool = val
            elif flag == "--air":
                airc = val
            else:
                prover = val
    tape, out = args
    os.makedirs(os.path.join(out, "preps"), exist_ok=True)
    os.makedirs(os.path.join(out, "airs"), exist_ok=True)

    calls, verdicts, case = [], {}, None
    for ln in open(tape):
        o = json.loads(ln)
        if "case" in o:
            case = o["case"]
            if "verdict" in o:
                verdicts[case] = o["verdict"]
            continue
        o["case"] = case
        calls.append(o)

    rows = []
    by_air = collections.defaultdict(list)
    for k, c in enumerate(calls):
        r = dict(k=k, case=c["case"], seq=c["seq"], code=c["code_sha256"], method=c["method"],
                 real=c["real"], replay=c["replayMatches"])
        p = c.get("prep")
        if p is None:
            r["class"] = "no-method-run"      # preparation/loading/link/resolve outcome
        elif not p.get("eligible"):
            r["class"] = "not-eligible"        # outside checkModuleIfH (the AIR's coverage)
        else:
            r["class"] = "eligible"
            path = os.path.join(out, "preps", "%06d.json" % k)
            with open(path, "w") as f:
                json.dump(p, f)
            r["prep"] = path
            key = (len(p["localTags"]), p["ngl"])
            by_air[key].append(r)
        rows.append(r)

    def air(key):
        path = os.path.join(out, "airs", "air-%d-%d.json" % key)
        if not os.path.exists(path):
            with open(path, "w") as f:
                subprocess.run([tool, airc, str(key[0]), str(key[1])], stdout=f, check=True)
        return path

    batches = []
    for key, rs in by_air.items():
        a = air(key)
        for i in range(0, len(rs), 64):
            batches.append((a, rs[i:i + 64]))

    def run(batch):
        a, rs = batch
        res = subprocess.run([prover, "check-tape", a] + [r["prep"] for r in rs],
                             capture_output=True, text=True,
                             env=dict(os.environ, RAYON_NUM_THREADS="1"))
        got = {}
        for ln in res.stdout.splitlines():
            if ln.startswith("{"):
                o = json.loads(ln)
                got[o["prep"]] = o
        return [(r, got.get(r["prep"], dict(ok=False, err="no output: " + res.stderr[-300:]))) for r in rs]

    with ThreadPoolExecutor(jobs) as ex:
        for done in ex.map(run, batches):
            for r, t in done:
                r["trace"] = t

    for r in rows:
        if r["class"] != "eligible":
            continue
        t, real = r["trace"], r["real"]
        c = calls[r["k"]]
        if not t.get("ok"):
            # M2: a run that reaches an admitted-but-unchipped instruction (memory.grow, abort, ...)
            r["class"] = "unchipped" if "unchipped opcode" in str(t.get("err")) else "trace-failed"
            r["err"] = str(t.get("err"))[:300]
            continue
        if "burnt" not in real:
            r["class"] = "real-is-line"
            continue
        status_ok = (real["err"] is None) == (c["prep"]["status"] == "fin")
        pre = c["preSync"]
        cmp = dict(status=status_ok)
        # M2: logs are compared for aborted calls too (only successful log calls are outputs).  The
        # burnt gas of an aborted call is the host's abort accounting (`burn`, `used` vs `burnt`,
        # `GasExceeded` caps), which the Wasm trace does not carry; what the trace does claim is its
        # final budget, so an abort compares `g_final_trace` with the spec replay's final `g`
        # (`prep.gFinal`, the run the replay check ties to the chunk's result).
        burnt_eq = pre["burnt"] + pre["remaining"] - t["g_final_trace"] == real["burnt"]
        if real["err"] is None:
            cmp["burnt"] = burnt_eq
        else:
            cmp["g_final"] = t["g_final_trace"] == c["prep"]["gFinal"]
            r["burnt_formula_eq"] = burnt_eq
        cmp["logs"] = trace_logs(t) == real["logs"]
        if real["err"] is None:
            lr = t.get("lastret")
            if isinstance(real["ret"], str) and real["ret"].startswith("receipt"):
                # `promise_return(p)`: the outcome names the receipt the promise became; the Wasm
                # trace carries the promise index (the receipt numbering is the state side's, M6)
                cmp["ret"] = lr is not None and lr[0] == 30
                r["promise_ret"] = [lr[1] if lr else None, real["ret"]]
            else:
                cmp["ret"] = (t["rets"][-1] if t["rets"] else None) == real["ret"] and (lr is None or lr[0] == 50)
        r["cmp"] = cmp
        r["class"] = "equal" if all(cmp.values()) else "DIFFERENT"
        if real["err"] is not None and all(cmp.values()):
            r["class"] = "equal-abort"

    with open(os.path.join(out, "rows.jsonl"), "w") as f:
        for r in rows:
            f.write(json.dumps(r) + "\n")

    def tally(rs):
        return dict(collections.Counter(r["class"] for r in rs))

    tiny = [r for r in rows if r["code"] == D3TINY]
    summary = dict(
        cases=len(verdicts), verdicts=dict(collections.Counter(verdicts.values())),
        calls=len(rows), replay_mismatch=sum(1 for r in rows if r["replay"] is False),
        classes=tally(rows), d3tiny_calls=len(tiny), d3tiny_classes=tally(tiny),
        by_code={code: tally([r for r in rows if r["code"] == code])
                 for code in sorted(set(r["code"] for r in rows))})
    with open(os.path.join(out, "summary.json"), "w") as f:
        json.dump(summary, f, indent=1)
    print(json.dumps(summary, indent=1))


if __name__ == "__main__":
    main()
