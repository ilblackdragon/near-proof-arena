#!/usr/bin/env python3
"""Extract every FunctionCall VM invocation of a corpus chunk, as the independent clean-room
checker (`oracle/tools/spec_check_v3_d3.py`) executes it while validating the whole chunk.

    extract_calls.py CASE_DIR [--code-dir DIR]

Prints one JSON object: the chunk verdict and, per VM call in execution order, the code hash
(sha256 of the code bytes), method, prepaid gas, input bytes (hex), and the VM outcome the chunk
validation used (aborted, burnt, used, logs, return value, gas profile).  With `--code-dir`, every
executed code blob is written there as `<sha256>.wasm`.

Nothing is changed in the checker: `run_vm` is wrapped, its arguments and result recorded, and its
result returned unchanged.  This is milestone-1 input selection (docs/zk-formal/E2E-GENERAL-CHUNK-PLAN.md
§5): it fixes, from the chunk itself, the call whose execution the Wasm AIR must prove.
"""
import hashlib
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "oracle", "tools"))

import spec_check_v3_d3 as D3  # noqa: E402

CALLS = []
_orig = D3.run_vm


def _hexs(b):
    return None if b is None else bytes(b).hex()


def _loading_fee(prepaid, cap, n):
    """The contract-loading ext cost `run_vm` charges before instantiation (same counter calls)."""
    gc = D3.CappedGas(prepaid, cap)
    try:
        gc.pay_per(D3.W.LOAD_BYTES, n)
        gc.pay_base(D3.W.LOAD_BASE)
    except D3.W.HostErr:
        return None
    return gc.burnt


def _wrapped(prep, code, method, prepaid, cap, ctx, ext, store, storage_usage):
    rec = dict(code_sha256=hashlib.sha256(bytes(code)).hexdigest(), code_len=len(code), method=method,
               prepaid=prepaid, input=_hexs(ctx.input), account=str(D3.W.CURRENT_ACCOUNT),
               storage_usage_in=storage_usage)
    try:
        out = _orig(prep, code, method, prepaid, cap, ctx, ext, store, storage_usage)
    except BaseException as e:
        rec["raised"] = "%s: %s" % (type(e).__name__, e)
        CALLS.append(rec)
        raise
    rec.update(aborted=out.get("aborted"), burnt=out.get("burnt"), used=out.get("used"),
               loading_fee=_loading_fee(prepaid, cap, len(code)),
               logs=[_hexs(x) if isinstance(x, (bytes, bytearray)) else x for x in out.get("logs", [])],
               ret=_hexs(out.get("ret")) if isinstance(out.get("ret"), (bytes, bytearray)) else out.get("ret"),
               storage_usage_out=out.get("storage_usage"))
    CALLS.append(rec)
    if CODE_DIR:
        p = os.path.join(CODE_DIR, rec["code_sha256"] + ".wasm")
        if not os.path.exists(p):
            with open(p, "wb") as f:
                f.write(bytes(code))
    return out


D3.run_vm = _wrapped
CODE_DIR = None


def main():
    global CODE_DIR
    sys.setrecursionlimit(100000)
    args = sys.argv[1:]
    if "--code-dir" in args:
        i = args.index("--code-dir")
        CODE_DIR = args[i + 1]
        os.makedirs(CODE_DIR, exist_ok=True)
        del args[i:i + 2]
    (case,) = args
    verdict, reason = D3.check_case(case)
    print(json.dumps(dict(case=case, verdict=verdict, reason=reason, calls=CALLS), indent=1, default=str))


if __name__ == "__main__":
    main()
