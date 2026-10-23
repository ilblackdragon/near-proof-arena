#!/usr/bin/env python3
"""A deliberately WRONG checker, used only as a negative control for the difftests.

It reads case directories on argv and prints one JSON verdict line per case, always `accept`
(D3-shaped) or always `true` (D1/D2-shaped), without reading the case at all. Any difftest pointed at
it must therefore report disagreements and exit nonzero; if one exits 0 while using this, that
difftest is not comparing.

This file exists so the negative control is a committed artifact instead of an ad-hoc `/tmp` script
that disappears. It is not used by `l7_verify_all.sh`; invoke it explicitly, e.g.

    D3_CHECK=oracle/wasm-d3/tests/wrongchecker.py python3 oracle/v3-d3/tools/difftest_d3.py \
        /data/illia/nearproof-deps/corpora/d3c9 --sample 60 --shards 4

    python3 oracle/tools/difftest_v3_d1.py --cases /data/illia/nearproof-deps/corpora/d1run \
        --lean oracle/wasm-d3/tests/wrongchecker.py \
        --python oracle/tools/spec_check_v3_d1.py --jobs 12 --report /tmp/neg-d1.json

Mode is chosen by `--mode d3|bool`, defaulting to `d3` (prints `{"case":…,"verdict":"accept"}`).
"""
import json
import os
import sys


def main():
    mode = "d3"
    args = sys.argv[1:]
    if "--mode" in args:
        i = args.index("--mode")
        mode = args[i + 1]
        del args[i:i + 2]
    for d in args:
        d = d.rstrip("/")
        if not os.path.isdir(d):
            continue
        if mode == "bool":
            print(json.dumps({"case": d, "accept": True}))
        else:
            print(json.dumps({"case": d, "verdict": "accept", "reason": ""}))
    return 0


if __name__ == "__main__":
    sys.exit(main())
