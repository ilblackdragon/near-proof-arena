"""Black-box probe helper: build modules with ../../tests/wasmenc.py and run them through the nearcore harness."""
import os, subprocess, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../tests"))
from wasmenc import *
H = "/data/illia/nearproof-deps/target-wasm-d3/release/near-wasm-d3-harness"
def near(lines, mode=None):
    return subprocess.run([H] + ([mode] if mode else []), input="\n".join(lines) + "\n", capture_output=True, text=True, check=True).stdout.splitlines()
def show(cases, mode=None):
    out = near([c for _, c in cases], mode)
    for (l, _), o in zip(cases, out):
        print(f"{l:40s} {o[:200]}")
IMPL = os.path.join(os.path.dirname(os.path.abspath(__file__)), "../nearwasm.py")
def mine(lines):
    return subprocess.run([sys.executable, IMPL], input="\n".join(lines) + "\n", capture_output=True, text=True, check=True).stdout.splitlines()
def cmp(cases):
    a = near([c for _, c in cases]); b = mine([c for _, c in cases])
    for (l, _), x, y in zip(cases, a, b):
        tag = "same" if x == y else "DIFF"
        print(f"{tag} {l:42s} near: {x[:150]}" + ("" if x == y else f"\n     {'':42s} mine: {y[:150]}"))
