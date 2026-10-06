"""Black-box host-function probe helper (harness `full` mode)."""
import json, os, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "../../../tests"))
from wasmenc import *
H = "/data/illia/nearproof-deps/target-wasm-d3/release/near-wasm-d3-harness"
IMPL = os.path.join(HERE, "../../nearwasm.py")
GAS = 300 * 10**12
U64MAX = 2**64 - 1
INV = json.load(open(os.path.join(HERE, "../../../../../docs/research/near-wasm-boundary-inventory.json")))
SIG = {}
for i in INV["imports"]:
    if i["module"] == "env":
        SIG[i["name"]] = ([{"u64": I64, "u32": I32}[a.split(":")[1].strip()] for a in i["args"].split(",") if a.strip()],
                          [{"u64": I64, "u32": I32}[x.strip()] for x in i["returns"].split(",") if x.strip()])

class P:
    def __init__(self, data=b"", opts="rcv=", gas=GAS):
        self.m = Module()
        self.m.vr = self.m.import_func("env", "value_return", [I64, I64], [])
        self.imp = {"value_return": self.m.vr}
        self.m.memory = (1, None)
        if data:
            self.m.datas.append(b"\x00" + i32c(0) + b"\x0b" + vec([bytes([x]) for x in data]))
        self.body = bytearray()
        self.opts = opts
        self.gas = gas
        self.slot = 0

    def call(self, name, *args, keep=False, store=True):
        ps, rs = SIG[name]
        if name not in self.imp:
            self.imp[name] = self.m.import_func("env", name, ps, rs)
        if rs and store and not keep:
            self.body += i32c(60000 + 8 * self.slot)
        for v, t in zip(args, ps):
            self.body += i64c(v) if t == I64 else i32c(v)
        self.body += b"\x10" + uleb(self.imp[name])
        if rs and not keep:
            if store:
                self.body += b"\x37\x03\x00" if rs[0] == I64 else b"\x36\x02\x00"
                self.slot += 1
            else:
                self.body += b"\x1a"
        return self

    def raw(self, b):
        self.body += b
        return self

    def done(self, ret=None):
        if ret is None:
            ret = (60000, 8 * self.slot)
        if ret is not False:
            self.body += i64c(ret[1]) + i64c(ret[0]) + b"\x10" + uleb(self.m.vr)
        self.m.func([], [], [], bytes(self.body))
        self.m.exports.append(("main", 0, len(self.m.imports)))
        return f"{self.gas} {self.m.encode().hex()} {self.opts}"

def near(lines, mode="full"):
    return subprocess.run([H, mode], input="\n".join(lines) + "\n", capture_output=True, text=True, check=True).stdout.splitlines()

def mine(lines):
    return subprocess.run([sys.executable, IMPL, "--full"], input="\n".join(lines) + "\n", capture_output=True, text=True).stdout.splitlines()

def show(cases, w=600):
    out = near([c for _, c in cases])
    for (l, _), o in zip(cases, out):
        print(f"{l:30s} {o[:w]}")

def cmp(cases, w=400):
    a = near([c for _, c in cases]); b = mine([c for _, c in cases])
    nd = 0
    for (l, _), x, y in zip(cases, a, b):
        if x != y: nd += 1
        print(("same " if x == y else "DIFF ") + f"{l:30s} near: {x[:w]}" + ("" if x == y else f"\n     {'':30s} mine: {y[:w]}"))
    print("diffs", nd)
