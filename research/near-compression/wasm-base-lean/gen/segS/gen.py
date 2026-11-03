#!/usr/bin/env python3
"""Generate WasmBase/Main/SegS/*.lean: HoldsXS copies of the seg_sound chain (E2E M4c, sub-lane MP).

Usage (from research/near-compression/wasm-base-lean, after building WasmBase.Main.SegSoundX):
  lake env lean gen/segS/deps.lean > /tmp/deps.txt     # chain declarations + source ranges
  python3 gen/segS/gen.py $PWD /tmp/deps.txt
Every declaration reachable from `seg_sound` whose type mentions `HoldsX` is copied (with its section
variables) into WasmBase/Main/SegS/<Module>.lean, `HoldsX (wasmBaseSegAir …)` -> `HoldsXS …`,
`ChipIf … (wasmBaseSegAir …) …` -> `SegSha.ChipIfS …`, chain names `foo` -> `fooS`; `prelude/<Module>.lean`
is inserted at the top of the module and `patches.py` holds the hand fixes (the t ≠ 20 / OkBus side
conditions the copies need).  The generated files are committed; rerun only if the originals change.
"""
import re, sys, os

ROOT = sys.argv[1]  # wasm-base-lean dir
DEPS = sys.argv[2]
ORDER = ["SegRows", "SegMemb", "SegSend", "SegCuto", "SegLink", "SegSha", "SegShaBytes", "SegShaCut",
         "SegCutWords", "SegSound", "SegBus", "SegRowsX", "SegRegKeep", "SegSoundX"]
EXCLUDE = {"WasmBase.SegSha.seg_if_bits", "WasmBase.SegSha.seg_if_send_zero", "WasmBase.SegSha.if_recv_mem"}
PRELUDE = {}
pre_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "prelude")
for m in ORDER:
    f = os.path.join(pre_dir, m + ".lean")
    if os.path.exists(f):
        PRELUDE[m] = open(f).read()

decls = {}  # module -> list of (full, short, a, b)
for line in open(DEPS):
    if not (line.startswith("DEP ") or line.startswith("EXTRA ")):
        continue
    _, mod, full, H, A, a, b = line.split()
    if H != "H=true" or "._" in full or mod == "WasmBase.Main.SegHoldsX":
        continue
    if full in EXCLUDE:
        continue
    m = mod.split(".")[-1]
    decls.setdefault(m, []).append((full, int(a), int(b)))

names = {}  # short (possibly SegSha.x) -> new
allnames = set()
for m, ds in decls.items():
    for full, a, b in ds:
        allnames.add(full)
for full in sorted(allnames) + sorted(EXCLUDE):
    short = full[len("WasmBase."):]
    base = short.split(".")[-1]
    stripped = base.rstrip("'")
    primes = base[len(stripped):]
    names[base] = stripped + "S" + primes

GENERIC = {"table_constrX": "table_constrXS", "table_constr_eqX": "table_constr_eqXS",
           "busNat_ltX": "busNat_ltXS", "lookup_soundX": "lookup_soundXS", "perm_exactX": "perm_exactXS",
           "msgs_permX": "msgs_permXS", "range16_valuesX": "range16_valuesXS",
           "regG_r16_recvX": "regG_r16_recvXS", "lookup_r16GX": "lookup_r16GXS"}


def transform(s):
    s = re.sub(r"HoldsX \(wasmBaseSegAir (\S+) (\S+)\) (\S+) (\S+?)\)", r"HoldsXS \1 \2 \3 \4)", s)
    s = re.sub(r"HoldsX \(wasmBaseSegAir (\S+) (\S+)\) (\S+) (\S+)", r"HoldsXS \1 \2 \3 \4", s)
    s = re.sub(r"(?:SegSha\.)?ChipIf (\S+) \(wasmBaseSegAir (\S+) (\S+)\) (\S+) (\S+) (\S+?)\)",
               r"SegSha.ChipIfS \1 \2 \3 \4 \5 \6)", s)
    s = re.sub(r"(?:SegSha\.)?ChipIf (\S+) \(wasmBaseSegAir (\S+) (\S+)\) (\S+) (\S+) (\S+)",
               r"SegSha.ChipIfS \1 \2 \3 \4 \5 \6", s)
    s = s.replace("H.toC", "H")
    allmap = dict(names)
    allmap.update(GENERIC)
    keys = sorted(allmap, key=len, reverse=True)
    pat = re.compile(r"(?<![A-Za-z0-9_'.])((?:SegSha\.)?)(" + "|".join(re.escape(k) for k in keys) + r")(?![A-Za-z0-9_'])")
    s = pat.sub(lambda mm: mm.group(1) + allmap[mm.group(2)], s)
    for (mo, old, new) in PATCHES:
        if mo == CURMOD[0] and old in s:
            s = s.replace(old, new)
            USED.add((mo, old))
    return s


PATCHES = []
USED = set()
CURMOD = [None]
pf = os.path.join(os.path.dirname(os.path.abspath(__file__)), "patches.py")
if os.path.exists(pf):
    exec(open(pf).read())

prev = None
outdir = os.path.join(ROOT, "WasmBase/Main/SegS")
os.makedirs(outdir, exist_ok=True)
for m in ORDER:
    CURMOD[0] = m
    src = open(os.path.join(ROOT, f"WasmBase/Main/{m}.lean")).read().split("\n")
    ds = sorted(decls.get(m, []), key=lambda x: x[1])
    # section contexts per line
    stack = []  # list of [kind, name, ctxlines]
    ctx_at = {}
    opens, opts = [], []
    i = 0
    n = len(src)
    while i < n:
        L = src[i]
        mm = re.match(r"^(section|namespace)\b\s*(\S*)", L)
        if mm:
            stack.append([mm.group(1), mm.group(2), []])
        elif re.match(r"^end\b", L):
            if stack:
                stack.pop()
        elif re.match(r"^(variable|include|omit)\b", L) and not L.rstrip().endswith(" in"):
            blk = [L]
            while i + 1 < n and src[i + 1].startswith(" "):
                i += 1
                blk.append(src[i])
            if stack:
                stack[-1][2].append("\n".join(blk))
        elif re.match(r"^open\b", L):
            opens.append(L)
        elif re.match(r"^set_option\b", L) and not L.rstrip().endswith(" in"):
            if stack and len(stack) == 1:
                opts.append(L)
        ctx_at[i + 1] = tuple(c for fr in stack if fr[0] == "section" for c in fr[2])
        i += 1
    out = []
    out.append(f"import WasmBase.Main.{m}")
    if prev:
        out.append(f"import WasmBase.Main.SegS.{prev}")
    else:
        out.append("import WasmBase.Main.SegHoldsS")
    out.append(f"/-!\n# WasmBase.Main.SegS.{m} — `{m}`'s `seg_sound` chain from `HoldsXS` (E2E M4c, MP)\n\n"
               f"Copies of the declarations of `Main/{m}.lean` that `seg_sound` uses, with "
               "`HoldsX (wasmBaseSegAir …)` replaced by `HoldsXS` (no table 20, no buses 15/16/17/103; "
               "`Main/SegHoldsS.lean`) and every chain name `foo` renamed `fooS`.  Proofs are the originals', "
               "with the side conditions `t ≠ 20` / `OkBus b` added.\n-/")
    out.append("namespace WasmBase\n")
    for o in dict.fromkeys(opens):
        out.append(o)
    for o in dict.fromkeys(opts):
        out.append(o)
    out.append("")
    if m in PRELUDE:
        out.append(PRELUDE[m])
    cur_ctx = None
    cur_ns = None
    for full, a, b in ds:
        ns = "SegSha" if full.startswith("WasmBase.SegSha.") else None
        ctx = ctx_at.get(a, ())
        if ctx != cur_ctx or ns != cur_ns:
            if cur_ctx is not None and cur_ctx:
                out.append("end\n")
            if cur_ns != ns:
                if cur_ns:
                    out.append(f"end {cur_ns}\n")
                if ns:
                    out.append(f"namespace {ns}\n")
            if ctx:
                out.append("section")
                out.extend(transform(c) for c in ctx)
                out.append("")
            cur_ctx, cur_ns = ctx, ns
        k = a - 1
        while k - 1 >= 0 and re.match(r"^(include|omit|set_option)\b.* in\s*$", src[k - 1]):
            k -= 1
        text = "\n".join(src[k:b])
        out.append(transform(text))
        out.append("")
    if cur_ctx:
        out.append("end\n")
    if cur_ns:
        out.append(f"end {cur_ns}\n")
    out.append("end WasmBase\n")
    open(os.path.join(outdir, f"{m}.lean"), "w").write("\n".join(out))
    prev = m
for (mo, old, new) in PATCHES:
    if (mo, old) not in USED:
        print("UNUSED PATCH", mo, old[:60])
print("ok", {m: len(v) for m, v in decls.items()})
