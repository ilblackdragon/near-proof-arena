#!/usr/bin/env python3
"""Hand-encode wasm modules shaped like the fuel-stress contract (fuelc.wat)."""
import os

def leb(n):
    out = bytearray()
    while True:
        b = n & 0x7f
        n >>= 7
        if n:
            out.append(b | 0x80)
        else:
            out.append(b)
            return bytes(out)

def vec(items):
    return leb(len(items)) + b"".join(items)

def section(sid, payload):
    return bytes([sid]) + leb(len(payload)) + payload

END, BLOCK, LOOP, BR, NOP = b"\x0b", b"\x02\x40", b"\x03\x40", b"\x0c", b"\x01"

def mod(bodies, exports):
    secs = []
    secs.append(section(1, vec([b"\x60\x00\x00"])))            # one type ()->()
    secs.append(section(3, vec([leb(0)] * len(bodies))))       # all funcs type 0
    secs.append(section(5, vec([b"\x00\x01"])))                # memory min 1
    exps = [leb(len(n)) + n.encode() + b"\x00" + leb(i) for n, i in exports]
    secs.append(section(7, vec(exps)))
    code = [leb(len(b)) + b for b in bodies]
    secs.append(section(10, vec(code)))
    return b"\x00asm\x01\x00\x00\x00" + b"".join(secs)

def body0(code):
    """0 local decls + code + function END (code itself must be structurally balanced)."""
    return leb(0) + code + END

def blocks(n):
    # (loop $l (block)(block)...(block) br $l)  -- the blocks4999 shape
    code = LOOP + (BLOCK + END) * n + BR + b"\x00" + END   # last END closes the loop
    return mod([body0(code)], [("run", 0)])

def spin():
    code = LOOP + BR + b"\x00" + END
    return mod([body0(code)], [("run", 0)])

def nops():
    code = LOOP + NOP * 8 + BR + b"\x00" + END
    return mod([body0(code)], [("run", 0)])

def deep(n):
    # (loop $l (block)^n (br n)) -- push-heavy: arc must push n-1 labels in one step
    code = LOOP + BLOCK * n + BR + leb(n) + END * (n + 1)   # n blocks + the loop
    return mod([body0(code)], [("run", 0)])

def mixed(iters=1000000):
    # helper fn0: 3 block/end pairs (arc on call entry)
    helper = body0((BLOCK + END) * 3)
    # main fn1: counter loop with locals, an if/else, block/end pairs and a call
    main_code = (
        LOOP +
        b"\x20\x00" +                        # local.get 0
        b"\x41\x01" + b"\x6a" +               # i32.const 1; i32.add
        b"\x21\x00" +                         # local.set 0
        (BLOCK + END) * 2 +                   # label-neutral arc inside the loop
        b"\x41\x00" +                         # i32.const 0 (if condition)
        b"\x04\x40" + b"\x01" + b"\x05" + b"\x01" + END +   # if void (nop else nop end)
        b"\x10\x00" +                          # call 0 (helper)
        b"\x20\x00" +                          # local.get 0
        b"\x41" + leb(iters) +                 # i32.const iters
        b"\x49" +                              # i32.lt_u
        b"\x0d\x00" +                          # br_if 0
        END +                                  # closes the loop
        b"\x41\x00" + b"\x20\x00" + b"\x36\x00\x00"          # i32.store mem[0] := i
    )
    main = leb(1) + leb(1) + b"\x7f" + main_code + END        # 1 local of type i32
    return mod([helper, main], [("run", 1)])

CONST0_DROP = b"\x41\x00\x1a"   # i32.const 0; drop (a charged group inside the loop)

def pushpop(n):
    # (loop (block)^n i32.const 0 drop (end)^n br 0): one run pushes n labels, a charged group,
    # then a run that pops them as entry labels -- the arcs' O(n)-per-iteration shape
    code = LOOP + BLOCK * n + CONST0_DROP + END * n + BR + b"\x00" + END
    return mod([body0(code)], [("run", 0)])

def brif(n):
    # (loop (block)^n i32.const 1 br_if n (end)^n): the back-edge is a taken br_if (not fused)
    code = LOOP + BLOCK * n + b"\x41\x01" + b"\x0d" + leb(n) + END * n + END
    return mod([body0(code)], [("run", 0)])

def midrun(n):
    # (loop (block i32.const 1 br_if 0) (block)(block)... br 0): the br_if lands mid-run
    code = LOOP + BLOCK + b"\x41\x01" + b"\x0d\x00" + END + (BLOCK + END) * n + BR + b"\x00" + END
    return mod([body0(code)], [("run", 0)])

def memoctl(depth=20):
    # breakage control for the label memo (ArcProbeBroken.lean): g() = block(i32) [block]^depth
    # i32.const 7 br depth end^depth end; run() checks call g + 100 + call g == 114, else traps.
    # The second call of g runs at value-stack height 2, so its `br` labels differ in their heights.
    g = leb(0) + b"\x02\x7f" + BLOCK * depth + b"\x41\x07" + BR + leb(depth) + END * depth + b"\x00" + END + END
    run = leb(0) + (b"\x10\x00" + b"\x41\xe4\x00" + b"\x10\x00" + b"\x6a\x6a"
                    + b"\x41\xf2\x00" + b"\x47" + b"\x04\x40\x00\x0b") + END
    secs = []
    secs.append(section(1, vec([b"\x60\x00\x01\x7f", b"\x60\x00\x00"])))
    secs.append(section(3, vec([leb(0), leb(1)])))
    secs.append(section(5, vec([b"\x00\x01"])))
    secs.append(section(7, vec([leb(3) + b"run" + b"\x00" + leb(1)])))
    secs.append(section(10, vec([leb(len(b)) + b for b in [g, run]])))
    return b"\x00asm\x01\x00\x00\x00" + b"".join(secs)

if __name__ == "__main__":
    import sys
    out = sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(os.path.abspath(__file__)), "mods")
    os.makedirs(out, exist_ok=True)
    for name, b in [
        ("b4999.wasm", blocks(4999)),
        ("b500.wasm", blocks(500)),
        ("b5.wasm", blocks(5)),
        ("spin.wasm", spin()),
        ("nops.wasm", nops()),
        ("deep200.wasm", deep(200)),
        ("mixed.wasm", mixed()),
        ("deep4999.wasm", deep(4999)),
        ("pushpop4999.wasm", pushpop(4999)),
        ("brif4999.wasm", brif(4999)),
        ("midrun4998.wasm", midrun(4998)),
        ("memoctl.wasm", memoctl()),
    ]:
        with open(os.path.join(out, name), "wb") as f:
            f.write(b)
        print(name, len(b), "bytes")
