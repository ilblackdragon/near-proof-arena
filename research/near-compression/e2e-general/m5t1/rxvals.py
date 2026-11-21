#!/usr/bin/env python3
"""Print the decoded RX row of a trace (`RX.bin`, `names.json`) as the Lean `RxVals` literal of
`M5T1/T1.lean` (the values `RxField.decode` reads: each byte group's little-endian value).

  rxvals.py DUMP_DIR NAMES_JSON [ROW]
"""
import json
import struct
import sys

FIELDS = [("lm", "lm", 1), ("la", "la", 1), ("gp", "gp", 16), ("egp", "egp", 16), ("gas", "gas", 8),
          ("dep", "dep", 16), ("amt", "amt", 16), ("lck", "lck", 16), ("vb", "vb", 8), ("vu", "vu", 8),
          ("vc", "vc", 8), ("vbal", "vbal", 16), ("vus", "vus", 8), ("vsub", "vsub", 16), ("fcx", "fcx", 8),
          ("gb", "gb", 8), ("gu", "gu", 8), ("cu", "cu", 8), ("req", "req", 16), ("burn", "burn", 16),
          ("pexec", "pexec", 8), ("tot", "tot", 8), ("gross", "gross", 8), ("unu", "unu", 16),
          ("gpb", "gpb", 16), ("sur", "sur", 16), ("bc", "bc", 16), ("rf", "rf", 16), ("tb", "tb", 16),
          ("q10", "q10", 8), ("rew", "rew", 16), ("amt2", "amt2", 16), ("txb", "txb", 16),
          ("glim", "glim", 8), ("gin", "gin", 8), ("cin", "cin", 8), ("tbin", "tbin", 16),
          ("sbin", "sbin", 16), ("wgin", "wgin", 16), ("gout", "gout", 8), ("cout", "cout", 8),
          ("tbout", "tbout", 16), ("sbout", "sbout", 16), ("wgout", "wgout", 16)]


def main():
    d, names_path = sys.argv[1], sys.argv[2]
    row = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    names = json.load(open(names_path))["RX"]
    idx = {n: i for i, n in enumerate(names)}
    b = open(f"{d}/RX.bin", "rb").read()
    log, w = struct.unpack("<II", b[:8])
    cells = struct.unpack(f"<{w}I", b[8 + 4 * w * row: 8 + 4 * w * (row + 1)])
    out = []
    for f, g, n in FIELDS:
        if n == 1:
            v = cells[idx[g]]
        else:
            v = sum(cells[idx[f"{g}.{k}"]] * 256 ** k for k in range(n))
        out.append(f"{f} := {v}")
    print("{ " + ",\n  ".join(out) + " }")


if __name__ == "__main__":
    main()
