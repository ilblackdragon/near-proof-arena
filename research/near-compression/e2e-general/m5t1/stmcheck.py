#!/usr/bin/env python3
"""F-5: lane F's `STMQ`/`STMA` traffic against lane B's state halves (B-T4).

  stmcheck.py LANEB_T1C_DIR PAIR...      (PAIR = LANEF_DUMP_DIR:LANEB_SEG, e.g. f5/se-seg-a:seg0)

Lane F's engine halves send `STMQ [r_in, tag_out, rest_out]` and receive `STMA [r_out, tag_in,
rest_in]` (Lean bus ids 17 / 18, answered on T1 by the `XTAPE` stand-in); lane B's saved state
halves (`m5tSegC`, `STC`) have the counterpart traffic on their public `htape.json` (cross-lane ids
211 / 212: the tape there plays the engine half). The join balances iff the payloads are equal and
the directions opposite. Exit 1 on any difference."""
import json
import sys

LF = {17: "STMQ", 18: "STMA"}
LB = {211: "STMQ", 212: "STMA"}


def msgs(path, ids):
    out = {}
    for b, send, m in json.load(open(path)):
        if b in ids:
            out[ids[b]] = (bool(send), list(m))
    return out


def main():
    root, pairs = sys.argv[1], sys.argv[2:]
    bad = 0
    for p in pairs:
        f, b = p.split(":")
        mf = msgs(f"{f}/xtape.json", LF)
        mb = msgs(f"{root}/{b}/htape.json", LB)
        for k in ("STMQ", "STMA"):
            # lane F's XTAPE plays lane B (it receives STMQ, sends STMA); lane B's htape plays lane F
            ok = k in mf and k in mb and mf[k][1] == mb[k][1] and mf[k][0] != mb[k][0]
            print(f"{p} {k}: {'EQUAL' if ok else 'DIFFERENT'} (tag {mf.get(k, (0, [0] * 15))[1][14]})")
            bad += not ok
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
