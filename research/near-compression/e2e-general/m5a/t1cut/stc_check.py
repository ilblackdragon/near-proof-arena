#!/usr/bin/env python3
"""B-T5: every `STC` input / output of lane B's five T1 leaves against the chain's `stRoot` at each cut.

    stc_check.py OUT [T1_INPUTS]

`OUT` holds the dumps `if`, `seg0` … `seg3` (`leaf.sh … --ifc --seg-keys --stc-meta`) or their `out/`
directories; each `htape.json` carries the `STC` stand-in's `STMQ` `[r_in, tag_out, rest_out]` and
`STMA` `[r_out, tag_in, rest_in]`. Compared with `t1-inputs.json` field `m14` (lane E's Lean-evaluated
`stOfI κ I c` per cut): `r_in` / `r_out` = the cuts' `stRoot`, the tags and the rests. The `done` close
(`c9`, finding M14-1) is the no-overlay record: `stRoot` = `bdigest ⟨3, empty root, 0, 0^32, 0, rest⟩`,
recomputed here from the record's parts as well.
"""
import hashlib
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..', 't1'))
sys.path.insert(0, os.path.join(HERE, '..'))
import chain  # noqa: E402
import stc as STC  # noqa: E402

PAIRS = {'if': ('c1', 'c9'), 'seg0': ('c1', 'c2'), 'seg1': ('c2', 'c7'), 'seg2': ('c7', 'c8'), 'seg3': ('c8', 'c9')}


def check(out, inputs):
    cuts = json.load(open(inputs))['m14']['cuts']
    rows, ok = [], True
    for d, (a, b) in PAIRS.items():
        p = os.path.join(out, d)
        m = chain.stc_msgs(p if os.path.exists(os.path.join(p, 'htape.json')) else os.path.join(p, 'out'))
        r = {'dump': d, 'cut_in': a, 'cut_out': b,
             'r_in': m['r_in'].hex() == cuts[a]['stRoot'], 'r_out': m['r_out'].hex() == cuts[b]['stRoot'],
             'tags': (m['tag_in'], m['tag_out']) == (int(cuts[a]['tag']), int(cuts[b]['tag'])),
             'rests': m['rest_in'].hex() == cuts[a]['rest'] and m['rest_out'].hex() == cuts[b]['rest'],
             'st_in': m['r_in'].hex(), 'st_out': m['r_out'].hex(), 'tag_in': m['tag_in'], 'tag_out': m['tag_out']}
        ok &= r['r_in'] and r['r_out'] and r['tags'] and r['rests']
        rows.append(r)
    c9 = cuts['c9']
    done = STC.bdigest(STC.ser(3, STC.EMPTY, 0, bytes(32), int(c9['idx']), bytes.fromhex(c9['rest']))).hex()
    ok &= done == c9['stRoot'] and STC.EMPTY.hex() == c9['ws_root']
    return ok, rows, done


def main():
    out = sys.argv[1]
    inputs = sys.argv[2] if len(sys.argv) > 2 else os.path.join(HERE, '..', '..', 't1', 'data', 't1-inputs.json')
    ok, rows, done = check(out, inputs)
    for r in rows:
        print(f"{r['dump']:5} {r['cut_in']} -> {r['cut_out']}: r_in {r['st_in'][:16]}… {'=' if r['r_in'] else '!='} "
              f"{r['cut_in']}.stRoot, r_out {r['st_out'][:16]}… {'=' if r['r_out'] else '!='} {r['cut_out']}.stRoot, "
              f"tags {r['tag_in']} -> {r['tag_out']} {'OK' if r['tags'] else 'BAD'}, rests {'OK' if r['rests'] else 'BAD'}")
    print(f"c9 = bdigest <3, empty root, 0, 0^32, 0, rest> = {done[:16]}… (recomputed)")
    print('STC vs chain (m14):', 'OK' if ok else 'MISMATCH')
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
