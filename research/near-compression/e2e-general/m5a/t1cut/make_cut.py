#!/usr/bin/env python3
"""B-T4: T1's STATE cut at the `rt` boundaries (lane I's chain `c1 … c9`).

    make_cut.py STATE_JSON [T1_INPUTS]

Writes `seg-keys.json` (tracegen `--seg-keys`) and `stc-meta.json` (`--stc-meta`) next to this file:

* seg0 = STATE seg A (`c1 → c2`): the 8 changes committed before receipt 1's step (lane F's Lean
  run, `acc.before.committed` of `t1/data/t1-inputs.json`);
* seg1 = the state half of RT resume (`c6 → c7`): the 2 changes receipt 1 commits (contract data
  `t`, the receiver's account);
* seg2 = STATE seg B (`c7 → c8`): no change (`R_out = R_in = R_n`);
* seg3 = the finalize leaf's state half (`c8 → c9`): no change, tag 1 → 3 (`done`);
* `if` (`--ifc`): the IF's own `STC` row, input = `c1`'s commitment (tag 1, `R_0`), output = `c9`'s
  (tag 3, `R_n`).

Every `rest` is `0^42`: lane I's chain placeholder (`chain.PLACEHOLDERS`; `encRestI` is not
adopted, lane F's engine rows own the `rest` preimage).
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
st = json.load(open(sys.argv[1]))
inp = json.load(open(sys.argv[2] if len(sys.argv) > 2 else os.path.join(HERE, '..', '..', 't1', 'data', 't1-inputs.json')))
before = dict(map(tuple, inp['acc']['before']['committed']))
after = dict(map(tuple, inp['acc']['after']['committed']))
chg = dict((k, v) for k, v in st['changes'])
assert set(chg) == set(after) and all(chg[k] == after[k] for k in after), 'the overlay after receipt 1 = the changes'
assert set(before) <= set(after) and all(after[k] == before[k] for k in before), 'receipt 1 does not rewrite receipt 0'
segs = [sorted(before), sorted(set(after) - set(before)), [], []]
json.dump(segs, open(os.path.join(HERE, 'seg-keys.json'), 'w'), indent=1)
Z = '00' * 42
meta = {n: dict(tag_in=1, tag_out=t, rest_in=Z, rest_out=Z)
        for n, t in (('if', 3), ('seg0', 1), ('seg1', 1), ('seg2', 1), ('seg3', 3))}
json.dump(meta, open(os.path.join(HERE, 'stc-meta.json'), 'w'), indent=1)
print('segments:', [len(s) for s in segs])
