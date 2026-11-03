#!/usr/bin/env python3
"""Synthetic state-access cases for the menu's completeness gaps (M5a-2).

  synth.py NAME OUT_STATE_JSON

Builds a pre-state trie from a key set (`ptrie.apply_changes` from the empty trie), picks the
changes of case NAME, and writes a state file in `extract_state.py`'s format (`nodes_read` = every
node of the pre-state trie, `keys_read` = the changed keys, `post_root` from the transcription).
The root is then checked against the Lean spec by `m5a-tool apply` (run.sh does it) — the spec is
the oracle, the transcription only proposes.

Cases (NEAR-shaped keys: `0x00 ‖ account id`, so `alice` is a prefix of `alice.near`):
  bval   upsert at a branch value (over a value and a new one: `BR.oUV`), delete of a branch value
         keeping the branch (`BR.oDV`), an absent delete at a branch without value (`BR.oDZ`), finds
         ending at a branch value (`BR.oFV`)
"""
import hashlib
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import ptrie as PT  # noqa: E402


def sha(b):
    return hashlib.sha256(b).digest()


def acct(name):
    return b'\x00' + name.encode()


def val(tag):
    return sha(tag.encode()) + tag.encode()


CASES = {
    'bval': dict(
        pre=['alice', 'alice.near', 'alice.x', 'bob', 'bob.near', 'bobz', 'carl1', 'carl2', 'carla',
             'dave.near', 'dave.w', 'erin', 'frank', 'frank.a', 'frank.b', 'gina1', 'gina2', 'ginaz'],
        # oUV over a value, oDV (two children kept), oDZ (no value), an absent delete inside an
        # extension, oUV over a value with one child, oUV of a new value, a leaf replace
        changes=[('alice', 'alice-2'), ('bob', None), ('carl', None), ('dave', None), ('frank', 'frank-2'),
                 ('gina', 'gina-2'), ('erin', 'erin-2')],
        reads=['dave', 'bob.near']),
}


def nodes(t, out):
    if t is None or t[0] == 'hash':
        return
    out.append(PT.serialize(t).hex())
    if t[0] == 'ext':
        nodes(t[2], out)
    elif t[0] == 'branch':
        for c in t[2]:
            nodes(c, out)


def main():
    name, out = sys.argv[1], sys.argv[2]
    case = CASES[name]
    pre = [(acct(a), val(a)) for a in case['pre']]
    t0, _ = PT.apply_changes(None, [(k, (len(v), sha(v))) for k, v in pre])
    chg = [(acct(a), None if v is None else val(v)) for a, v in case['changes']]
    chg.sort()
    t1, ops = PT.apply_changes(t0, [(k, None if v is None else (len(v), sha(v))) for k, v in chg])
    ns = []
    nodes(t0, ns)
    st = dict(case='synthetic:' + name, pre_root=PT.root_hash(t0).hex(), post_root=PT.root_hash(t1).hex(),
              nodes_read=ns, keys_read=sorted(set(k.hex() for k, _ in chg) | set(acct(a).hex() for a in case['reads'])),
              changes=[[k.hex(), None if v is None else v.hex()] for k, v in chg], transcription_ops=ops)
    json.dump(st, open(out, 'w'), indent=1)
    print(json.dumps(dict(pre_root=st['pre_root'], post_root=st['post_root'], ops=ops)))


if __name__ == '__main__':
    main()
