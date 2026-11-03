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
  bvnref two changes below a branch with a value (the kept value of a version-published branch, M5a-6)
  squashx deletes squashing onto extension / branch siblings (a fixture for the open gap; tracegen
         reports it Unsupported)
  longkey keys of 1–2 KiB (M5a-8: the u32 hex-prefix length past 255; leaf / extension keys of up to
         ~4,200 nibbles, continued over ~65 `SNC` chunks): a long leaf replaced (`SN.oLR`), split
         near its head (`oLX`), deleted (`oLD`), a long extension descended (`oEU`), finds
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
    # M5a-6: two changes below the branch holding `alice`'s value: the first rewrite of that branch
    # keeps the value and is published under a version id (`nref`), the second reads it from `VER`
    'bvnref': dict(
        pre=['alice', 'alice.near', 'alice.x', 'bob', 'bob.near', 'carl1', 'carl2'],
        changes=[('alice.near', 'alice.near-2'), ('alice.x', 'alice.x-2')],
        reads=['alice']),
    # M5a-8 item 4 (open; tracegen stops with `Unsupported: squash onto a ext sibling`): deletes
    # squashing onto a non-leaf sibling (`squashBranch` → `extendChild [i] c`, `c` an extension / a
    # branch), under a branch parent and under an extension parent that merges; a branch-value
    # delete leaving one extension child.  The spec oracle (`m5a-tool apply`) agrees with ptrie.py.
    'squashx': dict(
        pre=['cab', 'caxy1', 'caxy2', 'dab', 'daxy1', 'daxy2', 'dz', 'eab', 'ep1', 'eq1', 'ez',
             'gab', 'gaxy1', 'gaxy2', 'gb', 'hh', 'hhxy1', 'hhxy2', 'hz'],
        changes=[('cab', None), ('dab', None), ('eab', None), ('gab', None), ('hh', None)],
        reads=['caxy1', 'gb']),
    # M5a-8: keys of 1-2 KiB (`acct` + a long suffix; NEAR's storage keys go up to 2 KiB)
    'longkey': dict(
        pre=['alice,' + 'A' * 1100, 'alice,' + 'B' * 1100, 'bob,' + 'x' * 1000 + 'a',
             'bob,' + 'x' * 1000 + 'b', 'carl,' + 'Q' * 2040, 'dave', 'erin,' + 'E' * 1200,
             'erin,' + 'F' * 1200],
        changes=[('alice,' + 'A' * 1100, 'alice-2'), ('alice,' + 'AC' + 'C' * 1098, 'alice-3'),
                 ('bob,' + 'x' * 1000 + 'a', 'bob-2'), ('erin,' + 'E' * 1200, None),
                 ('carl,' + 'Q' * 2040, 'carl-2'), ('dave', 'dave-2')],
        reads=['bob,' + 'x' * 1000 + 'b', 'carl,' + 'Q' * 2040]),
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
