#!/usr/bin/env python3
"""M5a: extract a chunk's state-access set from the independent clean-room checker
(`oracle/tools/spec_check_v3_d3.py`) and cross-check it against the Lean `allFeatures` run's
write log (`nearspec-v3-check-successor --tier allFeatures --emit-full`, `stateChanges`).

  extract_state.py CASE_DIR LEAN_EMIT_FULL_JSON OUT_JSON

Output JSON (the main transition):
  pre_root      prev_state_root of the main transition (hex)
  post_root     the main transition's post_state_root (hex)
  header_state_root  the Lean run's computed state root (equals the header's prev_state_root,
                verdict accept); equal to post_root iff the chunk has no implicit transitions
  nodes_read    trie nodes the checker read (hex bytes, in first-read order)
  keys_read     keys looked up (hex) -> pre-value ref [len, sha256 hex] or null (absent)
  changes       the committed overlay at finalize, ascending raw key: [key, value hex | null]
  lean_changes  the Lean run's committed overlay ([key, len, valueHash] | [key, null, null])
"""
import hashlib
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "../../../.."))
sys.path.insert(0, os.path.join(ROOT, "oracle/tools"))
sys.setrecursionlimit(100000)
import spec_check_v3_d3 as D3  # noqa: E402
from v3lib.trie2 import Trie2  # noqa: E402

LOG = dict(transitions=[])


def main():
    case, lean_json, out = sys.argv[1], sys.argv[2], sys.argv[3]
    orig_node, orig_get, orig_getref, orig_update = Trie2.node, Trie2.get, Trie2.get_ref, Trie2.update
    cur = {}

    def track(self):
        if id(self) not in cur:
            t = dict(pre_root=self.root.hex(), nodes=[], seen=set(), keys={})
            cur[id(self)] = t
            LOG['transitions'].append(t)
        return cur[id(self)]

    def node(self, h):
        t = track(self)
        if h in self.store and h not in t['seen'] and 'changes' not in t:
            t['seen'].add(h)
            t['nodes'].append(self.store[h].hex())
        return orig_node(self, h)

    def ref(self, key):
        r = orig_getref(self, key)
        return None if r is None else [r[0], r[1].hex()]

    def get(self, key):
        t = track(self)
        t['keys'].setdefault(key.hex(), ref(self, key))
        return orig_get(self, key)

    def get_ref(self, key):
        t = track(self)
        t['keys'].setdefault(key.hex(), ref(self, key))
        return orig_getref(self, key)

    def update(self, changes):
        t = track(self)
        for k, _ in changes:
            t['keys'].setdefault(k.hex(), ref(self, k))
        t['changes'] = [[k.hex(), None if v is None else v.hex()] for k, v in changes]
        root = orig_update(self, changes)
        t['post_root'] = root.hex()
        return root

    Trie2.node, Trie2.get, Trie2.get_ref, Trie2.update = node, get, get_ref, update
    claim_b = open(os.path.join(case, "claim.bin"), "rb").read()
    witness_b = open(os.path.join(case, "witness.bin"), "rb").read()
    verdict = D3.check_case_inner(claim_b, witness_b)
    lean = json.loads(open(lean_json).read().splitlines()[0])
    assert lean['verdict'] == 'accept', lean['verdict']
    main_t = LOG['transitions'][0]
    lc = [[c['key'], None if c['valueLen'] is None else int(c['valueLen']), c['valueHash']]
          for c in lean['outputs']['stateChanges']]
    py = [[k, None if v is None else len(bytes.fromhex(v)),
           None if v is None else hashlib.sha256(bytes.fromhex(v)).hexdigest()]
          for k, v in main_t['changes']]
    res = dict(case=case, clean_room_verdict=verdict,
               n_transitions=len(LOG['transitions']),
               pre_root=main_t['pre_root'], post_root=main_t['post_root'],
               header_state_root=lean['outputs']['stateRoot'],
               nodes_read=main_t['nodes'], keys_read=main_t['keys'],
               changes=main_t['changes'], lean_changes=lc,
               lean_matches_clean_room=(lc == py))
    with open(out, "w") as f:
        json.dump(res, f, indent=1)
    print(json.dumps(dict(verdict=verdict, transitions=len(LOG['transitions']),
                          nodes=len(main_t['nodes']), keys=len(main_t['keys']),
                          changes=len(main_t['changes']), lean_match=lc == py,
                          post_eq_header=main_t['post_root'] == lean['outputs']['stateRoot'])))


if __name__ == "__main__":
    main()
