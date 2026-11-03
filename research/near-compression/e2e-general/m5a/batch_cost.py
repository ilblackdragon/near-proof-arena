#!/usr/bin/env python3
"""FINAL batching model: SHA-256 work of FINAL as proved now (every change walk hashes the old
and the rewritten node of every row) against nearcore's order (`Trie::update`: apply the sorted
changes one by one to an in-memory trie, then hash every node of the final trie that is not an
untouched pre-state subtree once, children first).  The spec's `applyChanges` has the same shape:
`PTrie.upsert`/`del` never hash, only `rootHash` of the final trie does.

  batch_cost.py STATE_JSON DUMP_DIR NAMES_JSON

Counts are exact for the given chunk (same ptrie transcription the trace generator uses):
* `now`: the dump's SHA-256 messages of FINAL rows (BR/SN rows with walk id ≥ 2^20, old + new);
* `batched_open`: each distinct pre-state node a change walk reads, hashed once (authenticating it);
* `batched_fin`: each node of the final trie created by FINAL, hashed once;
* `batched_open_reuse`: as `batched_open`, minus pre-state nodes the INTAKE finds already hash
  (every node on an INTAKE path is authenticated there; FINAL may consume those digests).
Cell prices as `cost.py` (SHA-256 block 17 × 544 cells, one 544-cell start row per message)."""
import hashlib
import json
import os
import struct
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import ptrie as PT  # noqa: E402

SHA_ROW, SHA_BLK = 544, 17
W_FINAL = 1 << 20
ID_BR, ID_SN = 2 << 24, 3 << 24


def cells(nbytes):
    return SHA_ROW + SHA_BLK * SHA_ROW * ((nbytes + 9 + 63) // 64)


def load(path):
    b = open(path, 'rb').read()
    log, w = struct.unpack('<II', b[:8])
    h = 1 << log
    vals = struct.unpack('<%dI' % (h * w), b[8:])
    return [vals[r * w:(r + 1) * w] for r in range(h)]


def main():
    st = json.load(open(sys.argv[1]))
    dump, names = sys.argv[2], json.load(open(sys.argv[3]))
    sha = lambda b: hashlib.sha256(b).digest()
    # ---- now: FINAL rows' messages
    final_ids = set()
    for t, base in (('BR', ID_BR), ('SN', ID_SN)):
        rows = load(os.path.join(dump, t + '.bin'))
        iw, ia = names[t].index('w'), names[t].index('act')
        for rid, r in enumerate(rows):
            if r[ia] == 1 and r[iw] >= W_FINAL:
                final_ids |= {base + 2 * rid, base + 2 * rid + 1}
    msgs = json.load(open(os.path.join(dump, 'sha_msgs.json')))
    now = [len(m['bytes']) // 2 for m in msgs if m['id'] in final_ids]
    # ---- batched: in-memory sequential application, hash once at the end
    store = {sha(bytes.fromhex(n)): bytes.fromhex(n) for n in st['nodes_read']}
    t0 = PT.reveal_all(store, bytes.fromhex(st['pre_root']))
    pre_ids = {}

    def index(t):
        if t is None or t[0] == 'hash':
            return
        pre_ids[id(t)] = t
        if t[0] == 'ext':
            index(t[2])
        elif t[0] == 'branch':
            for c in t[2]:
                index(c)
    index(t0)
    changes = sorted((bytes.fromhex(k), None if v is None else bytes.fromhex(v)) for k, v in st['changes'])
    keys_read = [bytes.fromhex(k) for k in st['keys_read']]

    def path_nodes(t, K, d, out):
        """Pre-state nodes a walk along K reads (the nodes `upsert`/`del`/`findRef` visit)."""
        if t is None or t[0] == 'hash':
            return
        out.add(id(t))
        if t[0] == 'leaf':
            return
        if t[0] == 'ext':
            if K[d:d + len(t[1])] == t[1]:
                path_nodes(t[2], K, d + len(t[1]), out)
            return
        if d < len(K) and t[2][K[d]] is not None:
            path_nodes(t[2][K[d]], K, d + 1, out)

    opened = set()
    cur = t0
    for k, v in changes:
        seen = set()
        path_nodes(cur, PT.nibbles(k), 0, seen)
        # squash reads the remaining sibling of a branch losing a child: count it as read
        opened |= {x for x in seen if x in pre_ids}
        r = PT.apply_change(cur, k, None if v is None else (len(v), sha(v)), [])
        cur = r[1]
    # siblings read by squashing (`oLS`): every pre-state leaf adjacent to a deleted path that
    # ends up re-keyed in the final trie is hashed in `fin` anyway; its old read costs one hash
    intake = set()
    for k in keys_read:
        path_nodes(t0, PT.nibbles(k), 0, intake)
    fin = []

    def walk_final(t):
        if t is None or t[0] == 'hash' or id(t) in pre_ids:
            return
        fin.append(len(PT.serialize(t)))
        if t[0] == 'ext':
            walk_final(t[2])
        elif t[0] == 'branch':
            for c in t[2]:
                walk_final(c)
    walk_final(cur)
    op = [len(PT.serialize(pre_ids[x])) for x in opened]
    op_new = [len(PT.serialize(pre_ids[x])) for x in opened if x not in intake]
    res = dict(
        now_msgs=len(now), now_cells=sum(cells(n) for n in now),
        open_msgs=len(op), open_cells=sum(cells(n) for n in op),
        open_not_in_intake_msgs=len(op_new), open_not_in_intake_cells=sum(cells(n) for n in op_new),
        fin_msgs=len(fin), fin_cells=sum(cells(n) for n in fin))
    res['batched_cells'] = res['open_cells'] + res['fin_cells']
    res['batched_reuse_cells'] = res['open_not_in_intake_cells'] + res['fin_cells']
    res['saving'] = round(1 - res['batched_cells'] / res['now_cells'], 3)
    res['saving_reuse'] = round(1 - res['batched_reuse_cells'] / res['now_cells'], 3)
    assert PT.root_hash(cur).hex() == st['post_root']
    print(json.dumps(res, indent=1))


main()
