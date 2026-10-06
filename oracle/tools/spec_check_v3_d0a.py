#!/usr/bin/env python3
"""Independent Python checker for domain D0a of near/pv86/chunk-validation/v0
(spec/near-chunk-validation-v0a.md): RelD0a = RelD0 ∧ A1 ∧ A2 ∧ Canon0f.

Runs the D0 checker (spec_check_v3.py, unmodified: it is pinned with the live D0
challenges) and, on an accepting case, the amendments:
  A1  c.gas_limit        chunk gas_limit of B2's own-shard slot <= 10^15
  A2  w.proof_routing    every receipt of every used source receipt proof routes
                         (final layout) to the validated shard
  C0f e.sched_canonical  every 0x0f value read (main pre-state, each implicit
                         pre-state) is absent or BandwidthSchedulerState::V1 whose links
                         are exactly the layout's n^2 links, sender-major

usage: spec_check_v3_d0a.py CASE_DIR...   (one JSON line per case, as spec_check_v3.py)
"""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import spec_check_v3 as d0  # noqa: E402
from v3lib.prim import PartialTrie  # noqa: E402

MAX_GAS_LIMIT = 10 ** 15


def canonical(L, v):
    if v is None:
        return True
    r = d0.R(v)
    try:
        if r.u8() != 0:
            return False
        links = [(r.u64(), r.u64(), r.u64())[:2] for _ in range(r.u32())]
        r.hash()
        r.end()
    except Exception:
        return False
    want = [(s, t) for s in L.shard_ids for t in L.shard_ids]
    return links == want


def amendments(claim_b, witness_b):
    """Violated amendments of an accepted (RelD0) case."""
    c = d0.decode_claim(claim_b)
    wr = d0.R(witness_b)
    wr.bytes()
    W = d0.decode_state_witness(wr.bytes())
    H = d0.decode_inner_bytes(c['chunk_inner'])
    L = d0.decode_layout(c['epochs'][0]['layout_raw'])
    idx = L.index[H.shard_id]
    blocks = c['blocks']
    for b in blocks:
        b.height = d0.decode_inner_lite(b.lite_raw)['height']
        b.slots = []
        for raw, hi in b.slots_raw:
            s = d0.Slot()
            s.inner = d0.decode_inner_bytes(raw)
            s.height_included = hi
            b.slots.append(s)
    new = [b.slots[idx].height_included == b.height for b in blocks]
    b2i = new.index(True)
    stop = new.index(True, b2i + 1)
    v = []
    own_slot = blocks[b2i].slots[idx]
    if own_slot.inner.gas_limit > MAX_GAS_LIMIT:
        v.append("c.gas_limit")
    routed = True
    for S in blocks[b2i:stop]:
        for s in S.slots:
            if s.height_included != S.height:
                continue
            receipts = W['proofs'][s.inner.chunk_hash][0]
            if any(d0.account_to_shard(L, x.recv) != H.shard_id for x in receipts):
                routed = False
    if not routed:
        v.append("w.proof_routing")
    key = bytes([d0.COL_BW_STATE])
    reads = [PartialTrie(W['main']['base_state'], own_slot.inner.prev_state_root).get(key)]
    root = W['main']['post_state_root']
    for T in W['implicit']:
        reads.append(PartialTrie(T['base_state'], root).get(key))
        root = T['post_state_root']
    if not all(canonical(L, x) for x in reads):
        v.append("e.sched_canonical")
    return v


def check_case(d):
    verdict, reason = d0.check_case(d)
    if verdict != "accept":
        return verdict, reason
    try:
        cb = open(os.path.join(d, "claim.bin"), "rb").read()
        wb = open(os.path.join(d, "witness.bin"), "rb").read()
        v = amendments(cb, wb)
    except Exception as e:  # a bug in this checker
        print("spec_check_v3_d0a: INTERNAL ERROR on %s: %r" % (d, e), file=sys.stderr)
        return "reject", "INTERNAL ERROR %s: %s" % (type(e).__name__, e)
    if v:
        return "out_of_domain", ",".join(v)
    return "accept", "ok"


def main():
    for d in sys.argv[1:]:
        v, reason = check_case(d)
        print(json.dumps(dict(case=d, verdict=v, reason=reason)))
        sys.stdout.flush()


if __name__ == "__main__":
    main()
