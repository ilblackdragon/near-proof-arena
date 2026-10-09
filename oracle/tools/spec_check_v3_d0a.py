#!/usr/bin/env python3
"""Independent Python checker for domain D0a of near/pv86/chunk-validation/v0
(spec/near-chunk-validation-v0a.md): RelD0a = RelD0 ∧ A1 ∧ A2 ∧ Canon0f ∧ A7 ∧ A8 ∧ A9 ∧ A10.

Runs the D0 checker (spec_check_v3.py, unmodified: it is pinned with the live D0
challenges) and, on an accepting case, the amendments:
  A1  c.gas_limit        chunk gas_limit of B2's own-shard slot <= 10^15
  A2  w.proof_routing    every receipt of every used source receipt proof routes
                         (final layout) to the validated shard
  C0f e.sched_canonical  every 0x0f value read (main pre-state, each implicit
                         pre-state) is absent or BandwidthSchedulerState::V1 whose links
                         are exactly the layout's n^2 links, sender-major
  A7  w.unfolded         unfold_bytes <= B (default B0 = 2,000,000): for every applied
                         transition, the bytes of the pre-trie revealed along the read keys,
                         counted per path copy (node encodings + revealed values), plus the
                         post-trie's node copies (and revealed values) that differ from the
                         pre-trie at the same position. Independent implementation: the read
                         keys are the keys the D0 checker actually reads (recorded on its
                         PartialTrie instances), positions are walked on the raw node bytes.
  A8  c.bw_requests      in every block of the claim's segment, every chunk slot's
                         BandwidthRequests has pairwise distinct to_shard values.
  A9  e.chacha_words     the bandwidth-scheduler runs of all applied transitions draw at
                         most W (default W0 = 770,000) ChaCha20 words in total. Independent
                         count: every ChaCha20Rng the D0 checker's scheduler (v3lib/sched.py)
                         creates is a counting instance; the words drawn are its next_u32 calls.
  A10 w.path_depth       every used source receipt proof's Merkle path has at most D
                         (default Dp0 = 32) items.

Violations are reported joined by "," in the order A1, A2, C0f, A7, A8, A9, A10 (the order
of the Lean checkD0a checks; Lean reports only the first failing one).

usage: spec_check_v3_d0a.py [--bound B] [--words-bound W] [--depth-bound D] CASE_DIR...
       (one JSON line per case, as spec_check_v3.py, plus "unfold", "chacha_words",
       "max_path_depth")
"""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import spec_check_v3 as d0  # noqa: E402
from v3lib.prim import PartialTrie, nibbles, decode_node  # noqa: E402

MAX_GAS_LIMIT = 10 ** 15
B0 = 2_000_000
W0 = 770_000
DP0 = 32

# ---------------- A7: record the tries the D0 checker builds ----------------
_TRIES = []


class RecTrie(d0.PartialTrie):
    def __init__(self, values, root):
        super().__init__(values, root)
        self.pre_store = dict(self.store)
        self.pre_root = root
        self.keys = set()
        _TRIES.append(self)

    def get(self, key):
        self.keys.add(bytes(key))
        return super().get(key)


d0.PartialTrie = RecTrie

# ---------------- A9: count the ChaCha20 words the scheduler runs draw ----------------
_RNGS = []


class CountingRng(d0.sched.ChaCha20Rng):
    def __init__(self, seed):
        super().__init__(seed)
        self.words = 0
        _RNGS.append(self)

    def next_u32(self):
        self.words += 1
        return super().next_u32()


d0.sched.ChaCha20Rng = CountingRng


def sched_words(layout, prev_state, congestion, bw_requests, seed):
    """Words drawn by one scheduler run (v3lib/sched.run with a counting RNG)."""
    _RNGS.clear()
    d0.sched.run(layout, prev_state, congestion, bw_requests, seed)
    return sum(r.words for r in _RNGS)


def _parse(raw):
    """(kind, key nibbles, vref, children, child) or None (not a well-formed node)."""
    try:
        if len(raw) < 9:
            return None
        n = decode_node(raw)
    except Exception:
        return None
    return n


def _value(store, vref, want):
    if not want or vref is None:
        return None
    v = store.get(vref[1])
    if v is None or len(v) != vref[0]:
        return None
    return v


def unfold_pre(store, h, keys):
    if not keys or h is None or h not in store:
        return 0
    raw = store[h]
    n = _parse(raw)
    if n is None:
        return 0
    tot = len(raw)
    if n.kind == 'leaf':
        v = _value(store, n.vref, any(k == n.key for k in keys))
        return tot + (len(v) if v is not None else 0)
    if n.kind == 'ext':
        sub = [k[len(n.key):] for k in keys if k[:len(n.key)] == n.key]
        return tot + unfold_pre(store, n.child, sub)
    v = _value(store, n.vref, any(len(k) == 0 for k in keys))
    tot += len(v) if v is not None else 0
    for i, c in n.children.items():
        tot += unfold_pre(store, c, [k[1:] for k in keys if k and k[0] == i])
    return tot


def _slot_diff(pre_vref, post_store, post_vref, want):
    v = _value(post_store, post_vref, want)
    if v is None:
        return 0
    return 0 if pre_vref == post_vref else len(v)


def unfold_diff(pre_store, hpre, post_store, hpost, keys):
    if not keys or hpost is None or hpost not in post_store:
        return 0
    raw = post_store[hpost]
    n = _parse(raw)
    if n is None:
        return 0
    pn = None
    if hpre is not None and hpre in pre_store:
        pn = _parse(pre_store[hpre])
        if pn is not None and pre_store[hpre] == raw:
            return 0
    tot = len(raw)
    if n.kind == 'leaf':
        pv = pn.vref if (pn is not None and pn.kind == 'leaf' and pn.key == n.key) else None
        return tot + _slot_diff(pv, post_store, n.vref, any(k == n.key for k in keys))
    if n.kind == 'ext':
        pc = pn.child if (pn is not None and pn.kind == 'ext' and pn.key == n.key) else None
        sub = [k[len(n.key):] for k in keys if k[:len(n.key)] == n.key]
        return tot + unfold_diff(pre_store, pc, post_store, n.child, sub)
    pv = pn.vref if (pn is not None and pn.kind == 'branch') else None
    tot += _slot_diff(pv, post_store, n.vref, any(len(k) == 0 for k in keys))
    for i, c in n.children.items():
        pc = pn.children.get(i) if (pn is not None and pn.kind == 'branch') else None
        tot += unfold_diff(pre_store, pc, post_store, c, [k[1:] for k in keys if k and k[0] == i])
    return tot


def unfold_bytes(tries):
    tot = 0
    for t in tries:
        keys = [nibbles(k) for k in t.keys]
        tot += unfold_pre(t.pre_store, t.pre_root, keys)
        tot += unfold_diff(t.pre_store, t.pre_root, t.store, t.root, keys)
    return tot


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
    depth = 0
    for S in blocks[b2i:stop]:
        for s in S.slots:
            if s.height_included != S.height:
                continue
            receipts, _from, _to, path = W['proofs'][s.inner.chunk_hash]
            depth = max(depth, len(path))
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
    return v, depth


def a8_ok(claim_b):
    """A8: every slot of every block of the segment has distinct to_shard values."""
    c = d0.decode_claim(claim_b)
    for b in c['blocks']:
        for raw, _hi in b.slots_raw:
            tos = [t for t, _bm in d0.decode_inner_bytes(raw).bandwidth_requests]
            if len(set(tos)) != len(tos):
                return False
    return True


def check_case(d, bound=B0, words_bound=W0, depth_bound=DP0):
    """(verdict, reason, unfold_bytes, chacha_words, max_path_depth); the last three are None
    unless the D0 checker accepts."""
    _TRIES.clear()
    _RNGS.clear()
    verdict, reason = d0.check_case(d)
    tries = list(_TRIES)
    words = sum(r.words for r in _RNGS)
    if verdict != "accept":
        return verdict, reason, None, None, None
    try:
        cb = open(os.path.join(d, "claim.bin"), "rb").read()
        wb = open(os.path.join(d, "witness.bin"), "rb").read()
        v, depth = amendments(cb, wb)
        u = unfold_bytes(tries)
    except Exception as e:  # a bug in this checker
        print("spec_check_v3_d0a: INTERNAL ERROR on %s: %r" % (d, e), file=sys.stderr)
        return "reject", "INTERNAL ERROR %s: %s" % (type(e).__name__, e), None, None, None
    if u > bound:
        v.append("w.unfolded")
    try:
        if not a8_ok(cb):
            v.append("c.bw_requests")
    except Exception as e:  # a bug in this checker
        print("spec_check_v3_d0a: INTERNAL ERROR on %s: %r" % (d, e), file=sys.stderr)
        return "reject", "INTERNAL ERROR %s: %s" % (type(e).__name__, e), None, None, None
    if words > words_bound:
        v.append("e.chacha_words")
    if depth > depth_bound:
        v.append("w.path_depth")
    if v:
        return "out_of_domain", ",".join(v), u, words, depth
    return "accept", "ok", u, words, depth


def main():
    args = sys.argv[1:]
    bounds = {"--bound": B0, "--words-bound": W0, "--depth-bound": DP0}
    while args[:1] and args[0] in bounds:
        bounds[args[0]], args = int(args[1]), args[2:]
    for d in args:
        v, reason, u, k, p = check_case(d, bounds["--bound"], bounds["--words-bound"],
                                        bounds["--depth-bound"])
        print(json.dumps(dict(case=d, verdict=v, reason=reason, unfold=u, chacha_words=k,
                              max_path_depth=p)))
        sys.stdout.flush()


if __name__ == "__main__":
    main()
