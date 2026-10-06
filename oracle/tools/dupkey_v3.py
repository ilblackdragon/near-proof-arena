#!/usr/bin/env python3
"""Duplicate chunk hashes among the used source chunks (V3-D0-DESIGN §3.5 `srcp`; lane v3-spec).

`checkD0` keys the source receipt proofs by `chunk_hash = sha256(sha256(inner) ‖ emr)` and
nothing in `RelD0` forbids two used source slots with the same inner (the claim's blocks are
authenticated only up to its own `prev_block_hash`). Construction, from an accepted D0 case:
in an older source block S' (index j ≥ 1 of the segment) with two new slots i ≠ k whose
proofs carry no receipts, replace slot k by a copy of slot i; recompute S'.chunk_headers_root,
the block hashes from S' up to blocks[0] (`prev_hash` links) and the endorsed chunk's
`prev_block_hash` (claim and witness header). Eligible only if every changed shuffle seed or
scheduler seed is irrelevant: blocks[0..j) have at most one non-empty source list each and
B2's context has no bandwidth requests (the scheduler RNG is then unused), no implicit blocks.

Two cases are written per eligible base case:
  * `dup` — the witness unchanged: the used keys are {K_i (twice), …} and slot k's old entry
    K_k is now an *extra, unused* entry, so `distinctKeys = used` still holds:
    expected **accept** (RelD0 satisfiable with duplicate keys);
  * `dup-noextra` — the same with the entry K_k removed: `distinctKeys = used − 1`:
    expected **reject** (`source_receipt_proofs contains extra proofs`).

usage: dupkey_v3.py --out DIR [--max N] CASE_DIR...
"""
import argparse, hashlib, json, os, shutil, struct, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import spec_check_v3 as d0  # noqa: E402

R = d0.R


def sha(b):
    return hashlib.sha256(b).digest()


def u32(x): return struct.pack('<I', x)
def u64(x): return struct.pack('<Q', x)
def bstr(b): return u32(len(b)) + b


def merkle(hashes):
    if not hashes:
        return bytes(32)
    while len(hashes) > 1:
        nxt = [sha(hashes[i] + hashes[i + 1]) for i in range(0, len(hashes) - 1, 2)]
        if len(hashes) % 2:
            nxt.append(hashes[-1])
        hashes = nxt
    return hashes[0]


def parse_claim(b):
    r = R(b)
    r.bytes(); r.bytes(); r.u32(); r.bytes(); r.hash()
    ci_start = r.i
    r.bytes()
    ci_end = r.i
    blocks = []
    for _ in range(r.u32()):
        v = r.u8(); ph = r.hash(); lite = r.bytes(); rest = r.bytes()
        slots = [(r.bytes(), r.u64()) for _ in range(r.u32())]
        blocks.append(dict(v=v, ph=ph, lite=lite, rest=rest, slots=slots))
    return b[:ci_start], b[ci_start + 4:ci_end], blocks, b[r.i:]


def enc_claim(prefix, inner, blocks, tail):
    out = prefix + bstr(inner) + u32(len(blocks))
    for x in blocks:
        out += bytes([x['v']]) + x['ph'] + bstr(x['lite']) + bstr(x['rest']) + u32(len(x['slots']))
        for s, h in x['slots']:
            out += bstr(s) + u64(h)
    return out + tail


def bhash(x):
    return sha(sha(sha(x['lite']) + sha(x['rest'])) + x['ph'])


def chunk_hash(inner):
    return sha(sha(inner) + inner[97:129])


def entries_spans(sw):
    """[(key, start, end, n_receipts)] of the source_receipt_proofs entries, and the vec offset."""
    r = R(sw)
    r.u8(); r.hash(); r.u8()
    d0.read_inner(r); r.u64(); d0.read_signature(r)
    d0.read_transition(r)
    vec_at = r.i
    out = []
    for _ in range(r.u32()):
        s = r.i
        key = r.hash()
        rs = r.vec(lambda: d0.read_receipt(r))
        r.u64(); r.u64(); r.vec(lambda: (r.hash(), r.u8()))
        out.append((key, s, r.i, len(rs)))
    return vec_at, out


def try_case(d, out, stats):
    cb = open(os.path.join(d, "claim.bin"), "rb").read()
    wb = open(os.path.join(d, "witness.bin"), "rb").read()
    prefix, inner, blocks, tail = parse_claim(cb)
    c = d0.decode_claim(cb)
    H = d0.decode_inner_bytes(c['chunk_inner'])
    L = d0.decode_layout(c['epochs'][0]['layout_raw'])
    idx = L.index[H.shard_id]
    heights = [d0.decode_inner_lite(x['lite'])['height'] for x in blocks]
    new = [x['slots'][idx][1] == h for x, h in zip(blocks, heights)]
    if not new[0]:
        return False  # implicit blocks present
    stop = new.index(True, 1)
    wr = R(wb); wr.bytes(); sw_start = wr.i + 4; sw = wr.bytes()
    vec_at, ents = entries_spans(sw)
    nrec = {k: n for k, _, _, n in ents}

    def new_slots(m):
        return [si for si, (s, h) in enumerate(blocks[m]['slots']) if h == heights[m]]
    # B2 context: no bandwidth requests anywhere
    if any(d0.decode_inner_bytes(s).bandwidth_requests for s, _ in blocks[0]['slots']):
        return False
    for j in range(1, stop):
        if any(sum(1 for si in new_slots(m) if nrec.get(chunk_hash(blocks[m]['slots'][si][0]), 0)) > 1
               for m in range(j)):
            break
        empties = [si for si in new_slots(j) if nrec.get(chunk_hash(blocks[j]['slots'][si][0]), 1) == 0]
        if len(empties) < 2:
            continue
        i, k = empties[0], empties[1]
        kk = chunk_hash(blocks[j]['slots'][k][0])
        nb = [dict(x, slots=list(x['slots'])) for x in blocks]
        nb[j]['slots'][k] = nb[j]['slots'][i]
        leaves = [sha(chunk_hash(s) + u64(h)) for s, h in nb[j]['slots']]
        nb[j]['rest'] = nb[j]['rest'][:64] + merkle(leaves) + nb[j]['rest'][96:]
        for m in range(j - 1, -1, -1):
            nb[m]['ph'] = bhash(nb[m + 1])
        h0 = bhash(nb[0])
        ninner = inner[:1] + h0 + inner[33:]
        ncb = enc_claim(prefix, ninner, nb, tail)
        # witness: header inner at sw[35:67] (tag, epoch, tag, inner tag, prev_block_hash)
        assert sw[35:67] == inner[1:33]
        nsw = sw[:35] + h0 + sw[67:]
        nwb = wb[:sw_start] + nsw + wb[sw_start + len(sw):]
        name = os.path.basename(os.path.normpath(d))
        for variant, w in (("dup", nwb), ("dup-noextra", None)):
            if w is None:
                span = [e for e in ents if e[0] == kk][0]
                n = struct.unpack('<I', nsw[vec_at:vec_at + 4])[0]
                s2 = nsw[:vec_at] + u32(n - 1) + nsw[vec_at + 4:span[1]] + nsw[span[2]:]
                w = wb[:sw_start - 4] + bstr(s2) + wb[sw_start + len(sw):]
            od = os.path.join(out, name + "-" + variant)
            os.makedirs(od, exist_ok=True)
            open(os.path.join(od, "claim.bin"), "wb").write(ncb)
            open(os.path.join(od, "witness.bin"), "wb").write(w)
            json.dump({"case": name + "-" + variant, "base": name, "kind": "dupkey",
                       "expected_rel_d0": variant == "dup",
                       "note": "slot %d of block %d replaced by slot %d (duplicate chunk hash among used source chunks)" % (k, j, i)},
                      open(os.path.join(od, "meta.json"), "w"), indent=1)
        stats["written"] += 2
        return True
    return False


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--max", type=int, default=50)
    ap.add_argument("cases", nargs="+")
    a = ap.parse_args()
    shutil.rmtree(a.out, ignore_errors=True)
    os.makedirs(a.out)
    stats = {"scanned": 0, "eligible": 0, "written": 0}
    for d in a.cases:
        if stats["eligible"] >= a.max:
            break
        stats["scanned"] += 1
        try:
            if try_case(d, a.out, stats):
                stats["eligible"] += 1
        except Exception as e:  # noqa: BLE001  (a base case this construction cannot use)
            print("skip %s: %r" % (d, e), file=sys.stderr)
    print(json.dumps(stats))


if __name__ == "__main__":
    main()
