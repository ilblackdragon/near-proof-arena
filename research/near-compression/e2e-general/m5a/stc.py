"""B-T3: the `STC` row (open / close the 42-B `stRoot`, `lean/StateM5a/Stc.lean`) and its `SRNG` table.

`build_stc(names, roles, comp, rin6, rout6, wslen, trie32, D, ...)` returns the `STC` rows, the `SRNG`
counts and the `STMQ` / `STMA` messages the stand-in for lane F's engine rows exchanges with it.
"""
import hashlib

import sha512c as S5

P = 2013265921
NB = 139
B_STMQ, B_STMA = 211, 212


def pad_byte(p):
    return 128 if p == 139 else 4 if p == 254 else 88 if p == 255 else 0


def ser(tag, ws, wslen, trie, idx, rest):
    assert len(ws) == 48 and len(trie) == 32 and len(rest) == 42 and 0 <= tag < 256
    return bytes([tag]) + ws + wslen.to_bytes(8, 'little') + trie + idx.to_bytes(8, 'little') + rest


def bdigest(m):
    return hashlib.sha384(m).digest()[:42]


def splits(word8):
    """`lo5, hi3` of byte 5, `lo2, hi6` of byte 2 (big-endian byte index)."""
    b5, b2 = word8[5], word8[2]
    return [b5 % 32, b5 // 32, b2 % 4, b2 // 4]



def limb3(b, i):
    return 65536 * b[3 * i] + 256 * b[3 * i + 1] + b[3 * i + 2]


class Stc:
    def __init__(self, names):
        self.cols = {nm: i for i, nm in enumerate(names['STC'])}
        self.width = len(names['STC'])

    def row(self):
        return [0] * self.width

    def set(self, r, nm, v, j=None):
        r[self.cols[nm if j is None else '%s.%d' % (nm, j)]] = v % P


def build(names, comp, rin_words, rout_words, wslen, trie, tag_in=1, tag_out=1, idx=0,
          rest_in=None, rest_out=None, mutant=None):
    """One active `STC` row.  `comp(h, block)` registers a compression and returns `(cid, out)`.
    Returns `(rows, rng_counts, stand_in_messages, info)`."""
    rest_in = rest_in if rest_in is not None else bdigest(b'lane F stand-in: rest of the input engine state')
    rest_out = rest_out if rest_out is not None else bdigest(b'lane F stand-in: rest of the output engine state')
    ws_in = b''.join(w.to_bytes(8, 'big') for w in rin_words)
    ws_out = b''.join(w.to_bytes(8, 'big') for w in rout_words)
    mi = ser(tag_in, ws_in, wslen, trie, idx, rest_in)
    mo = ser(tag_out, ws_out, wslen, trie, idx, rest_out)
    T = Stc(names)
    r = T.row()
    cnt = {}

    def rng(v):
        assert 0 <= v < 256, ('SRNG', v)
        cnt[v] = cnt.get(v, 0) + 1

    T.set(r, 'act', 1)
    for p in range(NB):
        T.set(r, 'b', mi[p], p)
    T.set(r, 'ot', mo[0])
    for j in range(48):
        T.set(r, 'ow', mo[1 + j], j)
    for j in range(42):
        T.set(r, 'or', mo[97 + j], j)

    def side(m, sname, hname, dname, xname, c1, c2, rname, rsname, wsname):
        pm = m + bytes(pad_byte(p) for p in range(NB, 256))
        assert pm == m + b'\x80' + b'\x00' * 100 + (8 * NB).to_bytes(16, 'big')
        words = [int.from_bytes(pm[8 * w:8 * w + 8], 'big') for w in range(32)]
        for w in range(18):
            for q, x in enumerate(splits(pm[8 * w:8 * w + 8])):
                T.set(r, sname, x, 4 * w + q)
        cid1, h1 = comp(S5.IV384, words[:16])
        cid2, out = comp(h1, words[16:])
        T.set(r, c1, cid1); T.set(r, c2, cid2)
        for w in range(8):
            for l, x in enumerate(S5.limbs(h1[w])):
                T.set(r, hname, x, 3 * w + l)
        for w in range(6):
            for l, x in enumerate(S5.limbs(out[w])):
                T.set(r, dname, x, 3 * w + l)
        for w in range(2):
            for l, x in enumerate(S5.limbs(out[6 + w])):
                T.set(r, xname, x, 3 * w + l)
        dig = b''.join(x.to_bytes(8, 'big') for x in out[:6])
        assert dig == hashlib.sha384(m).digest()
        for j in range(48):
            T.set(r, rname, dig[j], j)
        for k in range(6):
            for q, x in enumerate(splits(dig[8 * k:8 * k + 8])):
                T.set(r, rsname, x, 4 * k + q)
        ws = m[1:49]
        for k in range(6):
            for q, x in enumerate(splits(ws[8 * k:8 * k + 8])):
                T.set(r, wsname, x, 4 * k + q)
        return dig

    di = side(mi, 'si', 'hi', 'di', 'xi', 'ci1', 'ci2', 'ri', 'rsi', 'wsi')
    do = side(mo, 'so', 'ho', 'do', 'xo', 'co1', 'co2', 'ro', 'rso', 'wso')
    D = names['D']
    g = (1 << D) - wslen
    assert g < 1 << 24
    # `wsLen ≤ 2^D`: three bytes; a larger count (mutant `stcbig`) has no byte decomposition — the
    # row then carries the field value of `2^D − wsLen` in `g.0` (an `SRNG` lookup that cannot balance)
    gb = [(g >> (8 * k)) & 255 for k in range(3)] if g >= 0 else [g % P, 0, 0]
    for k in range(3):
        T.set(r, 'g', gb[k], k)
    # the lookups (`Stc.ranges`): every byte column once, every split part twice
    byte_cols = list(mi) + [mo[0]] + list(mo[1:49]) + list(mo[97:139]) + list(di) + list(do) + \
        [x for x in gb if x < 256]
    for x in byte_cols:
        rng(x)
    grps = (('si', 18), ('so', 18), ('rsi', 6), ('rso', 6), ('wsi', 6), ('wso', 6))
    part = lambda nm, i: r[T.cols['%s.%d' % (nm, i)]]
    for nm, n in grps:                      # `Stc.hiCols`: one lookup
        for w in range(n):
            rng(part(nm, 4 * w + 1)); rng(part(nm, 4 * w + 3))
    for nm, n in grps:                      # `Stc.loCols`: x and 2^(8-k) x
        for w in range(n):
            for q, k in ((0, 5), (2, 2)):
                x = part(nm, 4 * w + q)
                rng(x); rng(x << (8 - k))
    r_in, r_out = di[:42], do[:42]
    assert r_in == bdigest(mi) and r_out == bdigest(mo)
    stmq = [limb3(r_in, i) for i in range(14)] + [mo[0]] + [limb3(rest_out, i) for i in range(14)]
    stma = [limb3(r_out, i) for i in range(14)] + [mi[0]] + [limb3(rest_in, i) for i in range(14)]
    # the stand-in for lane F's engine rows: sends STMQ, receives STMA
    msgs = [[B_STMQ, True, stmq], [B_STMA, False, stma]]
    info = dict(st_root_in=r_in.hex(), st_root_out=r_out.hex(), rest_in=rest_in.hex(), rest_out=rest_out.hex(),
                tag_in=tag_in, tag_out=tag_out, ws_len=wslen, trie=trie.hex(), idx=idx)
    return [r], cnt, msgs, info


def srng_rows(names, cnt):
    cols = {nm: i for i, nm in enumerate(names['SRNG'])}
    rows = []
    for v in range(256):
        r = [0] * len(names['SRNG'])
        r[cols['v']] = v
        c = cnt.get(v, 0)
        assert c < 1 << 20
        for t in range(20):
            r[cols['m.%d' % t]] = (c >> t) & 1
        rows.append(r)
    return rows
