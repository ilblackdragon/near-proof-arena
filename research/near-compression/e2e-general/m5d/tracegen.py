#!/usr/bin/env python3
"""E2E M5d trace generator (lane G): the FINAL template (class F1) of one chunk.

    tracegen.py DUMP_JSON NAMES_JSON OUT_DIR [--mutant NAME]

DUMP_JSON is `m5d-tool dump` (the Lean `allFeatures` checker's own `finK` + `tailNew` on the case);
NAMES_JSON is `m5d-tool air-final` (table and column names, class constants). Writes one `.bin`
per table (u32 log2 height, u32 width, row-major u32 cells), `sha_msgs.json` (SHA-256 messages),
`comps.json` (SHA-512 compressions, chip order), `pubs.bin` (public values the proof carries) and
`stmt_pubs.bin` (the statement's: for a mutant, those of the honest run). Exit code 3: the mutant
does not apply.

Every output is recomputed here from the `FinIn` record exactly as the AIR does, and compared with
the checker's `o` (`dump.outputs`) before anything is written.
"""
import hashlib
import json
import os
import struct
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sha512c import compress, limbs, IV384  # noqa: E402

P = 0x78000001


def u(n, w):
    return list(n.to_bytes(w, 'little'))


def sha256(b):
    return list(hashlib.sha256(bytes(b)).digest())


def merkle_root(leaves):
    """nearcore `merklize` (NearSpec.merkleRoot)."""
    if not leaves:
        return [0] * 32
    lvl = list(leaves)
    while len(lvl) > 1:
        nxt = []
        for i in range(0, len(lvl) - 1, 2):
            nxt.append(sha256(lvl[i] + lvl[i + 1]))
        if len(lvl) % 2:
            nxt.append(lvl[-1])
        lvl = nxt
    return lvl[0]


def limbs3(bs):
    return [65536 * bs[3 * i] + 256 * bs[3 * i + 1] + bs[3 * i + 2] for i in range(14)]


def gf_mul(a, b):
    r = 0
    for _ in range(8):
        if b & 1:
            r ^= a
        hi = a & 0x80
        a = (a << 1) & 0xFF
        if hi:
            a ^= 0x1D
        b >>= 1
    return r


class Table:
    def __init__(self, name, cols):
        self.name = name
        self.cols = {c: i for i, c in enumerate(cols)}
        self.width = len(cols)
        self.rows = []

    def new(self):
        r = [0] * self.width
        self.rows.append(r)
        return r

    def ix(self, nm, j=None):
        return self.cols[nm if j is None else '%s.%d' % (nm, j)]

    def set(self, r, nm, v, j=None):
        r[self.ix(nm, j)] = v % P

    def setv(self, r, nm, vs, o=0):
        for j, v in enumerate(vs):
            r[self.ix(nm, o + j)] = v % P

    def get(self, r, nm, j=None):
        return r[self.ix(nm, j)]

    def height(self, min_rows=4, spare=False):
        h = max(len(self.rows) + (1 if spare else 0), min_rows)
        return 1 << (h - 1).bit_length()

    def dump(self, path, h):
        with open(path, 'wb') as f:
            f.write(struct.pack('<II', h.bit_length() - 1, self.width))
            for i in range(h):
                row = self.rows[i] if i < len(self.rows) else [0] * self.width
                f.write(struct.pack('<%dI' % self.width, *[x % P for x in row]))


class Gen:
    def __init__(self, dump, names, mutant=None):
        self.d = dump
        self.names = names
        self.C = names['consts']
        self.mutant = mutant
        self.applied = mutant is None
        self.T = {n: Table(n, names['cols'][n]) for n in names['tables'] if n != 'SHA'}
        self.sha_msgs = []
        self.comps = []
        self.r8, self.s2, self.s5 = {}, {}, {}

    # -- lookups ------------------------------------------------------------------------------
    def look(self, d, v, k=1):
        d[v] = d.get(v, 0) + k

    def mut(self, name):
        if self.mutant == name:
            self.applied = True
            return True
        return False

    # -- SHA-256 / SHA-384 messages -----------------------------------------------------------
    def sha(self, mid, msg):
        self.sha_msgs.append(dict(id=mid, bytes=bytes(msg).hex()))
        return sha256(msg)

    def s384(self, mid, msg):
        """SHA-384 of `msg` as `S384` rows; returns the 48 digest bytes."""
        T = self.T['S384']
        n = len(msg)
        padded = list(msg) + [0x80] + [0] * ((111 - n) % 128) + list((8 * n).to_bytes(16, 'big'))
        nblk = len(padded) // 128
        h = list(IV384)
        m0 = 1
        for k in range(nblk):
            blk = padded[128 * k:128 * k + 128]
            r = T.new()
            nd = max(0, min(128, n - 128 * k))
            T.set(r, 'act', 1)
            T.set(r, 'first', int(k == 0))
            T.set(r, 'last', int(k == nblk - 1))
            ndp = max(0, min(128, n - 128 * (k - 1))) if k > 0 else 128
            T.set(r, 'x', int(k > 0 and ndp < 128))
            T.set(r, 'id', mid)
            T.set(r, 'len', n)
            T.set(r, 'cnt', 128 * k)
            T.set(r, 'cid', 128 * len(self.comps))
            for i in range(128):
                T.set(r, 'f', int(i < nd), i)
                T.set(r, 'b', blk[i], i)
            # m0: 0x80 at byte 0 of this block (`f_prev[127] − f[0]`, `1 − f[0]` on the first block)
            T.set(r, 'm0', int(ndp == 128) - int(nd > 0))
            words = [int.from_bytes(bytes(blk[8 * w:8 * w + 8]), 'big') for w in range(16)]
            for w in range(16):
                b2, b5 = blk[8 * w + 2], blk[8 * w + 5]
                T.set(r, 's5lo', b5 % 32, w); T.set(r, 's5hi', b5 // 32, w)
                T.set(r, 's2lo', b2 % 4, w); T.set(r, 's2hi', b2 // 4, w)
                self.look(self.s5, b5); self.look(self.s2, b2)
                for i in (0, 1, 3, 4, 6, 7):
                    self.look(self.r8, blk[8 * w + i])
            out = compress(h, words)
            self.comps.append(dict(h=[str(x) for x in h], block=[str(x) for x in words]))
            T.setv(r, 'hin', [l for x in h for l in limbs(x)])
            T.setv(r, 'hout', [l for x in out for l in limbs(x)])
            if k == nblk - 1:
                ob = b''.join(x.to_bytes(8, 'big') for x in out[:6])
                for w in range(6):
                    b2, b5 = ob[8 * w + 2], ob[8 * w + 5]
                    T.set(r, 'o5lo', b5 % 32, w); T.set(r, 'o5hi', b5 // 32, w)
                    T.set(r, 'o2lo', b2 % 4, w); T.set(r, 'o2hi', b2 // 4, w)
                    self.look(self.s5, b5); self.look(self.s2, b2)
                    for i in (0, 1, 3, 4, 6, 7):
                        self.look(self.r8, ob[8 * w + i])
                T.setv(r, 'ob', list(ob))
            h = out
        dg = list(b''.join(x.to_bytes(8, 'big') for x in h[:6]))
        assert bytes(dg) == hashlib.sha384(bytes(msg)).digest()
        return dg

    # -- the run ------------------------------------------------------------------------------
    def run(self):
        d, C = self.d, self.C
        assert all(d['checks'].values()), d['checks']
        NS, RSD, RST = C['NS'], C['RSD'], C['RST']
        acc0 = C['acc0']
        fin = d['finIn']
        pre, post = bytes.fromhex(d['pre']), bytes.fromhex(d['post'])
        ci_off = C['CI_OFF']
        stream = bytearray(u(len(pre), 4)) + pre + post
        H = {'psr': 33, 'por': 65, 'emr': 97, 'el': 129, 'gu': 153, 'gl': 161, 'bb': 169, 'orr': 185,
             'txr': 217, 'props': 249, 'cong': 253, 'bw': 296, 'split': 301}
        # header (statement) mutants: one byte of each compared field of the public chunk header
        for k, o in H.items():
            if self.mut('hdr_' + k):
                stream[ci_off + o + (1 if k in ('props', 'cong', 'bw') else 0)] ^= 1
        stream = list(stream)
        assert len(pre) == C['PRE_LEN'] and len(stream) >= C['HBN']
        # -- FinIn ----------------------------------------------------------------------------
        root = list(bytes.fromhex(fin['root']))
        if self.mut('fin_root'):
            root[5] ^= 1
        cong = list(bytes.fromhex(fin['congestion']))
        if self.mut('fin_cong'):
            cong[3] ^= 1
        gas, bal, gl = int(fin['gasUsed']), int(fin['balanceBurnt']), int(fin['gasLimit'])
        if self.mut('fin_gas'):
            gas += 1
        if self.mut('fin_bal'):
            bal += 1
        if self.mut('fin_gl'):
            gl -= 1
        assert bytes.fromhex(fin['proposed']) == b'\x00' and not fin['proposals'] and not fin['bwRequests']
        assert not fin['txs']
        leaves = [list(bytes.fromhex(x)) for x in fin['outcomeLeaves']]
        if self.mut('leaf'):
            leaves[0][7] ^= 1
        if self.mut('outcome_drop'):
            leaves = leaves[:-1]
        sids = [int(s) for s in fin['shardIds']]
        assert len(sids) == NS and all(s < 65536 for s in sids)
        rcpts = [(int(r['shard']), list(bytes.fromhex(r['enc']))) for r in fin['outgoing']]
        if self.mut('rcpt_byte'):
            rcpts[0][1][40] ^= 1
        if self.mut('rcpt_shard'):
            s0 = rcpts[0][0]
            rcpts[0] = ([s for s in sids if s != s0][0], rcpts[0][1])
        if self.mut('rcpt_drop'):
            rcpts = rcpts[:-1]
        if self.mut('rcpt_swap'):
            rcpts[1], rcpts[2] = rcpts[2], rcpts[1]
        # outcome chain (OUTL)
        T = self.T['OUTL']
        acc = list(acc0)
        for i, lf in enumerate(leaves):
            r = T.new()
            T.set(r, 'act', 1); T.set(r, 'i', i)
            T.setv(r, 'leaf', lf); T.setv(r, 'acc', acc)
            dg = self.s384(C['OCH0'] + i, acc + lf)
            T.setv(r, 'dg', dg)
            acc = dg[:42]
        oacc = acc
        # receipt chain + segments (SEG) + body (BODY)
        body_r = []
        for s, enc in rcpts:
            body_r.append(enc)
        body = u(0, 4) + u(len(rcpts), 4) + [b for e in body_r for b in e]
        n = len(body)
        L = (n + RSD - 1) // RSD
        S = self.T['SEG']
        segs = []   # (kind, start, ell, sha_id, sha_b, s_id)
        cnt, off = [0] * NS, [0] * NS
        acc = list(acc0)
        shard_bytes = [[] for _ in range(NS)]
        start = 0
        # p0
        r = S.new(); S.set(r, 'act', 1); S.set(r, 'i', 0); S.set(r, 'kp0', 1); S.set(r, 'start', 0)
        S.set(r, 'ell', 4); S.set(r, 'nR', len(rcpts)); S.setv(r, 'sid', sids)
        segs.append(('p', 0, 4, 0, 0, 0)); start = 4
        # p1
        r = S.new(); S.set(r, 'act', 1); S.set(r, 'i', 1); S.set(r, 'kp1', 1); S.set(r, 'start', 4)
        S.set(r, 'ell', 4); S.set(r, 'nR', len(rcpts)); S.setv(r, 'sid', sids)
        S.set(r, 'r', len(rcpts) % 256, 0); S.set(r, 'r', len(rcpts) // 256, 1)
        self.look(self.r8, len(rcpts) % 256); self.look(self.r8, len(rcpts) // 256)
        segs.append(('p', 4, 4, 0, 0, 0)); start = 8
        for ci, (s, enc) in enumerate(rcpts):
            q = sids.index(s)
            ell = len(enc)
            r = S.new()
            S.set(r, 'act', 1); S.set(r, 'i', 2 + ci); S.set(r, 'krc', 1); S.set(r, 'start', start)
            S.set(r, 'ell', ell); S.setv(r, 'l', u(ell, 3)); S.set(r, 'ci', ci); S.set(r, 'nR', len(rcpts))
            S.setv(r, 'sid', sids); S.set(r, 'sh', 1, q)
            S.setv(r, 'sb', u(s, 2)); S.setv(r, 'cnt', cnt); S.setv(r, 'off', off); S.setv(r, 'acc', acc)
            for v in u(ell, 3) + u(s, 2):
                self.look(self.r8, v)
            msg = acc + u(s, 8) + u(ell, 4) + enc
            dg = self.s384(C['RCH0'] + ci, msg)
            S.setv(r, 'dg', dg)
            acc = dg[:42]
            segs.append(('r', start, ell, C['SHM0'] + q, 12 + off[q], C['RCH0'] + ci))
            shard_bytes[q] += enc
            cnt[q] += 1
            off[q] += ell
            start += ell
        racc = acc
        assert start == n
        r = S.new()
        S.set(r, 'act', 1); S.set(r, 'i', 2 + len(rcpts)); S.set(r, 'kpad', 1); S.set(r, 'start', n)
        S.set(r, 'ell', RSD * L - n); S.set(r, 'ci', len(rcpts)); S.set(r, 'nR', len(rcpts))
        S.setv(r, 'sid', sids); S.setv(r, 'cnt', cnt); S.setv(r, 'off', off); S.set(r, 'pz', int(RSD * L == n))
        if RSD * L > n:
            segs.append(('z', n, RSD * L - n, 0, 0, 0))
        padded = body + [0] * (RSD * L - n)
        B = self.T['BODY']
        k = 0
        for si, (kind, st, ell, sha_id, sha_b, s_id) in enumerate(segs):
            for j in range(ell):
                r = B.new()
                B.set(r, 'act', 1); B.set(r, 'k', k); B.set(r, 'b', padded[k])
                B.set(r, 'p', k // L); B.set(r, 'off', k % L); B.set(r, 'w', int(k % L == L - 1))
                B.set(r, 'i', si); B.set(r, 'j', j); B.set(r, 'ell', ell); B.set(r, 'e', int(j == ell - 1))
                B.set(r, 'st', int(j == 0))
                B.set(r, {'p': 'kp', 'r': 'kr', 'z': 'kz'}[kind], 1)
                B.set(r, 'shaId', sha_id); B.set(r, 'shaB', sha_b); B.set(r, 'sId', s_id)
                k += 1
        assert k == RSD * L
        if self.mut('body_byte'):
            B.rows[20][B.ix('b')] ^= 1
        # shard messages (SHD)
        D = self.T['SHD']
        sh_leaves = []
        for q, s in enumerate(sids):
            r = D.new()
            D.set(r, 'act', 1); D.set(r, 'q', q); D.setv(r, 'sb', u(s, 2)); D.setv(r, 'c', u(cnt[q], 2))
            D.set(r, 'offv', off[q])
            for v in u(s, 2) + u(cnt[q], 2):
                self.look(self.r8, v)
            d1 = self.sha(C['SHM0'] + q, u(s, 8) + u(cnt[q], 4) + shard_bytes[q])
            d2 = self.sha(C['SHL0'] + q, d1)
            D.setv(r, 'd1', d1); D.setv(r, 'd2', d2)
            sh_leaves.append(d2)
        # Reed–Solomon (RS, PART)
        M = C['matrix']
        data = [padded[p * L:(p + 1) * L] for p in range(RSD)]
        par = [[0] * L for _ in range(RST - RSD)]
        R = self.T['RS']
        for o in range(L):
            r = R.new()
            R.set(r, 'act', 1); R.set(r, 'off', o)
            for p in range(RSD):
                for m in range(8):
                    R.set(r, 'x', (data[p][o] >> m) & 1, 8 * p + m)
            for i in range(RST - RSD):
                v = 0
                for j in range(RSD):
                    v ^= gf_mul(M[RSD + i][j], data[j][o])
                par[i][o] = v
                for kb in range(8):
                    s = sum(((gf_mul(M[RSD + i][j], 1 << m) >> kb) & 1) * ((data[j][o] >> m) & 1)
                            for j in range(RSD) for m in range(8))
                    assert s % 2 == (v >> kb) & 1
                    R.set(r, 'r', s % 2, 8 * i + kb)
                    R.set(r, 'q', s // 2, 8 * i + kb)
                    self.look(self.r8, s // 2)
        if self.mut('rs_par'):
            ri = R.ix('r', 3)
            R.rows[5][ri] ^= 1
        parts = data + par
        Pt = self.T['PART']
        part_leaves = []
        for q in range(RST):
            r = Pt.new()
            Pt.set(r, 'act', 1); Pt.set(r, 'q', q); Pt.setv(r, 'l', u(L, 3))
            for v in u(L, 3):
                self.look(self.r8, v)
            dq = self.sha(C['PID0'] + q, u(L, 4) + parts[q])
            Pt.setv(r, 'd', dq)
            part_leaves.append(dq)
        # Merkle trees (MRK)
        roots = {}
        for tr, lv in ((C['TR_OUT'], leaves), (C['TR_SH'], sh_leaves), (C['TR_RS'], part_leaves)):
            roots[tr] = self.tree(tr, lv)
        # cross-check every output with the checker's
        o = d['outputs']
        honest = self.mutant is None
        if honest:
            assert bytes(roots[C['TR_OUT']]).hex() == o['outcomeRoot']
            assert bytes(roots[C['TR_SH']]).hex() == o['outgoingRoot']
            assert bytes(roots[C['TR_RS']]).hex() == o['encodedMerkleRoot']
            assert n == int(o['encodedLength'])
            assert bytes(root).hex() == o['stateRoot']
        # FinIn bytes
        fi = (root + cong + u(gas, 8) + u(bal, 16) + u(gl, 8) + [0] + u(0, 4) + u(0, 4) + oacc + racc +
              list(acc0) + u(NS, 4) + [b for s in sids for b in u(s, 8)])
        assert len(fi) == C['FI_LEN']
        fd = self.s384(C['ID_FIN'], [C['FIN_TAG']] + fi)
        cd = self.s384(C['ID_CLAIM'], stream)
        # STMT
        St = self.T['STMT']
        for kk, bb in enumerate(stream):
            r = St.new()
            St.set(r, 'act', 1); St.set(r, 'k', kk); St.set(r, 'b', bb); St.set(r, 'h', int(kk < C['HBN']))
        if self.mut('stmt_byte'):
            St.rows[ci_off + 40][St.ix('b')] ^= 1
        # FIN
        F = self.T['FIN']
        r = F.new()
        F.set(r, 'act', 1)
        F.setv(r, 'hb', stream[:C['HBN']])
        F.setv(r, 'fi', fi)
        F.setv(r, 'ro', roots[C['TR_OUT']]); F.setv(r, 'rs', roots[C['TR_RS']]); F.setv(r, 'rsh', roots[C['TR_SH']])
        F.setv(r, 'cd', cd); F.setv(r, 'fd', fd)
        F.set(r, 'nO', len(leaves)); F.set(r, 'nR', len(rcpts)); F.set(r, 'lenC', len(stream))
        x = RSD * L - n
        self.look(self.r8, x); self.look(self.r8, x + 256 - RSD)
        if self.mut('fin_ro'):
            F.rows[0][F.ix('ro', 0)] ^= 1
        self.fill_rng()
        pubs = limbs3(cd[:42]) + limbs3(fd[:42]) + [n, L]
        stmt = list(pubs)
        if self.mut('pub_claim'):
            pubs[3] += 1
        if self.mut('pub_n'):
            pubs[28] += 1
        self.pubs, self.stmt_pubs = pubs, stmt
        return dict(n=n, L=L, rcpts=len(rcpts), outcomes=len(leaves), stream=len(stream))

    def fill_rng(self):
        G = self.T['RNG']
        for v in range(256):
            r = G.new()
            G.set(r, 'v', v)
            for i in range(8):
                G.set(r, 'bit', (v >> i) & 1, i)
            for nm, dd in (('m8', self.r8), ('m2', self.s2), ('m5', self.s5)):
                c = dd.get(v, 0)
                assert c < (1 << 20)
                for i in range(20):
                    G.set(r, nm, (c >> i) & 1, i)
        assert all(v < 256 for dd in (self.r8, self.s2, self.s5) for v in dd), 'range lookup out of range'

    def tree(self, tr, leaves):
        T = self.T['MRK']
        c = len(leaves)
        lvl_nodes = list(leaves)
        first = True
        lvl = 0
        while True:
            if c <= 1:
                r = T.new()
                T.set(r, 'act', 1); T.set(r, 'f', int(first)); T.set(r, 'tr', tr); T.set(r, 'lvl', lvl)
                T.set(r, 'c', c); T.set(r, 'kt', 1); T.set(r, 'e0', int(c == 0)); T.set(r, 'g', len(T.rows) - 1)
                root = lvl_nodes[0] if c == 1 else [0] * 32
                T.setv(r, 'lb', root)
                return root
            nxt = []
            for idx in range((c + 1) // 2):
                r = T.new()
                g = len(T.rows) - 1
                T.set(r, 'act', 1); T.set(r, 'f', int(first)); first = False
                T.set(r, 'tr', tr); T.set(r, 'lvl', lvl); T.set(r, 'idx', idx); T.set(r, 'c', c); T.set(r, 'g', g)
                last_of_lvl = idx == (c + 1) // 2 - 1
                T.set(r, 'z', int(last_of_lvl))
                T.setv(r, 'lb', lvl_nodes[2 * idx])
                if 2 * idx + 1 < c:
                    T.set(r, 'kh', 1)
                    T.setv(r, 'rb', lvl_nodes[2 * idx + 1])
                    ob = self.sha(self.C['MID0'] + g, lvl_nodes[2 * idx] + lvl_nodes[2 * idx + 1])
                    if self.mut('mrk_node') and tr == self.C['TR_SH']:
                        ob = list(ob); ob[0] ^= 1
                    T.setv(r, 'ob', ob)
                    nxt.append(ob)
                else:
                    T.set(r, 'kc', 1)
                    nxt.append(lvl_nodes[2 * idx])
            lvl_nodes = nxt
            c = len(nxt)
            lvl += 1

    def write(self, out):
        os.makedirs(out, exist_ok=True)
        heights = {}
        spare = {'STMT', 'BODY', 'SEG', 'RS', 'PART', 'SHD', 'OUTL', 'MRK'}
        for nm, T in self.T.items():
            h = 256 if nm == 'RNG' else T.height(spare=nm in spare)
            if nm == 'S384' and self.mut('s384_pad'):
                r = T.rows[0]
                r[T.ix('b', 127)] ^= 1
            T.dump(os.path.join(out, nm + '.bin'), h)
            heights[nm] = (len(T.rows), h)
        json.dump(self.sha_msgs, open(os.path.join(out, 'sha_msgs.json'), 'w'))
        json.dump(self.comps, open(os.path.join(out, 'comps.json'), 'w'))
        with open(os.path.join(out, 'pubs.bin'), 'wb') as f:
            f.write(struct.pack('<%dI' % len(self.pubs), *[x % P for x in self.pubs]))
        with open(os.path.join(out, 'stmt_pubs.bin'), 'wb') as f:
            f.write(struct.pack('<%dI' % len(self.stmt_pubs), *[x % P for x in self.stmt_pubs]))
        return heights


class GenInit(Gen):
    """The INIT template: `claimDigest` and `ctxRoot` of `B_0` from the claim and witness bytes."""

    def run(self):
        d, C = self.d, self.C
        pre, blocks, post = (list(bytes.fromhex(d[k])) for k in ('pre', 'blocks', 'post'))
        wit = list(bytes.fromhex(d['witness']))
        assert bytes(pre + blocks + post).hex() == d['claim']
        if self.mut('pre_byte'):
            pre[30] ^= 1
        if self.mut('wit_byte'):
            wit[100] ^= 1
        if self.mut('blk_byte'):
            blocks[7] ^= 1
        kinds = [('ka', pre), ('kb', blocks), ('kp', post), ('kw', wit)]
        T = self.T['CLM']
        kc = ks = na = nb = nc = 0
        for kind, bs in kinds:
            for b in bs:
                r = T.new()
                T.set(r, 'act', 1); T.set(r, 'kc', kc); T.set(r, 'ks', ks); T.set(r, 'b', b); T.set(r, kind, 1)
                T.set(r, 'na', na); T.set(r, 'nb', nb); T.set(r, 'nc', nc)
                kc += 1
                ks += kind in ('ka', 'kp')
                na += kind == 'ka'
                nb += kind == 'kb'
                nc += kind != 'kw'
        if self.mut('clm_kind'):
            T.rows[len(pre) + 2][T.ix('kb')] = 0
            T.rows[len(pre) + 2][T.ix('kp')] = 1
        if self.mut('clm_byte'):
            T.rows[len(pre) + len(blocks) + 5][T.ix('b')] ^= 1
        stmt = u(len(pre), 4) + pre + post
        cb = pre + blocks + post
        ctx = [C['CTX_TAG']] + u(len(blocks), 4) + u(len(cb), 4) + cb + wit
        cd = self.s384(C['ID_CLAIM'], stmt)
        xd = self.s384(C['ID_CTX'], ctx)
        I = self.T['INI']
        r = I.new()
        I.set(r, 'act', 1); I.set(r, 'na', len(pre)); I.set(r, 'nb', len(blocks)); I.set(r, 'nc', len(cb))
        I.set(r, 'nt', len(cb) + len(wit)); I.set(r, 'ns', len(pre) + len(post))
        I.setv(r, 'cd', cd); I.setv(r, 'xd', xd)
        I.setv(r, 'pa', u(len(pre), 3)); I.setv(r, 'lb', u(len(blocks), 3)); I.setv(r, 'lc', u(len(cb), 3))
        for v in u(len(pre), 3) + u(len(blocks), 3) + u(len(cb), 3):
            self.look(self.r8, v)
        if self.mut('ini_lb'):
            r[I.ix('lb', 0)] += 1
            r[I.ix('nb')] += 1
        self.fill_rng()
        pubs = limbs3(cd[:42]) + limbs3(xd[:42])
        self.pubs, self.stmt_pubs = pubs, list(pubs)
        if self.mut('pub_ctx'):
            self.pubs[20] += 1
        return dict(pre=len(pre), blocks=len(blocks), post=len(post), witness=len(wit), claimDigest=bytes(cd[:42]).hex(),
                    ctxRoot=bytes(xd[:42]).hex())


INIT_MUTANTS = ['pre_byte', 'blk_byte', 'wit_byte', 'clm_kind', 'clm_byte', 'ini_lb', 'pub_ctx']

MUTANTS = ['hdr_psr', 'hdr_por', 'hdr_emr', 'hdr_el', 'hdr_gu', 'hdr_gl', 'hdr_bb', 'hdr_orr', 'hdr_txr',
           'hdr_props', 'hdr_cong', 'hdr_bw', 'hdr_split',
           'fin_root', 'fin_cong', 'fin_gas', 'fin_bal', 'fin_gl',
           'leaf', 'outcome_drop', 'rcpt_byte', 'rcpt_shard', 'rcpt_drop', 'rcpt_swap',
           'body_byte', 'rs_par', 'mrk_node', 'stmt_byte', 'fin_ro', 's384_pad', 'pub_claim', 'pub_n']


def main():
    args = sys.argv[1:]
    mutant = None
    if '--mutant' in args:
        i = args.index('--mutant')
        mutant = args[i + 1]
        args = args[:i] + args[i + 2:]
    dump, names, out = json.load(open(args[0])), json.load(open(args[1])), args[2]
    G = GenInit if 'CLM' in names['tables'] else Gen
    g = G(dump, names, mutant)
    info = g.run()
    if not g.applied:
        print('mutant %s: not applicable' % mutant)
        sys.exit(3)
    if mutant is not None:
        # the statement's public values are those of the honest run (the verifier's / leaf's view:
        # `claimDigest` from the public statement, the boundary digests from the neighbouring segment)
        h = G(dump, names, None)
        h.run()
        if G is GenInit or mutant.startswith('pub_'):
            g.stmt_pubs = h.stmt_pubs
    hts = g.write(out)
    print('GEN', json.dumps(info), 'tables', json.dumps(hts), 'sha_msgs', len(g.sha_msgs), 'comps', len(g.comps))


if __name__ == '__main__':
    main()
