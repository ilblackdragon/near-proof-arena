#!/usr/bin/env python3
"""E2E M5d trace generator (lane G): the FINAL template (class F1) of one chunk.

    tracegen.py DUMP_JSON NAMES_JSON OUT_DIR [--mutant NAME] [--template T.json] [--stats-only]

DUMP_JSON is `m5d-tool dump` (the Lean `allFeatures` checker's own `finK` + `tailNew` on the case);
NAMES_JSON is `m5d-tool air-final` (table and column names, class constants). Writes one `.bin`
per table (u32 log2 height, u32 width, row-major u32 cells), `sha_msgs.json` (SHA-256 messages),
`comps.json` (SHA-512 compressions, chip order), `pubs.bin` (public values the proof carries) and
`stmt_pubs.bin` (the statement's: for a mutant, those of the honest run). Exit code 3: the mutant
does not apply.

G-2 (`--template T.json`, `templates/*.json`): every table is written at the template's pinned
height (zero rows past the last filled row: every Lean table's activity is a prefix and its padding
rows are all-zero), and the dump carries `template.json` (the prover then pads `SHA` and the chip
to their pins and uses the template's parameters); exit code 4 if a table of this case (natural
height, one padding row kept) exceeds its pin. `--stats-only`: print the natural log heights
(every Lean table, `SHA`, `SHA512`) and write nothing (the census, `census.py`).

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


def lim8(b):
    """G-4: three little-endian limbs of 8 bytes (bytes 0..2, 3..5, 6..7), Lean `lim8`."""
    return [b[0] + 256 * b[1] + 65536 * b[2], b[3] + 256 * b[4] + 65536 * b[5], b[6] + 256 * b[7]]


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


class TemplateOverflow(Exception):
    """G-2: a table of this case exceeds the template's pinned height."""


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
        stream = bytearray(pre) + bytes(4) + post   # lane E's canonical S (StmtEnc)
        H = {'psr': 33, 'por': 65, 'emr': 97, 'el': 129, 'gu': 153, 'gl': 161, 'bb': 169, 'orr': 185,
             'txr': 217, 'props': 249, 'cong': 253, 'bw': 296, 'split': 301}
        # header (statement) mutants: one byte of each compared field of the public chunk header
        for k, o in H.items():
            if self.mut('hdr_' + k):
                stream[ci_off + o + (1 if k in ('props', 'cong', 'bw') else 0)] ^= 1
        stream = list(stream)
        assert len(pre) == C['PRE_LEN'] and len(stream) >= C['HBN']
        if self.mutant is None:
            print('claimDigest', hashlib.sha384(bytes(stream)).digest()[:42].hex(), file=sys.stderr)
        # -- FinIn ----------------------------------------------------------------------------
        root = list(bytes.fromhex(fin['root']))
        if self.mut('fin_root'):
            root[5] ^= 1
        cong = list(bytes.fromhex(fin['congestion']))
        if self.mut('fin_cong'):
            cong[3] ^= 1
        gas, bal, gl = int(fin['gasUsed']), int(fin['balanceBurnt']), int(fin['gasLimit'])
        gas_h, bal_h = gas, bal
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
        # B_out (G-2): ctxD(.header H) and outD(.done o)'s digest, = Lean's BOut on this case
        ci = stream[C['CI_OFF']:C['CI_OFF'] + 302]
        hd = self.s384(C['ID_HDR'], [C['TAG_HDR']] + ci)
        ob = (root + roots[C['TR_OUT']] + u(gl, 8) + u(gas, 8) + u(bal, 16) + roots[C['TR_SH']] + cong +
              [0] * 32 + roots[C['TR_RS']] + ci[129:137] + [0] * 9)
        assert len(ob) == 252
        if not self.mutant:
            assert bytes(ob).hex() == d['bout']['encOutputsF1'], 'encOutputsF1'
            assert bytes(hd[:42]).hex() == d['bout']['ctxHeaderD'], 'ctxHeaderD'
        od = self.s384(C['ID_OUT'], [C['TAG_OUT']] + ob)
        if not self.mutant:
            assert bytes(od[:42]).hex() == d['bout']['outDoneD'], 'outDoneD'
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
        F.setv(r, 'cd', cd); F.setv(r, 'fd', fd); F.setv(r, 'hd', hd); F.setv(r, 'od', od)
        if self.mut('bout_od'):
            F.rows[0][F.ix('od', 3)] ^= 1
        F.set(r, 'nO', len(leaves)); F.set(r, 'nR', len(rcpts)); F.set(r, 'lenC', len(stream))
        x = RSD * L - n
        self.look(self.r8, x); self.look(self.r8, x + 256 - RSD)
        if self.mut('fin_ro'):
            F.rows[0][F.ix('ro', 0)] ^= 1
        if self.mut('s384_pad'):
            # the bit-length byte of the first SHA-384 message's last block
            S3 = self.T['S384']
            S3.rows[0][S3.ix('b', 127)] ^= 1
        self.fill_rng()
        pubs = limbs3(cd[:42]) + limbs3(fd[:42]) + [n, L] + limbs3(hd[:42]) + limbs3(od[:42])
        # G-5: the clear counters of `done H o` (M12): big-endian `u64` gasUsed, `u128` balanceBurnt
        # (the boundary record's `natC` widths) = FinIn's little-endian bytes reversed
        assert len(pubs) == C['PV_GU']
        pubs += fi[75:83][::-1] + fi[83:99][::-1]
        assert len(pubs) == C['NUM_PUB']
        # the statement side (lane D's leaf): the header's own prev_gas_used / prev_balance_burnt
        stmt = list(pubs)
        stmt[C['PV_GU']:C['NUM_PUB']] = list(gas_h.to_bytes(8, 'big')) + list(bal_h.to_bytes(16, 'big'))
        if self.mut('pub_claim'):
            pubs[3] += 1
        if self.mut('pub_n'):
            pubs[28] += 1
        if self.mut('pub_hdr'):
            pubs[C['PV_HDR'] + 2] += 1
        if self.mut('pub_out'):
            pubs[C['PV_OUT'] + 5] += 1
        if self.mut('pub_gu'):
            pubs[C['PV_GU'] + 7] ^= 1
        if self.mut('pub_bb'):
            pubs[C['PV_BB'] + 15] ^= 1
        if self.mut('gu_le'):
            # the counter in FinIn's (little-endian) byte order, not the record's big-endian one
            pubs[C['PV_GU']:C['PV_BB']] = fi[75:83]
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

    SPARE = {'STMT', 'BODY', 'SEG', 'RS', 'PART', 'SHD', 'OUTL', 'MRK', 'BLK', 'LAY'}

    def natural(self):
        """[G-2] Log heights of every table: `nat` as `write` sizes them without a template, `fit`
        what a template pin must cover (every Lean table keeps one all-zero padding row, so its last
        row is inactive). `SHA` as the honest generator `sha256gen.rs` (1 + 17·blocks rows per
        message), the chip `SHA512` as `s384::trace::main_height` (128 rows per compression)."""
        lg = lambda h: (h - 1).bit_length()
        nat, fit = {}, {}
        for nm, T in self.T.items():
            nat[nm] = 8 if nm == 'RNG' else lg(T.height(spare=nm in self.SPARE))
            fit[nm] = 8 if nm == 'RNG' else lg(T.height(spare=True))
        if 'SHA' in self.names['tables']:
            rows = sum(1 + 17 * ((len(m['bytes']) // 2 + 9 + 63) // 64) for m in self.sha_msgs)
            nat['SHA'] = fit['SHA'] = lg(max(rows, 4))
        nat['SHA512'] = fit['SHA512'] = lg(max(128 * len(self.comps), 4))
        return nat, fit

    def write(self, out, tmpl=None):
        os.makedirs(out, exist_ok=True)
        heights = {}
        if tmpl is not None:
            _, fit = self.natural()
            pin = tmpl['heights']
            extra = sorted(set(pin) - set(fit))
            assert not extra, 'template pins tables the AIR does not have: %s' % extra
            over = ['%s: 2^%d > 2^%d' % (t, fit[t], pin.get(t, -1)) for t in fit if fit[t] > pin.get(t, -1)]
            if over:
                raise TemplateOverflow('; '.join(over))
            assert pin['RNG'] == 8, 'RNG is a fixed 2^8 table'
        for nm, T in self.T.items():
            h = 256 if nm == 'RNG' else T.height(spare=nm in self.SPARE)
            if tmpl is not None:
                h = 1 << tmpl['heights'][nm]
            T.dump(os.path.join(out, nm + '.bin'), h)
            heights[nm] = (len(T.rows), h)
        if tmpl is not None:
            json.dump(tmpl, open(os.path.join(out, 'template.json'), 'w'), indent=1)
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
        # G-2: the framing walk over section B (BLK) and the main slot's prev_state_root (INI)
        npre = len(pre)
        reads = set()
        B = self.T['BLK']
        def rd32(o):
            assert blocks[o + 3] == 0
            reads.update(range(npre + o, npre + o + 4))
            return blocks[o] + 256 * blocks[o + 1] + 65536 * blocks[o + 2], blocks[o:o + 4]
        def blkrow(kind, st, en, ys, rb, rs, bi, si):
            r = B.new()
            B.set(r, 'act', 1); B.set(r, kind, 1); B.set(r, 's', npre + st); B.set(r, 'e', npre + en)
            B.set(r, 'E', npre + len(blocks)); B.setv(r, 'y', ys + [0] * (12 - len(ys)))
            B.set(r, 'rb', rb); B.set(r, 'rs', rs)
            B.set(r, 'zr', int(rb == 0)); B.set(r, 'ir', pow(rb, P - 2, P) if rb else 0)
            B.set(r, 'zs', int(rs == 0)); B.set(r, 'is', pow(rs, P - 2, P) if rs else 0)
            B.set(r, 'bi', bi); B.set(r, 'si', si)
            sp = u(npre + st, 3); B.setv(r, 'sp', sp)
            for x in sp:
                self.look(self.r8, x)
        o = 0
        nblk, y = rd32(0)
        blkrow('kn', 0, 4, y, nblk, 0, 0, 0)
        o = 4
        slots, slotrow = {}, {}
        rb = nblk
        cbytes = pre + blocks + post
        self.hinc = {}
        def setz(r, at):
            # G-4: a block's height (inner_lite[0..8]) / a slot's height_included, 8 bytes at `at`
            z = cbytes[at:at + 8]
            B.setv(r, 'z', z)
            reads.update(range(at, at + 8))
            return lim8(z)
        for bi in range(nblk):
            st = o
            l1, y1 = rd32(o + 33)
            l2, y2 = rd32(o + 37 + l1)
            ns, y3 = rd32(o + 41 + l1 + l2)
            o = o + 45 + l1 + l2
            rb -= 1
            blkrow('kh', st, o, y1 + y2 + y3, rb, ns, bi + 1, 0)
            hb = setz(B.rows[-1], npre + st + 37)
            B.setv(B.rows[-1], 'hb', hb)
            rs = ns
            for si in range(ns):
                st = o
                ls, y0 = rd32(o)
                slots[(bi, si)] = (npre + o + 4, ls)
                slotrow[(bi, si)] = len(B.rows)
                o = o + 12 + ls
                rs -= 1
                blkrow('ks', st, o, y0, rb, rs, bi + 1, si + 1)
                hi = setz(B.rows[-1], npre + st + 4 + ls)
                B.setv(B.rows[-1], 'hb', hb)
                self.hinc[id(B.rows[-1])] = hi
        assert o == len(blocks), (o, len(blocks))
        # G-4: L.index shard from the single epoch's layout (LAY), the claim's shard id (INI)
        C = self.C
        post0 = npre + len(blocks)
        if cbytes[post0 + C['POST_NEP']:post0 + C['POST_NEP'] + 4] != [1, 0, 0, 0]:
            raise TemplateOverflow('INIT class E1: the epoch table has more than one epoch')
        reads.update(range(post0 + C['POST_NEP'], post0 + C['POST_NEP'] + 4))
        assert cbytes[C['P_CH'] + 3] == 0
        lc = cbytes[C['P_CH']] + 256 * cbytes[C['P_CH'] + 1] + 65536 * cbytes[C['P_CH'] + 2]
        reads.update(range(C['P_CH'], C['P_CH'] + 4))
        shp = lc + C['P_CI'] + C['CI_SHARD']
        shb = cbytes[shp:shp + 8]
        reads.update(range(shp, shp + 8))
        assert int.from_bytes(bytes(shb), 'little') == int(d['walk']['mainShard']), 'claim shard id'
        ix = self.lay_walk(cbytes, post0 + C['POST_LAY'], lim8(shb), reads)
        if self.mutant is None:
            assert ix == int(d['walk']['mainIdx']), ('layout index', ix, d['walk']['mainIdx'])
        b2i, mi = self.fill_sel(B, ix)
        if self.mutant is None:
            assert (b2i, mi) == (int(d['walk']['b2i']), int(d['walk']['mainIdx'])), 'walk selection'
        if self.mut('lbshift'):
            # a block vector re-framed one byte short: the walk's last end is |pre| + ℓ_B − 1
            last = B.rows[-1]
            last[B.ix('e')] -= 1
        if self.mut('psr_ix'):
            # a consistent walk for another main index (BLK, INI): LAY's first matching pair still
            # carries the true index
            ix = (ix + 1) % len([k for k in slots if k[0] == 0])
            b2i, mi = self.fill_sel(B, ix)
            for rr in self.T['LAY'].rows:
                rr[self.T['LAY'].ix('ix')] = ix
        if self.mut('sel_two'):
            # a second slot row selected as well (the first slot of the last block)
            other = slotrow[(nblk - 1, 0)]
            B.rows[other][B.ix('sel')] = 1
            self.regen_g(B)
        if self.mut('sel_none'):
            B.rows[slotrow[(b2i, mi)]][B.ix('sel')] = 0
            self.regen_g(B)
        sst, sln = slots[(b2i, mi)]
        selrow = slotrow[(b2i, mi)]
        psr = cbytes[sst + 33:sst + 65]
        if self.mutant is None:
            assert bytes(psr).hex() == d['walk']['slotPrevStateRoot'], 'slot prev_state_root'
        reads.update(range(sst + 33, sst + 65))
        for rr in T.rows[:len(cbytes)]:
            rr[T.ix('rd')] = int(rr[T.ix('kc')] in reads)
        if self.mut('clm_kind'):
            T.rows[len(pre) + 2][T.ix('kb')] = 0
            T.rows[len(pre) + 2][T.ix('kp')] = 1
        if self.mut('clm_byte'):
            T.rows[len(pre) + len(blocks) + 5][T.ix('b')] ^= 1
        stmt = pre + u(0, 4) + post   # lane E's canonical S (StmtEnc.encode_splice)
        cb = pre + blocks + post
        # G-5: big-endian u32 lengths (lane E's `ViewE.rawPre`, `u32 = beN 4`)
        ctx = [C['CTX_TAG']] + list(len(blocks).to_bytes(4, 'big')) + list(len(cb).to_bytes(4, 'big')) + cb + wit
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
        I.set(r, 'b2i', b2i); I.set(r, 'mi', mi); I.set(r, 'sst', sst); I.set(r, 'sln', sln)
        I.setv(r, 'slx', u(sln - 65, 3)); I.setv(r, 'psr', psr)
        I.setv(r, 'cy', cbytes[C['P_CH']:C['P_CH'] + 4]); I.setv(r, 'sh', shb)
        for v in u(sln - 65, 3):
            self.look(self.r8, v)
        if self.mut('psr_slot'):
            # another slot's prev_state_root (the walk picks b2i / mainIdx; here: the next slot)
            other = [k for k in slots if k != (b2i, mi)][0]
            sst2, sln2 = slots[other]
            B.rows[selrow][B.ix('sel')] = 0
            B.rows[slotrow[other]][B.ix('sel')] = 1
            r[I.ix('b2i')], r[I.ix('mi')] = other
            self.regen_g(B)
            Tc = self.T['CLM']
            for q in range(sst + 33, sst + 65):
                Tc.rows[q][Tc.ix('rd')] = 0
            for q in range(sst2 + 33, sst2 + 65):
                Tc.rows[q][Tc.ix('rd')] = 1
            r[I.ix('sst')] = sst2; r[I.ix('sln')] = sln2
            psr = (pre + blocks + post)[sst2 + 33:sst2 + 65]
            I.setv(r, 'psr', psr)
        if self.mut('ini_lb'):
            r[I.ix('lb', 0)] += 1
            r[I.ix('nb')] += 1
        self.fill_rng()
        pubs = limbs3(cd[:42]) + limbs3(xd[:42]) + [256 * psr[2 * t] + psr[2 * t + 1] for t in range(16)]
        self.pubs, self.stmt_pubs = pubs, list(pubs)
        if self.mut('pub_ctx'):
            self.pubs[20] += 1
        if self.mut('pub_psr'):
            self.pubs[30] += 1
        return dict(pre=len(pre), blocks=len(blocks), post=len(post), witness=len(wit), claimDigest=bytes(cd[:42]).hex(),
                    ctxRoot=bytes(xd[:42]).hex())



    def regen_g(self, B):
        """`g` = a slot selected on an earlier row (active rows), from the rows' `sel`."""
        g = 0
        for r in B.rows:
            B.set(r, 'g', g)
            g += r[B.ix('sel')]

    def fill_sel(self, B, ix):
        """G-4: BLK's main-slot selection for main index `ix` (`walkSegment` on a single-epoch
        segment): target slot rows, new target slots, the first one selected. Returns (b2i, mainIdx)."""
        g, pick = 0, None
        for r in B.rows:
            hi = self.hinc.get(id(r))
            B.set(r, 'ix', ix)
            ks = r[B.ix('ks')]
            si = r[B.ix('si')]
            tgt = int(ks == 1 and si - 1 == ix)
            B.set(r, 'tgt', tgt)
            B.set(r, 'itg', 0 if (not ks or tgt) else pow((si - 1 - ix) % P, P - 2, P))
            eq = 0
            dv = [0, 0, 0]
            if tgt:
                hb = [r[B.ix('hb', q)] for q in range(3)]
                ds = [(hi[q] - hb[q]) % P for q in range(3)]
                eq = int(all(x == 0 for x in ds))
                if not eq:
                    q = next(q for q in range(3) if ds[q])
                    dv[q] = pow(ds[q], P - 2, P)
            B.set(r, 'eq', eq); B.setv(r, 'dv', dv)
            sel = eq * (1 - g)
            B.set(r, 'sel', sel); B.set(r, 'g', g)
            if sel:
                pick = (r[B.ix('bi')] - 1, r[B.ix('si')] - 1)
            g += sel
        assert pick is not None, 'no new chunk for the main index'
        return pick

    def lay_walk(self, cb, p0, sh, reads):
        """G-4: the LAY rows over the layout bytes at `p0` (`decodeLayout` prefix up to the
        `id_to_index` pairs); returns `L.index shard` (the first pair with key = shard)."""
        A = self.T['LAY']
        u32 = lambda o: cb[o] + 256 * cb[o + 1] + 65536 * cb[o + 2] + 16777216 * cb[o + 3]
        rows = []
        def row(kind, st, en, nb, rb=0, rp=0):
            r = A.new()
            A.set(r, 'act', 1); A.set(r, kind, 1); A.set(r, 's', st); A.set(r, 'e', en)
            A.setv(r, 'y', cb[st:st + nb] + [0] * (16 - nb))
            reads.update(range(st, st + nb))
            A.set(r, 'rb', rb); A.set(r, 'rp', rp)
            A.set(r, 'zr', int(rb == 0)); A.set(r, 'ir', pow(rb, P - 2, P) if rb else 0)
            A.set(r, 'zp', int(rp == 0)); A.set(r, 'ip', pow(rp, P - 2, P) if rp else 0)
            A.setv(r, 'sh', sh)
            spb = u(st, 3); A.setv(r, 'sp', spb)
            for x in spb:
                self.look(self.r8, x)
            rows.append(r)
            return r
        assert cb[p0] in (2, 3), 'layout tag'
        nbd = u32(p0 + 1); assert cb[p0 + 4] == 0
        o = p0 + 5
        row('k0', p0, o, 5, rb=nbd)
        rb = nbd
        for _ in range(nbd):
            ln = u32(o); assert cb[o + 3] == 0
            rb -= 1
            row('kb', o, o + 4 + ln, 4, rb=rb)
            o += 4 + ln
        n = u32(o); assert cb[o + 3] == 0
        row('ki', o, o + 4 + 8 * n, 4)
        o += 4 + 8 * n
        m = u32(o); assert cb[o + 3] == 0
        row('km', o, o + 4, 4, rp=m)
        o += 4
        rp, g, ix = m, 0, None
        for _ in range(m):
            rp -= 1
            r = row('kp', o, o + 16, 16, rp=rp)
            key = lim8(cb[o:o + 8])
            ds = [(key[q] - sh[q]) % P for q in range(3)]
            eq = int(all(x == 0 for x in ds))
            dv = [0, 0, 0]
            if not eq:
                q = next(q for q in range(3) if ds[q]); dv[q] = pow(ds[q], P - 2, P)
            A.set(r, 'eq', eq); A.setv(r, 'dv', dv)
            hit = eq * (1 - g)
            A.set(r, 'hit', hit); A.set(r, 'g', g)
            if hit:
                assert cb[o + 9:o + 16] == [0] * 7, 'layout index >= 256'
                ix = cb[o + 8]
            g += hit
            o += 16
        assert ix is not None, 'shard not in layout'
        for r in rows:
            A.set(r, 'ix', ix)
        return ix

INIT_MUTANTS = ['pre_byte', 'blk_byte', 'wit_byte', 'clm_kind', 'clm_byte', 'ini_lb', 'pub_ctx',
                'lbshift', 'psr_slot', 'pub_psr', 'psr_ix', 'sel_two', 'sel_none']

MUTANTS = ['hdr_psr', 'hdr_por', 'hdr_emr', 'hdr_el', 'hdr_gu', 'hdr_gl', 'hdr_bb', 'hdr_orr', 'hdr_txr',
           'hdr_props', 'hdr_cong', 'hdr_bw', 'hdr_split',
           'fin_root', 'fin_cong', 'fin_gas', 'fin_bal', 'fin_gl',
           'leaf', 'outcome_drop', 'rcpt_byte', 'rcpt_shard', 'rcpt_drop', 'rcpt_swap',
           'body_byte', 'rs_par', 'mrk_node', 'stmt_byte', 'fin_ro', 's384_pad', 'pub_claim', 'pub_n',
           'bout_od', 'pub_hdr', 'pub_out', 'pub_gu', 'pub_bb', 'gu_le']


def main():
    args = sys.argv[1:]
    mutant = None
    if '--mutant' in args:
        i = args.index('--mutant')
        mutant = args[i + 1]
        args = args[:i] + args[i + 2:]
    tmpl = None
    if '--template' in args:
        i = args.index('--template')
        tmpl = json.load(open(args[i + 1]))
        args = args[:i] + args[i + 2:]
    stats_only = '--stats-only' in args
    args = [a for a in args if a != '--stats-only']
    dump, names, out = json.load(open(args[0])), json.load(open(args[1])), args[2]
    G = GenInit if 'CLM' in names['tables'] else Gen
    g = G(dump, names, mutant)
    try:
        info = g.run()
    except TemplateOverflow as e:
        print('TEMPLATE OVERFLOW (class): %s' % e)
        sys.exit(4)
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
    if stats_only:
        nat, fit = g.natural()
        print('STATS', json.dumps(dict(info=info, natural=nat, fit=fit, sha_msgs=len(g.sha_msgs), comps=len(g.comps))))
        return
    try:
        hts = g.write(out, tmpl)
    except TemplateOverflow as e:
        print('TEMPLATE OVERFLOW (%s): %s' % (tmpl.get('name'), e))
        sys.exit(4)
    print('GEN', json.dumps(info), 'tables', json.dumps(hts), 'sha_msgs', len(g.sha_msgs), 'comps', len(g.comps))


if __name__ == '__main__':
    main()
