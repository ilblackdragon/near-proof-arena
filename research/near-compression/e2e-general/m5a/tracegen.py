#!/usr/bin/env python3
"""M5a trace generator: INTAKE + working-set tree + FINAL for one transition's state accesses.

  tracegen.py STATE_JSON NAMES_JSON OUT_DIR [--mutant NAME]

STATE_JSON is `extract_state.py`'s output (pre-state root, the witness nodes the checker read, the
keys looked up, and the committed overlay at finalize, cross-checked against the Lean run).
NAMES_JSON is `m5a-tool air`'s column map.  OUT_DIR receives one `<TABLE>.bin` per Python-built
table (u32 log2 height, u32 width, row-major u32 cells), `sha_msgs.json` (the SHA-256 table's
messages, built into a trace by the prover), `comps.json` (the SHA-512 compressions, in chip
order), `tape.json` (the public messages) and `pubs.bin` (prev_state_root as 16 limbs).

The walks are the spec's own recursions (`ptrie.py`, a transcription of `PTrie.findRef`,
`PTrie.upsert`, `PTrie.del`, `applyChanges`); every row records the case it takes, and the result
root is checked against `ptrie.apply_changes` and the checker's post-state root before anything is
written.  A case without an AIR row (splits, absent deletes, …) raises `Unsupported`.

Mutants (`--mutant`), each a dishonest trace or statement the proof must reject:
  node      flip one byte of a revealed pre-state trie node (the walk then hashes a different node)
  prevalue  claim a wrong pre-value for one working-set key (its INTAKE find answer differs)
  omitwrite drop one write access from the trace (the public write log still lists it)
  postroot  state a wrong post-state root (the public tape's closing root)
"""
import hashlib
import json
import os
import struct
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import ptrie as PT  # noqa: E402
import sha512c as S5  # noqa: E402

P = 2013265921
ID_KEY, ID_BR, ID_SN = 1 << 24, 2 << 24, 3 << 24
W_FINAL = 1 << 20
RK_ANS, RK_H, RK_HB, RK_HE, RK_LD, RK_NONE = 0, 1, 2, 3, 4, 5
KMAX, HPMAX = 64, 33


class Unsupported(Exception):
    pass


def sha(b):
    return hashlib.sha256(b).digest()


def pack2(b32):
    return [256 * b32[2 * i] + b32[2 * i + 1] for i in range(16)]


def mem_limbs(m):
    return [(m >> (16 * k)) & 0xffff for k in range(4)]


def le(n, k):
    return list(n.to_bytes(k, 'little'))


class Table:
    def __init__(self, name, names):
        self.name = name
        self.cols = {}
        for i, nm in enumerate(names):
            self.cols[nm] = i
        self.width = len(names)
        self.rows = []

    def new(self):
        r = [0] * self.width
        self.rows.append(r)
        return r

    def ix(self, nm, j=None):
        return self.cols[nm if j is None else '%s.%d' % (nm, j)]

    def set(self, r, nm, v, j=None):
        r[self.ix(nm, j)] = v % P

    def setv(self, r, nm, vs):
        for j, v in enumerate(vs):
            r[self.ix(nm, j)] = v % P

    def get(self, r, nm, j=None):
        return r[self.ix(nm, j)]

    def dump(self, path, min_rows=4, exact=None):
        h = max(len(self.rows), min_rows)
        h = 1 << (h - 1).bit_length()
        if exact is not None:
            assert len(self.rows) == exact == h, (self.name, len(self.rows), exact)
        pad = self.pad_row if hasattr(self, 'pad_row') else None
        with open(path, 'wb') as f:
            f.write(struct.pack('<II', h.bit_length() - 1, self.width))
            for i in range(h):
                if i < len(self.rows):
                    row = self.rows[i]
                else:
                    row = pad(i) if pad else [0] * self.width
                f.write(struct.pack('<%dI' % self.width, *[x % P for x in row]))
        return h


class Gen:
    def __init__(self, st, names, mutant=None):
        self.names = names
        self.D = names['D']
        self.mutant = mutant
        self.T = {t: Table(t, names[t]) for t in ['KEY', 'BR', 'SN', 'KCMP', 'WSB', 'WSN', 'WSA']}
        self.sha_msgs = []
        self.comps = []
        self.nib_count = {}
        self.klen_count = {}
        self.store = {sha(bytes.fromhex(n)): bytes.fromhex(n) for n in st['nodes_read']}
        self.pre_root = bytes.fromhex(st['pre_root'])
        self.post_root = bytes.fromhex(st['post_root'])
        self.changes = [(bytes.fromhex(k), None if v is None else bytes.fromhex(v)) for k, v in st['changes']]
        self.keys = sorted(set(bytes.fromhex(k) for k in st['keys_read']) | set(k for k, _ in self.changes))
        self.keybytes = list(self.keys)          # kid -> key bytes (WS keys first, then extra keys)
        self.kid_of = {k: i for i, k in enumerate(self.keys)}
        self.op_census = {}

    # ------------------------------------------------------------------ keys
    def kid(self, key):
        if key not in self.kid_of:
            self.kid_of[key] = len(self.keybytes)
            self.keybytes.append(key)
        return self.kid_of[key]

    def nib(self, kid, idx):
        nibs = PT.nibbles(self.keybytes[kid])
        assert idx < len(nibs), ('nibble out of range', kid, idx)
        self.nib_count[(kid, idx)] = self.nib_count.get((kid, idx), 0) + 1
        return nibs[idx]

    def klen(self, kid, L):
        assert L == 2 * len(self.keybytes[kid]), ('klen', kid, L)
        self.klen_count[kid] = self.klen_count.get(kid, 0) + 1

    def sha_msg(self, mid, data):
        self.sha_msgs.append(dict(id=mid, bytes=data.hex()))

    def comp(self, h, block):
        cid = 128 * len(self.comps)
        self.comps.append(dict(h=[str(x) for x in h], block=[str(x) for x in block]))
        return cid, S5.compress(h, block)

    def census(self, op):
        self.op_census[op] = self.op_census.get(op, 0) + 1

    # ------------------------------------------------------------------ node rows
    def br_row(self, node, d, ctx, op):
        T = self.T['BR']
        r = T.new()
        rid = len(T.rows) - 1
        _, v, kids, m = node
        T.set(r, 'act', 1)
        T.set(r, 'rid', rid)
        T.set(r, 'w', ctx['w'])
        T.set(r, 'd', d)
        T.set(r, 'kid', ctx['kid'])
        T.set(r, ['mF', 'mU', 'mD'][ctx['mode']], 1)
        if op is not None:
            T.set(r, op, 1)
            self.census('BR.' + op)
        T.set(r, 'dvlen', ctx['vlen'])
        T.setv(r, 'dvh', pack2(ctx['vh']))
        hasv = 1 if v is not None else 0
        T.set(r, 'hasv', hasv)
        if v is not None:
            T.setv(r, 'vl', le(v[0], 4))
            T.setv(r, 'vh', list(v[1]))
        for i in range(16):
            if kids[i] is not None:
                T.set(r, 'f', 1, i)
                hb = PT.hash_of(kids[i])
                for b in range(32):
                    T.set(r, 'ch', hb[b], 32 * i + b)
        T.setv(r, 'mem', le(m, 8))
        ser = PT.serialize(node)
        ho = sha(ser)
        T.setv(r, 'ho', list(ho))
        self.sha_msg(ID_BR + 2 * rid, ser)
        n = self.nib(ctx['kid'], d)
        T.set(r, 'sel', 1, n)
        if op is None:
            return T, r, rid, n
        gdn = op in ('oFD', 'oUD', 'oDH', 'oDL', 'oDN', 'oD1')
        gnew = op in ('oUD', 'oUN', 'oDH', 'oDL', 'oDN')
        T.set(r, 'gdn', int(gdn))
        T.set(r, 'gnew', int(gnew))
        return T, r, rid, n

    def br_new(self, T, r, rid, node, new_node, nh, nm, om, op):
        """Fill the rewritten branch: flags, new child hash/mem, memory chain, digest."""
        _, v, kids, m = node
        _, v2, kids2, m2 = new_node
        assert v2 == v
        for i in range(16):
            T.set(r, 'nf', 1 if kids2[i] is not None else 0, i)
        if nh is not None:
            T.setv(r, 'nh', list(nh))
        T.setv(r, 'nm', mem_limbs(nm))
        T.setv(r, 'om', mem_limbs(om))
        T.setv(r, 'nmem', le(m2, 8))
        assert m2 == m + nm - om, (m2, m, nm, om)
        self.carries(T, r, mem_limbs(m), mem_limbs(nm), mem_limbs(om), mem_limbs(m2))
        ser = PT.serialize(new_node)
        hn = sha(ser)
        T.setv(r, 'hn', list(hn))
        self.sha_msg(ID_BR + 2 * rid + 1, ser)
        nkn = sum(1 for c in kids2 if c is not None)
        if op in ('oDH', 'oDL', 'oDN'):
            hasv = 1 if v is not None else 0
            T.set(r, 'inv1', pow(nkn, P - 2, P))
            if nkn != 1:
                T.set(r, 'inv2', (1 - hasv) * pow(nkn - 1, P - 2, P))
        return hn

    def carries(self, T, r, M, NMp, OMm, NM):
        cy = 0
        for k in range(4):
            t = M[k] + NMp[k] - OMm[k] + cy
            assert (t - NM[k]) % 65536 == 0
            cy = (t - NM[k]) // 65536
            assert cy in (-1, 0, 1)
            T.set(r, 'cy', cy, k)
        assert cy == 0

    def sn_row(self, node, d, ctx, op, kid, key):
        """A leaf / extension row (old node `node`, or None for a materialized leaf)."""
        T = self.T['SN']
        r = T.new()
        rid = len(T.rows) - 1
        T.set(r, 'act', 1)
        T.set(r, 'rid', rid)
        T.set(r, 'w', ctx['w'])
        T.set(r, 'd', d)
        T.set(r, 'kid', kid)
        if ctx.get('mode') is not None and op not in ('oLS', 'oLM'):
            T.set(r, ['mF', 'mU', 'mD'][ctx['mode']], 1)
        T.set(r, op, 1)
        self.census('SN.' + op)
        isL = op.startswith('oL')
        T.set(r, 'isL', int(isL))
        T.set(r, 'isE', int(not isL))
        T.set(r, 'gold', int(op != 'oLM'))
        T.set(r, 'gnew', int(op in ('oLR', 'oLM', 'oEU')))
        T.set(r, 'gdn', int(op in ('oEF', 'oEU', 'oED')))
        if len(key) > KMAX:
            raise Unsupported('key of %d nibbles in one node' % len(key))
        for j, x in enumerate(key):
            T.set(r, 'a', 1, j)
            T.set(r, 'k', x, j)
            got = self.nib(kid, d + j)
            assert got == x, ('key nibble', kid, d + j, got, x)
        if isL:
            self.klen(kid, d + len(key))
        T.set(r, 'klen', len(key))
        odd = len(key) % 2
        T.set(r, 'odd', odd)
        hp = PT.hex_prefix(key, isL)
        T.set(r, 'hplen', len(hp))
        for m_ in range(len(hp)):
            T.set(r, 'ha', 1, m_)
            T.set(r, 'hp', hp[m_], m_)
        if ctx.get('mode') is not None:
            T.set(r, 'dvlen', ctx['vlen'])
            T.setv(r, 'dvh', pack2(ctx['vh']))
        if node is not None:
            if isL:
                T.setv(r, 'x', le(node[2][0], 4) + list(node[2][1]))
            else:
                T.setv(r, 'x', list(PT.hash_of(node[2])))
            T.setv(r, 'mem', le(node[3], 8))
            ser = PT.serialize(node)
            T.setv(r, 'ho', list(sha(ser)))
            self.sha_msg(ID_SN + 2 * rid, ser)
        return T, r, rid

    def sn_new(self, T, r, rid, new_node):
        if new_node[0] == 'leaf':
            T.setv(r, 'nx', le(new_node[2][0], 4) + list(new_node[2][1]))
        else:
            T.setv(r, 'nx', list(PT.hash_of(new_node[2])))
        T.setv(r, 'nmem', le(new_node[3], 8))
        ser = PT.serialize(new_node)
        hn = sha(ser)
        T.setv(r, 'hn', list(hn))
        self.sha_msg(ID_SN + 2 * rid + 1, ser)
        return hn

    # ------------------------------------------------------------------ results (UP)
    @staticmethod
    def res(rk, h=None, nm=0, om=0, kid2=0, st2=0, alen=0, avh=None, fpres=0, node=None):
        return dict(rk=rk, h=h or bytes(32), nm=nm, om=om, kid2=kid2, st2=st2, alen=alen,
                    avh=avh or bytes(32), fpres=fpres, node=node)

    def put_child_up_br(self, T, r, op, cr):
        T.set(r, 'rk', cr['rk'])
        T.setv(r, 'om', mem_limbs(cr['om']))
        if op in ('oUD', 'oDH'):
            T.setv(r, 'nh', list(cr['h']))
            T.setv(r, 'nm', mem_limbs(cr['nm']))
        if op == 'oDL':
            T.set(r, 'kid2', cr['kid2'])
            T.set(r, 'st2', cr['st2'])
        if op in ('oFD', 'oDL'):
            T.set(r, 'lvlen', cr['alen'])
            T.setv(r, 'lvh', pack2(cr['avh']))
        if op == 'oFD':
            T.set(r, 'fpres', cr['fpres'])

    def put_child_up_sn(self, T, r, op, cr):
        T.set(r, 'rkc', cr['rk'])
        T.setv(r, 'uom', mem_limbs(cr['om']))
        if op == 'oEU':
            T.setv(r, 'unm', mem_limbs(cr['nm']))
        if op == 'oED':
            T.set(r, 'kid2', cr['kid2'])
        if op in ('oEF', 'oED'):
            T.set(r, 'alen', cr['alen'])
            T.setv(r, 'avh', pack2(cr['avh']))
        if op == 'oEF':
            T.set(r, 'fpres', cr['fpres'])

    def materialize(self, w, d, kid, vlen, vh):
        """`SN.oLM`: the leaf `K_kid[d..] ↦ (vlen, vh)`; returns (node, hash)."""
        key = PT.nibbles(self.keybytes[kid])[d:]
        node = ('leaf', key, (vlen, vh), PT.leaf_mem(key, vlen))
        T, r, rid = self.sn_row(None, d, dict(w=w), 'oLM', kid, key)
        T.set(r, 'dvlen', vlen)
        T.setv(r, 'dvh', pack2(vh))
        hn = self.sn_new(T, r, rid, node)
        return node, hn

    # ------------------------------------------------------------------ walks
    def walk(self, t, d, ctx):
        """One node of a walk; returns the spec result (`res`) with the rewritten subtree."""
        K = ctx['K']
        mode = ctx['mode']
        if t[0] == 'hash':
            raise Unsupported('unrevealed node on the path')
        if t[0] == 'branch':
            _, v, kids, m = t
            if d >= len(K):
                raise Unsupported('key ends at a branch')
            n = K[d]
            c = kids[n]
            if mode == 0:
                op = 'oFA' if c is None else 'oFD'
                T, r, rid, _ = self.br_row(t, d, ctx, op)
                if c is None:
                    return self.res(RK_ANS)
                cr = self.walk(c, d + 1, ctx)
                self.put_child_up_br(T, r, op, cr)
                return self.res(RK_ANS, alen=cr['alen'], avh=cr['avh'], fpres=cr['fpres'])
            if mode == 1:
                if c is None:
                    T, r, rid, _ = self.br_row(t, d, ctx, 'oUN')
                    leaf, lh = self.materialize(ctx['w'], d + 1, ctx['kid'], ctx['vlen'], ctx['vh'])
                    T.set(r, 'kid2', ctx['kid'])
                    T.set(r, 'st2', d + 1)
                    T.set(r, 'lvlen', ctx['vlen'])
                    T.setv(r, 'lvh', pack2(ctx['vh']))
                    T.set(r, 'rk', 0)
                    kids2 = list(kids)
                    kids2[n] = leaf
                    nn = ('branch', v, kids2, m + leaf[3])
                    T.setv(r, 'nh', list(lh))
                    hn = self.br_new(T, r, rid, t, nn, lh, leaf[3], 0, 'oUN')
                else:
                    T, r, rid, _ = self.br_row(t, d, ctx, 'oUD')
                    cr = self.walk(c, d + 1, ctx)
                    self.put_child_up_br(T, r, 'oUD', cr)
                    kids2 = list(kids)
                    kids2[n] = cr['node']
                    nn = ('branch', v, kids2, PT.nsub(m + cr['nm'], cr['om']))
                    hn = self.br_new(T, r, rid, t, nn, cr['h'], cr['nm'], cr['om'], 'oUD')
                return self.res(RK_H, h=hn, nm=nn[3], om=m, node=nn)
            # delete
            if c is None:
                raise Unsupported('delete of an absent key')
            T, r, rid, _ = self.br_row(t, d, ctx, None)   # the op depends on the child's result
            cr = self.walk(c, d + 1, ctx)
            kids2 = list(kids)
            if cr['rk'] in (RK_HB, RK_HE):
                op = 'oDH'
                kids2[n] = cr['node']
                nh, nm = cr['h'], cr['nm']
            elif cr['rk'] == RK_LD:
                op = 'oDL'
                leaf, nh = self.materialize(ctx['w'], d + 1, cr['kid2'], cr['alen'], cr['avh'])
                kids2[n] = leaf
                nm = leaf[3]
            else:
                kids2[n] = None
                nm, nh = 0, None
                rest = [(i, x) for i, x in enumerate(kids2) if x is not None]
                if len(rest) == 1 and v is None:
                    op = 'oD1'
                else:
                    op = 'oDN'
                    if not rest:
                        raise Unsupported('squash to empty / value leaf')
            T.set(r, op, 1)
            self.census('BR.' + op)
            T.set(r, 'gdn', 1)
            T.set(r, 'gnew', int(op != 'oD1'))
            self.put_child_up_br(T, r, op, cr)
            if op == 'oD1':
                i, sibn = rest[0]
                if sibn[0] != 'leaf':
                    raise Unsupported('squash onto a %s sibling' % sibn[0])
                T.set(r, 'sr', 1, i)
                # the sibling's full key: this node's path, i, the sibling's own key
                full = ctx['K'][:d] + [i] + sibn[1]
                if len(full) % 2:
                    raise Unsupported('odd sibling key')
                kid2 = self.kid(PT.pack_nibbles(full))
                assert self.nib(kid2, d) == i
                Ts, rs, rids = self.sn_row(sibn, d + 1, dict(w=ctx['w']), 'oLS', kid2, sibn[1])
                T.set(r, 'kid2', kid2)
                T.set(r, 'lvlen', sibn[2][0])
                T.setv(r, 'lvh', pack2(sibn[2][1]))
                return self.res(RK_LD, om=m, kid2=kid2, st2=d, alen=sibn[2][0], avh=sibn[2][1])
            if op == 'oDL':
                T.setv(r, 'nh', list(nh))
                T.setv(r, 'nm', mem_limbs(nm))
            nn = ('branch', v, kids2, m + nm - cr['om'])
            hn = self.br_new(T, r, rid, t, nn, nh, nm, cr['om'], op)
            return self.res(RK_HB, h=hn, nm=nn[3], om=m, node=nn)
        kid = ctx['kid']
        if t[0] == 'leaf':
            _, k, s, m = t
            if k != K[d:]:
                raise Unsupported('leaf key differs (absent find / split)')
            if mode == 0:
                self.sn_row(t, d, ctx, 'oLF', kid, k)
                return self.res(RK_ANS, alen=s[0], avh=s[1], fpres=1)
            if mode == 1:
                T, r, rid = self.sn_row(t, d, ctx, 'oLR', kid, k)
                nn = PT.new_leaf(k, (ctx['vlen'], ctx['vh']))
                hn = self.sn_new(T, r, rid, nn)
                return self.res(RK_H, h=hn, nm=nn[3], om=m, node=nn)
            self.sn_row(t, d, ctx, 'oLD', kid, k)
            return self.res(RK_NONE, om=m)
        # extension
        _, k, c, m = t
        if K[d:d + len(k)] != k:
            raise Unsupported('extension key differs (absent / split)')
        op = ['oEF', 'oEU', 'oED'][mode]
        T, r, rid = self.sn_row(t, d, ctx, op, kid, k)
        cr = self.walk(c, d + len(k), ctx)
        self.put_child_up_sn(T, r, op, cr)
        if mode == 0:
            return self.res(RK_ANS, alen=cr['alen'], avh=cr['avh'], fpres=cr['fpres'])
        if mode == 1:
            if PT.mem_of(c) is None:
                raise Unsupported('unrevealed extension child')
            nn = ('ext', k, cr['node'], PT.nsub(m + cr['nm'], cr['om']))
            T.setv(r, 'unm', mem_limbs(cr['nm']))
            self.carries(T, r, mem_limbs(m), mem_limbs(cr['nm']), mem_limbs(cr['om']), mem_limbs(nn[3]))
            hn = self.sn_new(T, r, rid, nn)
            return self.res(RK_H, h=hn, nm=nn[3], om=m, node=nn)
        if cr['rk'] != RK_LD:
            raise Unsupported('delete under an extension with a %d child result' % cr['rk'])
        for j, x in enumerate(k):
            assert self.nib(cr['kid2'], d + j) == x
        return self.res(RK_LD, om=m, kid2=cr['kid2'], st2=d, alen=cr['alen'], avh=cr['avh'])

    # ------------------------------------------------------------------ the run
    def run(self):
        st_pre = PT.reveal_all(self.store, self.pre_root)
        assert PT.hash_of(st_pre) == self.pre_root
        n = len(self.keys)
        N = 1 << self.D
        assert n <= N, 'working set of %d keys needs a deeper tree' % n
        # ---- INTAKE: find walks
        pre = {}
        for i, key in enumerate(self.keys):
            ctx = dict(w=i, kid=i, mode=0, K=PT.nibbles(key), vlen=0, vh=bytes(32))
            res = self.walk(st_pre, 0, ctx)
            pre[key] = (res['fpres'], res['alen'], res['avh'])
            f = PT.find(st_pre, PT.nibbles(key))
            want = (0, 0, bytes(32)) if f == ('absent',) else (1, f[1][0], f[1][1])
            assert pre[key] == want, key.hex()
        if self.mutant == 'prevalue':
            k0 = self.keys[0]
            p0 = pre[k0]
            pre[k0] = (p0[0], p0[1] + 1, p0[2]) if p0[0] else (1, 1, sha(b'x'))
        # ---- FINAL: change walks in key order
        chg = dict(self.changes)
        cur = st_pre
        roots = [self.pre_root]
        final = {}
        for i, key in enumerate(self.keys):
            if key not in chg:
                continue
            v = chg[key]
            ref = (1, len(v), sha(v)) if v is not None else (0, 0, bytes(32))
            final[key] = ref
            ctx = dict(w=W_FINAL + i, kid=i, mode=1 if v is not None else 2, K=PT.nibbles(key),
                       vlen=ref[1], vh=ref[2])
            res = self.walk(cur, 0, ctx)
            if res['rk'] not in (RK_H, RK_HB, RK_HE):
                raise Unsupported('root result %d' % res['rk'])
            cur = res['node']
            roots.append(res['h'])
        spec_t, _ = PT.apply_changes(st_pre, [(k, None if v is None else (len(v), sha(v))) for k, v in self.changes])
        assert PT.root_hash(spec_t) == roots[-1] == self.post_root, 'post-state root'
        self.roots = roots
        self.pre, self.final = pre, final
        self.build_ws()
        self.build_kcmp()
        self.build_keys()

    # ------------------------------------------------------------------ working set
    def leaf_words(self, kd, pre, cur, wr):
        kdl, pvl, cvl = pack2(kd), pack2(pre[2]), pack2(cur[2])
        hi = [pre[0], pre[1], cur[0], cur[1], wr, 0, 0, 0]
        ws = [(kdl[2 * t], kdl[2 * t + 1], hi[t]) for t in range(8)]
        ws += [(pvl[2 * t], pvl[2 * t + 1], 0) for t in range(8)]
        ws += [(cvl[2 * t], cvl[2 * t + 1], 0) for t in range(8)]
        ws += [(0, 0, 0)] * 8
        return [S5.word(*x) for x in ws]

    def leaf_hash(self, words):
        c1, mid = self.comp(S5.IV384, words[:16])
        c2, out = self.comp(mid, words[16:])
        return c1, c2, mid, out

    def node_hash(self, l6, r6):
        blk = list(l6) + list(r6) + [1 << 63, 0, 0, 768]
        cid, out = self.comp(S5.IV384, blk)
        return cid, out

    @staticmethod
    def l18(ws):
        return [x for w in ws for x in S5.limbs(w)]

    def build_ws(self):
        D, N = self.D, 1 << self.D
        n = len(self.keys)
        kd = {k: sha(k) for k in self.keys}
        leaves0 = []
        for k in self.keys:
            p = self.pre[k]
            leaves0.append((kd[k], p, p, 0))
        leaves1 = []
        for k in self.keys:
            p = self.pre[k]
            if k in self.final:
                leaves1.append((kd[k], p, self.final[k], 1))
            else:
                leaves1.append((kd[k], p, p, 0))
        Tb = self.T['WSB']
        dig = {0: [], 1: []}
        for ph, leaves in ((0, leaves0), (1, leaves1)):
            j = 0
            for i in range(N):
                r = Tb.new()
                Tb.set(r, 'ph', ph)
                Tb.set(r, 'i', i)
                Tb.set(r, 'e', int(i == N - 1))
                Tb.set(r, 'j', j)
                if i < n:
                    kdi, p, c, wr = leaves[i]
                    Tb.set(r, 'real', 1)
                    Tb.set(r, 'kid', i)
                    Tb.setv(r, 'kd', pack2(kdi))
                    Tb.set(r, 'pp', p[0]); Tb.set(r, 'pl', p[1]); Tb.setv(r, 'pv', pack2(p[2]))
                    Tb.set(r, 'cp', c[0]); Tb.set(r, 'cl', c[1]); Tb.setv(r, 'cv', pack2(c[2]))
                    Tb.set(r, 'wr', wr)
                    c1, c2, mid, out = self.leaf_hash(self.leaf_words(kdi, p, c, wr))
                    Tb.set(r, 'cid1', c1); Tb.set(r, 'cid2', c2)
                    Tb.setv(r, 'mid', self.l18(mid))
                    Tb.setv(r, 'dg', self.l18(out[:6]))
                    Tb.setv(r, 'dx', self.l18(out[6:]))
                    dig[ph].append(out[:6])
                    if ph == 0 and i + 1 < n:
                        Tb.set(r, 'so', 1)
                    if ph == 1 and wr:
                        Tb.setv(r, 'rin', pack2(self.roots[j]))
                        Tb.setv(r, 'rout', pack2(self.roots[j + 1]))
                        Tb.set(r, 'rk', self.root_rk[j])
                        Tb.setv(r, 'rnm', mem_limbs(self.root_mem[j][0]))
                        Tb.setv(r, 'rom', mem_limbs(self.root_mem[j][1]))
                        j += 1
                else:
                    dig[ph].append([0] * 6)
        # inner nodes, and the path state for the write accesses
        Tn = self.T['WSN']
        self.nw = len(self.final)

        def build(ph, leafd):
            lv = [list(x) for x in leafd]
            levels = [lv]
            for l in range(D):
                nxt = []
                for idx in range(len(lv) // 2):
                    r = Tn.new()
                    Tn.set(r, 'act', 1); Tn.set(r, 'ph', ph); Tn.set(r, 'lvl', l); Tn.set(r, 'idx', idx)
                    top = int(l == D - 1)
                    Tn.set(r, 'top', top)
                    Tn.setv(r, 'l', self.l18(lv[2 * idx])); Tn.setv(r, 'r', self.l18(lv[2 * idx + 1]))
                    cid, out = self.node_hash(lv[2 * idx], lv[2 * idx + 1])
                    Tn.set(r, 'cid', cid)
                    Tn.setv(r, 'o', self.l18(out[:6])); Tn.setv(r, 'ox', self.l18(out[6:]))
                    if top and ph == 1:
                        Tn.set(r, 'nw', self.nw)
                    nxt.append(out[:6])
                lv = nxt
                levels.append(lv)
            return levels

        build(0, dig[0])
        # write accesses: the tree evolves leaf by leaf from phase 0 to phase 1
        Ta = self.T['WSA']
        state = [list(x) for x in leaves0]
        digs = [list(x) for x in dig[0]]
        jj = 0
        for i, k in enumerate(self.keys):
            if k not in self.final:
                continue
            r = Ta.new()
            Ta.set(r, 'act', 1)
            Ta.set(r, 'jj', jj)
            kdi, p, c, wr = state[i]
            nc = self.final[k]
            Ta.setv(r, 'kd', pack2(kdi))
            Ta.set(r, 'pp', p[0]); Ta.set(r, 'pl', p[1]); Ta.setv(r, 'pv', pack2(p[2]))
            Ta.set(r, 'cp', c[0]); Ta.set(r, 'cl', c[1]); Ta.setv(r, 'cv', pack2(c[2]))
            Ta.set(r, 'wr', wr)
            Ta.set(r, 'ncp', nc[0]); Ta.set(r, 'ncl', nc[1]); Ta.setv(r, 'ncv', pack2(nc[2]))
            cO1, cO2, midO, outO = self.leaf_hash(self.leaf_words(kdi, p, c, wr))
            cN1, cN2, midN, outN = self.leaf_hash(self.leaf_words(kdi, p, nc, 1))
            Ta.setv(r, 'cidL', [cO1, cO2, cN1, cN2])
            Ta.setv(r, 'midO', self.l18(midO)); Ta.setv(r, 'dgO', self.l18(outO[:6])); Ta.setv(r, 'dxO', self.l18(outO[6:]))
            Ta.setv(r, 'midN', self.l18(midN)); Ta.setv(r, 'dgN', self.l18(outN[:6])); Ta.setv(r, 'dxN', self.l18(outN[6:]))
            assert digs[i] == outO[:6]
            # path
            lv = digs
            levels = [lv]
            for l in range(D):
                lv = [None] * (len(lv) // 2)
                levels.append(lv)
            # recompute the current tree levels (old)
            cur_levels = [list(digs)]
            for l in range(D):
                prev = cur_levels[-1]
                cur_levels.append([S5.compress(S5.IV384, list(prev[2 * x]) + list(prev[2 * x + 1]) +
                                               [1 << 63, 0, 0, 768])[:6] for x in range(len(prev) // 2)])
            idx = i
            curO, curN = outO[:6], outN[:6]
            for l in range(D):
                side = idx & 1
                sib = cur_levels[l][idx ^ 1]
                Ta.set(r, 'side', side, l)
                for t, x in enumerate(self.l18(sib)):
                    Ta.set(r, 'sib', x, 18 * l + t)
                lo, ro = (sib, curO) if side else (curO, sib)
                ln, rn = (sib, curN) if side else (curN, sib)
                co, outPO = self.node_hash(lo, ro)
                cn, outPN = self.node_hash(ln, rn)
                Ta.set(r, 'cO', co, l); Ta.set(r, 'cN', cn, l)
                for t, x in enumerate(self.l18(outPO[:6])):
                    Ta.set(r, 'pO', x, 18 * l + t)
                for t, x in enumerate(self.l18(outPO[6:])):
                    Ta.set(r, 'xO', x, 6 * l + t)
                for t, x in enumerate(self.l18(outPN[:6])):
                    Ta.set(r, 'pN', x, 18 * l + t)
                for t, x in enumerate(self.l18(outPN[6:])):
                    Ta.set(r, 'xN', x, 6 * l + t)
                curO, curN = outPO[:6], outPN[:6]
                idx >>= 1
            state[i] = (kdi, p, nc, 1)
            digs[i] = outN[:6]
            jj += 1
        assert digs == [list(x) for x in dig[1]]
        build(1, dig[1])
        if self.mutant == 'omitwrite':
            # the dishonest prover leaves one write access out of the trace
            Ta.rows.pop(0)

    # ------------------------------------------------------------------ keys and order
    def build_keys(self):
        T = self.T['KEY']
        for kid, key in enumerate(self.keybytes):
            dg = sha(key)
            self.sha_msg(ID_KEY + kid, key)
            for j, b in enumerate(key):
                r = T.new()
                T.set(r, 'kid', kid); T.set(r, 'j', j)
                hi, lo = b >> 4, b & 15
                T.set(r, 'hi', hi); T.set(r, 'lo', lo)
                for t in range(4):
                    T.set(r, 'hib', (hi >> t) & 1, t)
                    T.set(r, 'lob', (lo >> t) & 1, t)
                T.set(r, 'act', 1)
                T.set(r, 'first', int(j == 0))
                last = j == len(key) - 1
                T.set(r, 'last', int(last))
                for nm, cnt in (('mh', self.nib_count.get((kid, 2 * j), 0)),
                                ('ml', self.nib_count.get((kid, 2 * j + 1), 0))):
                    assert cnt < 16, ('lookup count', kid, j, cnt)
                    for t in range(4):
                        T.set(r, nm, (cnt >> t) & 1, t)
                if last:
                    cl = self.klen_count.get(kid, 0)
                    cd = 2 if kid < len(self.keys) else 0
                    assert cl < 16
                    for t in range(4):
                        T.set(r, 'mlen', (cl >> t) & 1, t)
                        T.set(r, 'mdig', (cd >> t) & 1, t)
                    T.setv(r, 'dg', list(dg))
        used = set(k for k, _ in self.nib_count) | set(self.klen_count)
        for (kid, idx) in self.nib_count:
            assert idx < 2 * len(self.keybytes[kid])

    def build_kcmp(self):
        T = self.T['KCMP']
        for a in range(len(self.keys) - 1):
            ka, kb = PT.nibbles(self.keys[a]), PT.nibbles(self.keys[a + 1])
            p = 0
            while p < len(ka) and p < len(kb) and ka[p] == kb[p]:
                p += 1
            assert p < len(kb) and (p == len(ka) or ka[p] < kb[p])
            for j in range(p + 1):
                r = T.new()
                T.set(r, 'act', 1); T.set(r, 'first', int(j == 0)); T.set(r, 'ka', a); T.set(r, 'kb', a + 1)
                T.set(r, 'j', j)
                if j < p:
                    T.set(r, 'x', ka[j])
                    self.nib(a, j); self.nib(a + 1, j)
                else:
                    T.set(r, 'fin', 1)
                    T.set(r, 'xb', kb[p]); self.nib(a + 1, p)
                    if p == len(ka):
                        T.set(r, 'pre', 1); self.klen(a, p)
                    else:
                        T.set(r, 'xa', ka[p]); self.nib(a, p)
                        T.setv(r, 'db', [((kb[p] - ka[p] - 1) >> t) & 1 for t in range(4)])

    # ------------------------------------------------------------------ output
    def write(self, out):
        os.makedirs(out, exist_ok=True)
        heights = {}
        for nm, T in self.T.items():
            if nm == 'WSB':
                heights[nm] = T.dump(os.path.join(out, nm + '.bin'), exact=2 << self.D)
            else:
                if nm in ('BR', 'SN'):
                    w = T.width
                    rid_i = T.ix('rid')
                    n0 = len(T.rows)
                    T.pad_row = (lambda rid_i, w: (lambda i: [i if c == rid_i else 0 for c in range(w)]))(rid_i, w)
                heights[nm] = T.dump(os.path.join(out, nm + '.bin'))
        json.dump(self.sha_msgs, open(os.path.join(out, 'sha_msgs.json'), 'w'))
        json.dump(self.comps, open(os.path.join(out, 'comps.json'), 'w'))
        pubs = pack2(self.pre_root)
        with open(os.path.join(out, 'pubs.bin'), 'wb') as f:
            f.write(struct.pack('<16I', *pubs))
        tape = []
        for key, ref in sorted(self.final.items()):
            tape.append([13, True, pack2(sha(key)) + [ref[0], ref[1]] + pack2(ref[2])])
        post = self.post_root
        if self.mutant == 'postroot':
            post = bytes([post[0] ^ 1]) + post[1:]
        tape.append([14, True, [0] + pack2(self.pre_root)])
        tape.append([14, False, [len(self.final)] + pack2(post)])
        json.dump(tape, open(os.path.join(out, 'tape.json'), 'w'))
        stats = dict(heights=heights, sha_msgs=len(self.sha_msgs),
                     sha_blocks=sum((len(m['bytes']) // 2 + 9 + 63) // 64 for m in self.sha_msgs),
                     compressions=len(self.comps), keys=len(self.keybytes), ws_keys=len(self.keys),
                     changes=len(self.final), rows={k: len(T.rows) for k, T in self.T.items()},
                     ops=self.op_census, pre_root=self.pre_root.hex(), post_root=self.roots[-1].hex())
        json.dump(stats, open(os.path.join(out, 'stats.json'), 'w'), indent=1)
        return stats


def main():
    st = json.load(open(sys.argv[1]))
    names = json.load(open(sys.argv[2]))
    out = sys.argv[3]
    mutant = None
    if len(sys.argv) > 5 and sys.argv[4] == '--mutant':
        mutant = sys.argv[5]
    g = Gen(st, names, mutant)
    if mutant == 'node':
        # A tampered pre-state node: the leaf of the first written key carries memory usage + 1
        # (still a well-formed node), while its parent keeps the true child hash.  Every row that
        # visits the leaf holds and hashes the tampered content.
        orig_reveal = PT.reveal_all
        k0 = g.changes[0][0]

        def reveal(store, h, fuel=10000):
            t = orig_reveal(store, h, fuel)
            return tamper(t, PT.nibbles(k0), 0)

        def tamper(t, K, d):
            if t[0] == 'leaf':
                bad = ('leaf', t[1], t[2], t[3] + 1)
                PT.OVERRIDE[id(bad)] = PT.hash_of(t)
                return bad
            if t[0] == 'ext':
                return ('ext', t[1], tamper(t[2], K, d + len(t[1])), t[3])
            kids = list(t[2])
            kids[K[d]] = tamper(kids[K[d]], K, d + 1)
            return ('branch', t[1], kids, t[3])
        PT.reveal_all = reveal
    g.root_rk, g.root_mem = [], []
    orig_walk = g.walk

    def walk(t, d, ctx):
        r = orig_walk(t, d, ctx)
        if d == 0 and ctx['mode'] != 0:
            g.root_rk.append(r['rk'])
            g.root_mem.append((r['nm'], r['om']))
        return r
    g.walk = walk
    g.run()
    stats = g.write(out)
    print(json.dumps(dict((k, stats[k]) for k in ('rows', 'heights', 'sha_msgs', 'sha_blocks', 'compressions', 'ops'))))


if __name__ == '__main__':
    main()
