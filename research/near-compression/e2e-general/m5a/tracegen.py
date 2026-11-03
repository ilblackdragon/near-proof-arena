#!/usr/bin/env python3
"""M5a trace generator: INTAKE + working-set tree + FINAL for one transition's state accesses.

  tracegen.py STATE_JSON NAMES_JSON OUT_DIR [--mutant NAME] [--segs S] [--extra-writes N]

STATE_JSON is `extract_state.py`'s output (pre-state root, the witness nodes the checker read, the
keys looked up, and the committed overlay at finalize, cross-checked against the Lean run).
NAMES_JSON is `m5a-tool air`'s column map.  OUT_DIR receives one `<TABLE>.bin` per Python-built
table (u32 log2 height, u32 width, row-major u32 cells), `sha_msgs.json` (the SHA-256 table's
messages, built into a trace by the prover), `comps.json` (the SHA-512 compressions, in chip
order), `tape.json` (the public messages) and `pubs.bin` (prev_state_root as 16 limbs, then the working-set entry count `wsLen`).

The walks are the spec's own recursions (`ptrie.py`, a transcription of `PTrie.findRef`,
`PTrie.upsert`, `PTrie.del`, `applyChanges`); every row records the case it takes, and the result
root is checked against `ptrie.apply_changes` and the checker's post-state root before anything is
written.  A case without an AIR row (splits, absent deletes, …) raises `Unsupported`.

Mutants (`--mutant`), each a dishonest trace or statement the proof must reject:
  node      flip one byte of a revealed pre-state trie node (the walk then hashes a different node)
  prevalue  claim a wrong pre-value for one working-set key (its INTAKE find answer differs)
  omitwrite drop one write access from the trace (the public write log still lists it)
  postroot  state a wrong post-state root (the public tape's closing root)
Row-level mutants (one row of a T2 row type tampered after generation, `TAMPERS`):
  absent    a present-key leaf find (`oLF`) rewritten as an absent find with a fake mismatch
  extabsent an absent extension find (`oEA`) claiming one more matching nibble
  branchval a find ending at a branch (`oFV`) answering "no value"
  split     a split's new branch (`oSL`) placing the old-side child at another slot
  splitext  an extension split (`oEX`) with the child's usage `cm` + 1
  absdel    an absent delete at a leaf (`oLZ`) claiming a mismatch where the nibbles agree
  squash    an extension over a kept branch (`oEB`) with its memory usage + 1
  chain     a continuation row (`SNC`) holding another nibble (its hp byte adjusted)
Batched-FINAL mutants (M5a-2: in-memory node versions on `VER`):
  verslot   a row reading an in-memory version holds another off-path child (one slot byte)
  vernid    a row reading an in-memory version claims another version's id (a stale / foreign read)
  vmcount   a pre-state node's hashing row publishes it for one reader more than read it
  finroot   the last change leaves the root in memory (a version id) instead of hashing it
  nidforge  a version published under another row's version id
Working-set count mutants (M5a-5: `wsLen` is public value 16):
  wslen     the statement claims one working-set entry more than the trace has (a padding leaf
            would have to count as real)
  wslenlo   the statement claims one entry fewer (the last real leaf would have to be padding)
Branch-value mutants (synthetic case `bval`):
  bvalue    a branch-value write (`oUV`) storing another value-hash byte than the walk's value
  bvmem     a branch-value delete (`oDV`) with memory usage + 1
Working-set segment mutants (M5a-3: write accesses on the `WM` memory chain, batched path update):
  wsstale   a write access consumes another value than the entry's latest
  wsorder   two accesses to one entry chained in the wrong time order (needs --extra-writes)
  wsseg     a write access attributed to another segment than the write log's (needs --segs ≥ 2)
  wssib     a segment path node changes an untouched sibling between the old and the new tree
  wsdrop    a segment path node that receives no touched child
  wsabsorb  an inactive path-node row absorbs a touched child without hashing it
  wsleaf    a touched leaf claims another pre-value length (consistently hashed)

Options: --segs S cuts the write log into S segments (default 1: the whole M5a write tape is one
STATE segment); --extra-writes N writes an intermediate value to each of the first N written keys
before its final one (exercises the memory chain).
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
RK_ANS, RK_H, RK_HB, RK_HE, RK_LD, RK_NONE, RK_SAME = 0, 1, 2, 3, 4, 5, 6
KMAX, HPMAX = 64, 33
VBITS = 7
# ops that read a node version and leave it in place (`del` returned `deleted = false`)
SAME_OPS = {'BR.oDA', 'BR.oDS', 'BR.oDZ', 'SN.oLZ', 'SN.oEZ', 'SN.oES'}


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
    def __init__(self, st, names, mutant=None, plan=None, segs=1, extra_writes=0):
        self.segs, self.extra_writes = segs, extra_writes
        # Batched FINAL: `plan` (from a first pass, `make_plan`) says, for every node version,
        # whether it is published under a version id (`nref`: rewritten by a later change) or
        # hashed (final), how many rows read it, and which row hashes each pre-state node.
        # `plan = None` is the first pass: every old node hashed, every new node final.
        self.plan = plan
        self.ver = {}        # id(node) -> ('new', table, rid) for nodes the rows produced
        self.keep = []       # keeps produced nodes alive (their ids are keys of `ver`)
        self.reads = []      # (version key, table, rid, cont)
        self.prod_cont = {}  # version key -> produced by a row with a continued key
        self.names = names
        self.D = names['D']
        self.mutant = mutant
        self.T = {t: Table(t, names[t]) for t in ['KEY', 'BR', 'SN', 'KCMP', 'WSB', 'WSN', 'WSA', 'SNC', 'RNG', 'WSL', 'WSP']}
        self.rng_count = {}
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

    def rng(self, v):
        assert 0 <= v < 256, ('range', v)
        self.rng_count[v] = self.rng_count.get(v, 0) + 1

    # ------------------------------------------------------------------ versions (batched FINAL)
    def vkey(self, node):
        k = self.ver.get(id(node))
        return k if k is not None else ('pre', PT.hash_of(node))

    @staticmethod
    def nid(tbl, rid):
        return (ID_BR if tbl == 'BR' else ID_SN) + 2 * rid + 1

    def is_vid(self, k):
        return self.plan is not None and k[0] == 'new' and self.plan['nref'].get(k, 0) == 1

    def ref(self, node):
        """A node's ref `(flag, 32 cells)`: its version id (flag 1, cell 0) or its digest."""
        k = self.ver.get(id(node))
        if k is not None and self.is_vid(k):
            return 1, [self.nid(k[1], k[2])] + [0] * 31
        return 0, list(PT.hash_of(node))

    def set_ref(self, T, r, col, fcol, ref):
        T.setv(r, col, ref[1])
        T.set(r, fcol, ref[0])

    @staticmethod
    def set_bits(T, r, col, n):
        assert 0 <= n < 1 << VBITS, ('version readers', n)
        for t in range(VBITS):
            T.set(r, col, (n >> t) & 1, t)

    def old_ref(self, T, r, tbl, rid, node, cont):
        """The row's old node: hashed here (`gsha`, published for `vm` other readers) or read from
        `VER` by its ref.  Sets `gsha`, `oref`, `vm`, `ho`; returns the ref."""
        k = self.vkey(node)
        self.reads.append((k, tbl, rid, cont))
        vm = 0
        if self.plan is None or cont:
            gsha = True
            assert not self.is_vid(k), 'a continued key under a version id'
        elif k[0] == 'pre':
            pt, pr, cnt = self.plan['prov'][k]
            gsha = (pt, pr) == (tbl, rid)
            vm = cnt if gsha else 0
        else:
            gsha = False
        T.set(r, 'gsha', int(gsha))
        self.set_bits(T, r, 'vm', vm)
        if gsha:
            ser = PT.serialize(node)
            ref = (0, list(sha(ser)))
            self.sha_msg((ID_BR if tbl == 'BR' else ID_SN) + 2 * rid, ser)
        else:
            ref = self.ref(node)
        self.set_ref(T, r, 'ho', 'oref', ref)
        return ref

    def new_ref(self, T, r, tbl, rid, node, cont):
        """The row's new node: published under its version id (`nref`) or hashed (final); `vmn`
        readers.  Registers the version; sets `nref`, `vmn`, `hn`; returns the ref."""
        k = ('new', tbl, rid)
        self.ver[id(node)] = k
        self.keep.append(node)
        self.prod_cont[k] = cont
        vmn = 0 if self.plan is None else self.plan['vmn'].get(k, 0)
        if self.is_vid(k):
            ref = (1, [self.nid(tbl, rid)] + [0] * 31)
            for x in le(node[3], 8):     # an unhashed node's memory bytes are range-checked
                self.rng(x)
        else:
            # a final node's children must be final (digests)
            kids = node[2] if node[0] == 'branch' else ([node[2]] if node[0] == 'ext' else [])
            for ch in kids:
                if ch is not None and self.ref(ch)[0] == 1:
                    raise Unsupported('final node over an in-memory child (continued key)')
            ser = PT.serialize(node)
            ref = (0, list(sha(ser)))
            self.sha_msg((ID_BR if tbl == 'BR' else ID_SN) + 2 * rid + 1, ser)
        self.set_bits(T, r, 'vmn', vmn)
        self.set_ref(T, r, 'hn', 'nref', ref)
        return ref

    @staticmethod
    def own_ref(T, r):
        return T.get(r, 'oref'), [T.get(r, 'ho', b) for b in range(32)]

    def make_plan(self):
        """From a first pass: version ids for nodes a later change rewrites, reader counts, and the
        row that hashes each pre-state node (its first reader)."""
        ops = {}
        for tbl, opl in (('BR', ['oFD', 'oFA', 'oUD', 'oUN', 'oDH', 'oDL', 'oDN', 'oD1', 'oFV', 'oDA',
                                 'oDS', 'oSL', 'oUV', 'oDV', 'oDZ']),
                         ('SN', ['oLF', 'oLR', 'oLD', 'oLS', 'oLM', 'oEF', 'oEU', 'oED', 'oLA', 'oEA',
                                 'oLZ', 'oEZ', 'oES', 'oEB', 'oLX', 'oEX', 'oEP', 'oEM'])):
            T = self.T[tbl]
            for rid, row in enumerate(T.rows):
                ops[(tbl, rid)] = tbl + '.' + next(o for o in opl if T.get(row, o) == 1)
        by = {}
        for k, tbl, rid, cont in self.reads:
            by.setdefault(k, []).append((tbl, rid, cont, ops[(tbl, rid)]))
        prov, nref, vmn = {}, {}, {}
        for k, rs in by.items():
            if k[0] == 'pre':
                nc = [(t, r) for t, r, c, _ in rs if not c]
                if nc:
                    prov[k] = (nc[0][0], nc[0][1], len(nc) - 1)
            elif self.prod_cont[k]:
                assert all(c for _, _, c, _ in rs)
                nref[k], vmn[k] = 0, 0
            else:
                assert not any(c for _, _, c, _ in rs)
                nref[k] = int(any(o not in SAME_OPS for _, _, _, o in rs))
                vmn[k] = len(rs)
        return dict(prov=prov, nref=nref, vmn=vmn)

    # ------------------------------------------------------------------ node rows
    def br_row(self, node, d, ctx, op):
        """A branch row.  `node` is the old branch (None for a split's new branch `oSL`)."""
        T = self.T['BR']
        r = T.new()
        rid = len(T.rows) - 1
        T.set(r, 'act', 1)
        T.set(r, 'rid', rid)
        T.set(r, 'w', ctx['w'])
        T.set(r, 'd', d)
        T.set(r, 'kid', ctx['kid'])
        if op != 'oSL':
            T.set(r, ['mF', 'mU', 'mD'][ctx['mode']], 1)
        if op is not None:
            T.set(r, op, 1)
            self.census('BR.' + op)
        T.set(r, 'dvlen', ctx['vlen'])
        T.setv(r, 'dvh', pack2(ctx['vh']))
        n = None
        if op not in ('oFV', 'oUV', 'oDV', 'oDZ'):
            n = self.nib(ctx['kid'], d)
            T.set(r, 'sel', 1, n)
        if node is not None:
            _, v, kids, m = node
            hasv = 1 if v is not None else 0
            T.set(r, 'hasv', hasv)
            if v is not None:
                T.setv(r, 'vl', le(v[0], 4))
                T.setv(r, 'vh', list(v[1]))
            for i in range(16):
                if kids[i] is not None:
                    T.set(r, 'f', 1, i)
                    fl, hb = self.ref(kids[i])
                    T.set(r, 'isn', fl, i)
                    for b in range(32):
                        T.set(r, 'ch', hb[b], 32 * i + b)
            T.setv(r, 'mem', le(m, 8))
            self.old_ref(T, r, 'BR', rid, node, False)
        if op is not None:
            self.br_gates(T, r, op)
        return T, r, rid, n

    def br_gates(self, T, r, op):
        T.set(r, 'gdn', int(op in ('oFD', 'oUD', 'oDH', 'oDL', 'oDN', 'oD1', 'oDS')))
        T.set(r, 'gnew', int(op in ('oUD', 'oUN', 'oDH', 'oDL', 'oDN', 'oSL', 'oUV', 'oDV')))

    def br_new(self, T, r, rid, node, new_node, nh, nm, om, op, nm2=0, vplus=0, vminus=0):
        """Fill the rewritten branch: flags, new child ref/mem, value, memory chain, its ref.
        `vplus` / `vminus`: `valueMem` of a written / removed branch value (`oUV`, `oDV`)."""
        _, v2, kids2, m2 = new_node
        T.set(r, 'nhv', int(v2 is not None))
        if v2 is not None:
            T.setv(r, 'nvl', le(v2[0], 4))
            T.setv(r, 'nvh', list(v2[1]))
        for i in range(16):
            T.set(r, 'nf', 1 if kids2[i] is not None else 0, i)
        if nh is not None:
            self.set_ref(T, r, 'nh', 'nhf', nh)
        T.setv(r, 'nm', mem_limbs(nm))
        T.setv(r, 'om', mem_limbs(om))
        T.setv(r, 'nmem', le(m2, 8))
        if node is None:
            base = 50
        else:
            assert v2 == node[1] or op in ('oUV', 'oDV')
            base = node[3]
        assert m2 == base + nm + nm2 + vplus - om - vminus, (m2, base, nm, nm2, om, vplus, vminus)
        vl = lambda x: [(x - 50) % 65536 + 50, (x - 50) >> 16, 0, 0] if x else [0] * 4
        self.carries(T, r, [mem_limbs(base)[k] + mem_limbs(nm)[k] + mem_limbs(nm2)[k] + vl(vplus)[k]
                            for k in range(4)],
                     [mem_limbs(om)[k] + vl(vminus)[k] for k in range(4)], mem_limbs(m2), 'cy', (-1, 0, 1, 2))
        hn = self.new_ref(T, r, 'BR', rid, new_node, False)
        nkn = sum(1 for c in kids2 if c is not None)
        if op in ('oDH', 'oDL', 'oDN'):
            hasv = 1 if v2 is not None else 0
            T.set(r, 'inv1', pow(nkn, P - 2, P))
            if nkn != 1:
                T.set(r, 'inv2', (1 - hasv) * pow(nkn - 1, P - 2, P))
        if op == 'oDV':
            T.set(r, 'inv1', pow(nkn, P - 2, P))
            T.set(r, 'inv2', pow(nkn - 1, P - 2, P))
        return hn

    def carries(self, T, r, plus, minus, out, col, rng=(-1, 0, 1)):
        """`out = plus − minus` on 16-bit limbs (`plus` may hold sums of several limbs)."""
        cy = 0
        for k in range(4):
            t = plus[k] - minus[k] + cy
            assert (t - out[k]) % 65536 == 0
            cy = (t - out[k]) // 65536
            assert cy in rng, cy
            T.set(r, col, cy, k)
        assert cy == 0

    def sn_row(self, node, d, ctx, op, kid, key, kid2=None, jm=None, y=None):
        """A leaf / extension row (old node `node`, or None for a built node) and its key chain.
        `jm`/`y`: the mismatch of an absent / split row (first nibble not matching the walk key)."""
        T = self.T['SN']
        r = T.new()
        rid = len(T.rows) - 1
        T.set(r, 'act', 1)
        T.set(r, 'rid', rid)
        T.set(r, 'w', ctx['w'])
        T.set(r, 'd', d)
        T.set(r, 'kid', kid)
        if kid2 is not None:
            T.set(r, 'kid2', kid2)
        if ctx.get('mode') is not None and op not in ('oLS', 'oLM', 'oEP', 'oEM'):
            T.set(r, ['mF', 'mU', 'mD'][ctx['mode']], 1)
        T.set(r, op, 1)
        self.census('SN.' + op)
        isL = op.startswith('oL')
        gA = op in ('oLA', 'oEA', 'oLZ', 'oEZ', 'oLX', 'oEX')
        g2 = op in ('oED', 'oLX', 'oEX')
        gold = op not in ('oLM', 'oEP', 'oEM')
        gnew = op in ('oLR', 'oLM', 'oEU', 'oEB', 'oEP', 'oEM')
        T.set(r, 'isL', int(isL))
        T.set(r, 'isE', int(not isL))
        T.set(r, 'gold', int(gold))
        T.set(r, 'gnew', int(gnew))
        T.set(r, 'gdn', int(op in ('oEF', 'oEU', 'oED', 'oES', 'oEB')))
        T.set(r, 'gA', int(gA))
        T.set(r, 'g2', int(g2))
        T.set(r, 'gfr', int(op in ('oEB', 'oEP', 'oEM')))
        L = len(key)
        odd = L % 2
        cont = L > KMAX
        head = (62 + odd) if cont else L
        if not gA:
            jm = head
        else:
            assert jm is not None
            if not ((jm < head and jm < KMAX) or (jm == L and not cont and jm < KMAX)):
                raise Unsupported('mismatch at nibble %d of a %d-nibble node key' % (jm, L))
        for j in range(head):
            x = key[j]
            T.set(r, 'a', 1, j)
            T.set(r, 'k', x, j)
            if j < jm:
                T.set(r, 'b', 1, j)
                got = self.nib(kid, d + j)
                assert got == x, ('key nibble', kid, d + j, got, x)
            elif not g2:
                self.rng(x)
                self.rng(x + 240)
            if g2:
                got = self.nib(kid2, d + j)
                assert got == x, ('key2 nibble', kid2, d + j, got, x)
        T.set(r, 'jm', jm)
        if jm == 0:
            T.set(r, 'j0', 1)
        else:
            T.set(r, 'ij0', pow(jm, P - 2, P))
        if jm < KMAX:
            T.set(r, 'kj', key[jm] if jm < head else 0)
            T.set(r, 'ajm', int(jm < head))
        if gA:
            Kw = PT.nibbles(self.keybytes[kid])
            if jm < L and d + jm < len(Kw):
                T.set(r, 'mN', 1)
                yy = self.nib(kid, d + jm)
                assert yy == y and yy != key[jm]
                T.set(r, 'y', yy)
                T.set(r, 'iy', pow((yy - key[jm]) % P, P - 2, P))
            elif jm < L:
                T.set(r, 'mK', 1)
                self.klen(kid, d + jm)
            else:
                assert isL and d + jm < len(Kw)
                T.set(r, 'mL', 1)
                yy = self.nib(kid, d + jm)
                T.set(r, 'y', yy)
        if isL:
            if op == 'oLX':
                self.klen(kid2, d + L)
            elif not gA:
                self.klen(kid, d + L)
        T.set(r, 'klen', L)
        T.set(r, 'odd', odd)
        hp = PT.hex_prefix(key, isL)
        T.set(r, 'hplen', len(hp))
        nh_head = (head + 2 - odd) // 2
        for m_ in range(nh_head):
            T.set(r, 'ha', 1, m_)
            T.set(r, 'hp', hp[m_], m_)
        if cont:
            T.set(r, 'cont', 1)
            T.set(r, 'rl', L - head)
            self.snc_rows(rid, 1, d + head, key[head:], kid, int(not gA), kid2 or 0, int(g2), int(gold),
                          int(gnew), hp)
        if ctx.get('mode') is not None:
            T.set(r, 'dvlen', ctx['vlen'])
            T.setv(r, 'dvh', pack2(ctx['vh']))
        if node is not None:
            if isL:
                T.setv(r, 'x', le(node[2][0], 4) + list(node[2][1]))
            else:
                self.set_ref(T, r, 'x', 'xf', self.ref(node[2]))
            T.setv(r, 'mem', le(node[3], 8))
            self.old_ref(T, r, 'SN', rid, node, bool(cont))
        return T, r, rid

    def snc_rows(self, rid, c, p, rest, kA, fA, kB, gB, gO, gN, hp):
        """Continuation chunks of a long node key: chunk `c` holds 64 nibbles (hp bytes 32c..)."""
        T = self.T['SNC']
        chunk, more = rest[:64], rest[64:]
        r = T.new()
        T.set(r, 'act', 1)
        T.set(r, 'rid', rid); T.set(r, 'c', c); T.set(r, 'p', p)
        T.set(r, 'kA', kA); T.set(r, 'fA', fA); T.set(r, 'kB', kB); T.set(r, 'gB', gB)
        T.set(r, 'gO', gO); T.set(r, 'gN', gN)
        assert len(chunk) % 2 == 0
        for j, x in enumerate(chunk):
            T.set(r, 'a', 1, j)
            T.set(r, 'k', x, j)
            if fA:
                assert self.nib(kA, p + j) == x
            if gB:
                assert self.nib(kB, p + j) == x
            if not fA and not gB:
                self.rng(x)
                self.rng(x + 240)
        for m_ in range(len(chunk) // 2):
            T.set(r, 'ha', 1, m_)
            T.set(r, 'hp', 16 * chunk[2 * m_] + chunk[2 * m_ + 1], m_)
            assert hp[32 * c + m_] == 16 * chunk[2 * m_] + chunk[2 * m_ + 1]
        T.set(r, 'n', len(chunk))
        if more:
            T.set(r, 'more', 1)
            T.set(r, 'rl', len(more))
            self.snc_rows(rid, c + 1, p + 64, more, kA, fA, kB, gB, gO, gN, hp)

    def sn_new(self, T, r, rid, new_node):
        if new_node[0] == 'leaf':
            T.setv(r, 'nx', le(new_node[2][0], 4) + list(new_node[2][1]))
        else:
            self.set_ref(T, r, 'nx', 'nxf', self.ref(new_node[2]))
        T.setv(r, 'nmem', le(new_node[3], 8))
        return self.new_ref(T, r, 'SN', rid, new_node, T.get(r, 'cont') == 1)

    def ext_fresh_mem(self, T, r, key, unm, out):
        """`nmem = unm + extOwnMem key` (fresh extension rows `oEB`/`oEP`/`oEM`)."""
        own = PT.ext_own_mem(key)
        assert out == unm + own
        T.setv(r, 'unm', mem_limbs(unm))
        self.carries(T, r, [mem_limbs(unm)[k] + (own if k == 0 else 0) for k in range(4)], [0] * 4,
                     mem_limbs(out), 'cy')

    # ------------------------------------------------------------------ results (UP)
    @staticmethod
    def res(rk, h=None, nm=0, om=0, kid2=0, st2=0, alen=0, avh=None, fpres=0, node=None):
        """`h`: the result's ref `(flag, 32 cells)`."""
        return dict(rk=rk, h=h or (0, [0] * 32), nm=nm, om=om, kid2=kid2, st2=st2, alen=alen,
                    avh=avh or bytes(32), fpres=fpres, node=node)

    def put_child_up_br(self, T, r, op, cr):
        T.set(r, 'rk', cr['rk'])
        T.setv(r, 'om', mem_limbs(cr['om']))
        if op in ('oUD', 'oDH'):
            self.set_ref(T, r, 'nh', 'nhf', cr['h'])
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
        if op in ('oEU', 'oEB'):
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

    def split(self, t, d, ctx):
        """`splitLeaf` / `splitExt` (both keys continue past the common prefix): the old row
        (`oLX` / `oEX`), the re-keyed extension (`oEM`), the new branch (`oSL`) with the walk's new
        leaf, and the extension over the common prefix (`oEP`).  Returns the spec result."""
        K = ctx['K']
        w, kid = ctx['w'], ctx['kid']
        k = t[1]
        rest = K[d:]
        jm = len(PT.common_prefix(k, rest))
        if jm >= len(k) or d + jm >= len(K):
            raise Unsupported('split where a key ends at the branch')
        v = (ctx['vlen'], ctx['vh'])
        ops = []
        spec = PT.split_leaf(k, t[2], rest, v, ops) if t[0] == 'leaf' else PT.split_ext(k, t[2], t[3], rest, v, ops)
        full = K[:d] + k
        if t[0] == 'ext' and len(full) % 2:
            full = full + [0]
        if len(full) % 2:
            raise Unsupported('odd leaf key')
        kid2 = self.kid(PT.pack_nibbles(full))
        e = d + jm
        y = K[e]
        x = k[jm]
        op = 'oLX' if t[0] == 'leaf' else 'oEX'
        T, r, rid = self.sn_row(t, d, ctx, op, kid, k, kid2=kid2, jm=jm, y=y)
        # the old-side child
        if op == 'oLX':
            xchild = None
        else:
            cm = t[3] - PT.ext_own_mem(k)
            if cm < 0:
                raise Unsupported('extension memory below its own usage')
            T.setv(r, 'cmb', le(cm, 8))
            for bb in le(cm, 8):
                self.rng(bb)
            self.carries(T, r, [mem_limbs(cm)[q] + (PT.ext_own_mem(k) if q == 0 else 0) for q in range(4)],
                         [0] * 4, mem_limbs(t[3]), 'cy2')
            xs = k[jm + 1:]
            if not xs:
                T.set(r, 'z', 1)
                xchild = (self.ref(t[2]), cm, None)
            else:
                T.set(r, 'iz', pow(len(xs), P - 2, P))
                sub = ('ext', xs, t[2], PT.ext_own_mem(xs) + cm)
                Tm, rm, ridm = self.sn_row(None, e + 1, dict(w=w), 'oEM', kid2, xs)
                self.ext_fresh_mem(Tm, rm, xs, cm, sub[3])
                hs = self.sn_new(Tm, rm, ridm, sub)
                T.setv(r, 'sxh', pack2(hs[1]))
                T.set(r, 'sxhf', hs[0])
                T.setv(r, 'sxm', mem_limbs(sub[3]))
                xchild = (hs, sub[3], sub)
            T.setv(r, 'xh', pack2(xchild[0][1]))
            T.set(r, 'xhf', xchild[0][0])
            T.setv(r, 'xm', mem_limbs(xchild[1]))
        # the new branch at e
        Tb, rb, ridb, nb = self.br_row(None, e, ctx, 'oSL')
        assert nb == y
        Tb.set(rb, 'sr', 1, x)
        Tb.set(rb, 'xk', kid2)
        assert self.nib(kid2, e) == x
        leaf, lh = self.materialize(w, e + 1, kid, ctx['vlen'], ctx['vh'])
        Tb.set(rb, 'kid2', kid); Tb.set(rb, 'st2', e + 1)
        Tb.set(rb, 'lvlen', ctx['vlen']); Tb.setv(rb, 'lvh', pack2(ctx['vh']))
        self.set_ref(Tb, rb, 'nh', 'nhf', lh)
        kids2 = [None] * 16
        kids2[y] = leaf
        if op == 'oLX':
            s = t[2]
            Tb.set(rb, 'xl', 1)
            Tb.set(rb, 'lvlen2', s[0]); Tb.setv(rb, 'lvh2', pack2(s[1]))
            xleaf, xh = self.materialize(w, e + 1, kid2, s[0], s[1])
            self.set_ref(Tb, rb, 'nh2', 'nh2f', xh)
            Tb.setv(rb, 'nm2', mem_limbs(xleaf[3]))
            kids2[x] = xleaf
            xm = xleaf[3]
        else:
            self.set_ref(Tb, rb, 'nh2', 'nh2f', xchild[0])
            Tb.setv(rb, 'nm2', mem_limbs(xchild[1]))
            kids2[x] = xchild[2] if xchild[2] is not None else t[2]
            xm = xchild[1]
        br = ('branch', None, kids2, 50 + leaf[3] + xm)
        hb = self.br_new(Tb, rb, ridb, None, br, lh, leaf[3], 0, 'oSL', nm2=xm)
        top, th = br, hb
        if jm > 0:
            ext = ('ext', K[d:e], br, PT.ext_own_mem(K[d:e]) + br[3])
            Te, re_, ride = self.sn_row(None, d, dict(w=w), 'oEP', kid, K[d:e])
            self.ext_fresh_mem(Te, re_, K[d:e], br[3], ext[3])
            th = self.sn_new(Te, re_, ride, ext)
            top = ext
        assert PT.hash_of(top) == PT.hash_of(spec), 'split result differs from the spec'
        T.setv(r, 'sh', pack2(th[1]))
        T.set(r, 'shf', th[0])
        T.setv(r, 'sm', mem_limbs(top[3]))
        return self.res(RK_H, h=th, nm=top[3], om=t[3], node=top)

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
                if mode == 0:
                    self.br_row(t, d, ctx, 'oFV')
                    self.klen(ctx['kid'], d)
                    if v is None:
                        return self.res(RK_ANS)
                    return self.res(RK_ANS, alen=v[0], avh=v[1], fpres=1)
                if mode == 1:
                    # write the branch's value (`oUV`)
                    T, r, rid, _ = self.br_row(t, d, ctx, 'oUV')
                    self.klen(ctx['kid'], d)
                    nv = (ctx['vlen'], ctx['vh'])
                    old = v[0] + 50 if v is not None else 0
                    nn = ('branch', nv, kids, m + nv[0] + 50 - old)
                    for x in le(nv[0], 4):
                        self.rng(x)
                    hn = self.br_new(T, r, rid, t, nn, None, 0, 0, 'oUV', vplus=nv[0] + 50, vminus=old)
                    return self.res(RK_H, h=hn, nm=nn[3], om=m, node=nn)
                if v is None:
                    # an absent delete: the key ends at a branch without value (`oDZ`)
                    T, r, rid, _ = self.br_row(t, d, ctx, 'oDZ')
                    self.klen(ctx['kid'], d)
                    return self.res(RK_SAME, h=self.own_ref(T, r), om=m, node=t)
                if sum(1 for x in kids if x is not None) < 2:
                    raise Unsupported('squash after a branch-value delete')
                T, r, rid, _ = self.br_row(t, d, ctx, 'oDV')
                self.klen(ctx['kid'], d)
                nn = ('branch', None, kids, m - (v[0] + 50))
                hn = self.br_new(T, r, rid, t, nn, None, 0, 0, 'oDV', vminus=v[0] + 50)
                return self.res(RK_HB, h=hn, nm=nn[3], om=m, node=nn)
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
                T, r, rid, _ = self.br_row(t, d, ctx, 'oDA')
                return self.res(RK_SAME, h=self.own_ref(T, r), om=m, node=t)
            T, r, rid, _ = self.br_row(t, d, ctx, None)   # the op depends on the child's result
            cr = self.walk(c, d + 1, ctx)
            if cr['rk'] == RK_SAME:
                op = 'oDS'
                T.set(r, op, 1)
                self.census('BR.' + op)
                self.br_gates(T, r, op)
                self.put_child_up_br(T, r, op, cr)
                return self.res(RK_SAME, h=self.own_ref(T, r), om=m, node=t)
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
            self.br_gates(T, r, op)
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
                self.sn_row(sibn, d + 1, dict(w=ctx['w']), 'oLS', kid2, sibn[1])
                T.set(r, 'kid2', kid2)
                T.set(r, 'lvlen', sibn[2][0])
                T.setv(r, 'lvh', pack2(sibn[2][1]))
                return self.res(RK_LD, om=m, kid2=kid2, st2=d, alen=sibn[2][0], avh=sibn[2][1])
            if op == 'oDL':
                T.setv(r, 'nm', mem_limbs(nm))
            nn = ('branch', v, kids2, m + nm - cr['om'])
            hn = self.br_new(T, r, rid, t, nn, nh, nm, cr['om'], op)
            return self.res(RK_HB, h=hn, nm=nn[3], om=m, node=nn)
        kid = ctx['kid']
        if t[0] == 'leaf':
            _, k, s, m = t
            if k != K[d:]:
                if mode == 1:
                    return self.split(t, d, ctx)
                jm = len(PT.common_prefix(k, K[d:]))
                y = K[d + jm] if d + jm < len(K) else None
                op = 'oLA' if mode == 0 else 'oLZ'
                T, r, rid = self.sn_row(t, d, ctx, op, kid, k, jm=jm, y=y)
                if mode == 0:
                    return self.res(RK_ANS)
                return self.res(RK_SAME, h=self.own_ref(T, r), om=m, node=t)
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
            if mode == 1:
                return self.split(t, d, ctx)
            jm = len(PT.common_prefix(k, K[d:]))
            y = K[d + jm] if d + jm < len(K) else None
            op = 'oEA' if mode == 0 else 'oEZ'
            T, r, rid = self.sn_row(t, d, ctx, op, kid, k, jm=jm, y=y)
            if mode == 0:
                return self.res(RK_ANS)
            return self.res(RK_SAME, h=self.own_ref(T, r), om=m, node=t)
        if mode == 0:
            T, r, rid = self.sn_row(t, d, ctx, 'oEF', kid, k)
            cr = self.walk(c, d + len(k), ctx)
            self.put_child_up_sn(T, r, 'oEF', cr)
            return self.res(RK_ANS, alen=cr['alen'], avh=cr['avh'], fpres=cr['fpres'])
        if mode == 1:
            T, r, rid = self.sn_row(t, d, ctx, 'oEU', kid, k)
            cr = self.walk(c, d + len(k), ctx)
            self.put_child_up_sn(T, r, 'oEU', cr)
            if PT.mem_of(c) is None:
                raise Unsupported('unrevealed extension child')
            nn = ('ext', k, cr['node'], PT.nsub(m + cr['nm'], cr['om']))
            self.carries(T, r, [mem_limbs(m)[q] + mem_limbs(cr['nm'])[q] for q in range(4)],
                         mem_limbs(cr['om']), mem_limbs(nn[3]), 'cy')
            hn = self.sn_new(T, r, rid, nn)
            return self.res(RK_H, h=hn, nm=nn[3], om=m, node=nn)
        # delete below the extension: the op depends on the child's result
        T, r, rid = self.sn_row(t, d, ctx, 'oES', kid, k)   # provisional; retagged below
        cr = self.walk(c, d + len(k), ctx)
        rk = cr['rk']
        if rk == RK_LD:
            self.retag_sn(T, r, 'oES', 'oED', k, d, cr['kid2'])
            self.put_child_up_sn(T, r, 'oED', cr)
            return self.res(RK_LD, om=m, kid2=cr['kid2'], st2=d, alen=cr['alen'], avh=cr['avh'])
        if rk == RK_SAME:
            self.put_child_up_sn(T, r, 'oES', cr)
            return self.res(RK_SAME, h=self.own_ref(T, r), om=m, node=t)
        if rk == RK_HB:
            self.retag_sn(T, r, 'oES', 'oEB', k, d, None)
            self.put_child_up_sn(T, r, 'oEB', cr)
            nn = PT.extend_child(k, cr['node'], [])
            self.ext_fresh_mem(T, r, k, cr['nm'], nn[3])
            hn = self.sn_new(T, r, rid, nn)
            return self.res(RK_HE, h=hn, nm=nn[3], om=m, node=nn)
        raise Unsupported('delete under an extension with a %d child result' % rk)

    def retag_sn(self, T, r, old, new, k, d, kid2):
        """Retag a provisional `oES` row once the child's result is known (the op and its kid2)."""
        if len(k) > KMAX:
            raise Unsupported('long extension key under a delete')
        T.set(r, old, 0)
        T.set(r, new, 1)
        self.op_census['SN.' + old] -= 1
        self.census('SN.' + new)
        g2 = new == 'oED'
        T.set(r, 'g2', int(g2))
        T.set(r, 'gnew', int(new == 'oEB'))
        T.set(r, 'gfr', int(new == 'oEB'))
        if g2:
            T.set(r, 'kid2', kid2)
            for j, x in enumerate(k):
                assert self.nib(kid2, d + j) == x

    # ------------------------------------------------------------------ the run
    def run(self):
        st_pre = PT.reveal_all(self.store, self.pre_root)
        if getattr(self, "tamper_fn", None):
            st_pre = self.tamper_fn(st_pre)
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
        roots = [(0, list(self.pre_root))]
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
            if res['rk'] not in (RK_H, RK_HB, RK_HE, RK_SAME):
                raise Unsupported('root result %d' % res['rk'])
            cur = res['node']
            roots.append(res['h'])
        spec_t, _ = PT.apply_changes(st_pre, [(k, None if v is None else (len(v), sha(v))) for k, v in self.changes])
        if self.mutant is None:
            assert roots[-1] == (0, list(self.post_root)), 'post-state root (a digest)'
            assert PT.root_hash(spec_t) == self.post_root == PT.hash_of(cur), 'post-state root'
        self.roots = roots
        self.pre, self.final = pre, final
        self.build_ws()
        self.build_kcmp()
        self.build_keys()
        self.build_rng()

    # ------------------------------------------------------------------ working set
    @staticmethod
    def len_chunks(n):
        assert 0 <= n < 1 << 24, ('value length', n)
        return [(n >> (6 * k)) & 63 for k in range(4)]

    def leaf_words(self, kd, pre, cur, wr):
        """The one-compression leaf block (`Ws.leafBlock`): word t < 8 = (pv_2t, pv_2t+1,
        kd_t + 2^16 x_t), word 8+t = (cv_2t, cv_2t+1, kd_8+t + 2^16 x_8+t)."""
        kdl, pvl, cvl = pack2(kd), pack2(pre[2]), pack2(cur[2])
        x = [pre[0] + 2 * cur[0] + 4 * wr] + self.len_chunks(pre[1]) + self.len_chunks(cur[1]) + [0] * 7
        ws = [(pvl[2 * t], pvl[2 * t + 1], kdl[t] + (x[t] << 16)) for t in range(8)]
        ws += [(cvl[2 * t], cvl[2 * t + 1], kdl[8 + t] + (x[8 + t] << 16)) for t in range(8)]
        return [S5.word(*w) for w in ws]

    def leaf_hash(self, words):
        cid, out = self.comp(S5.IV384, words)
        return cid, out

    def node_hash(self, l6, r6):
        blk = list(l6) + list(r6) + [1 << 63, 0, 0, 768]
        cid, out = self.comp(S5.IV384, blk)
        return cid, out

    @staticmethod
    def l18(ws):
        return [x for w in ws for x in S5.limbs(w)]

    @staticmethod
    def tree_levels(D, leafd):
        lv = [list(x) for x in leafd]
        levels = [lv]
        for _ in range(D):
            lv = [S5.compress(S5.IV384, list(lv[2 * x]) + list(lv[2 * x + 1]) + [1 << 63, 0, 0, 768])[:6]
                  for x in range(len(lv) // 2)]
            levels.append(lv)
        return levels

    def write_log(self):
        """The write accesses `(t, seg, key, ref)`: the committed changes in key order (one per
        written key, as the tape of M5a), optionally preceded by `extra` intermediate writes of
        the first written keys (an overwritten value, to exercise the memory chain), at times
        1, 2, …; cut into `segs` contiguous segments."""
        ws = []
        for n, (key, ref) in enumerate(sorted(self.final.items())):
            if n < self.extra_writes:
                v = b'm5a3-intermediate-%d' % n
                ws.append((key, (1, len(v), sha(v))))
            ws.append((key, ref))
        S = min(self.segs, len(ws))
        out = []
        for t, (key, ref) in enumerate(ws):
            out.append((t + 1, t * S // len(ws), key, ref))
        return out, S

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
                    Tb.setv(r, 'plx', self.len_chunks(p[1])); Tb.setv(r, 'clx', self.len_chunks(c[1]))
                    for x in self.len_chunks(p[1]) + self.len_chunks(c[1]):
                        self.rng(x)
                    cid, out = self.leaf_hash(self.leaf_words(kdi, p, c, wr))
                    Tb.set(r, 'cid', cid)
                    Tb.setv(r, 'dg', self.l18(out[:6]))
                    Tb.setv(r, 'dx', self.l18(out[6:]))
                    dig[ph].append(out[:6])
                    if ph == 0 and i + 1 < n:
                        Tb.set(r, 'so', 1)
                    if ph == 1 and wr:
                        Tb.setv(r, 'rin', pack2(self.roots[j][1]))
                        Tb.set(r, 'rif', self.roots[j][0])
                        Tb.setv(r, 'rout', pack2(self.roots[j + 1][1]))
                        Tb.set(r, 'rof', self.roots[j + 1][0])
                        Tb.set(r, 'rk', self.root_rk[j])
                        Tb.setv(r, 'rnm', mem_limbs(self.root_mem[j][0]))
                        Tb.setv(r, 'rom', mem_limbs(self.root_mem[j][1]))
                        j += 1
                else:
                    dig[ph].append([0] * 6)
        # inner nodes of both full trees
        Tn = self.T['WSN']
        self.writes, self.nseg = self.write_log()

        def build(ph, leafd):
            lv = [list(x) for x in leafd]
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
                        Tn.set(r, 'nw', self.nseg)
                    nxt.append(out[:6])
                lv = nxt

        build(0, dig[0])
        # segments: write accesses on the memory chain, one batched path update per segment
        Ta, Tl, Tp = self.T['WSA'], self.T['WSL'], self.T['WSP']
        state = [list(x) for x in leaves0]
        digs = [list(x) for x in dig[0]]
        idx_of = {k: i for i, k in enumerate(self.keys)}
        rch = [self.tree_levels(D, digs)[D][0]]
        for s in range(self.nseg):
            seg_w = [w for w in self.writes if w[1] == s]
            touched = sorted(set(idx_of[w[2]] for w in seg_w))
            seg_start = list(state)
            last_t = {}
            for (t, _, key, ref) in seg_w:
                i = idx_of[key]
                kdi, p, c, wr = state[i]
                r = Ta.new()
                Ta.set(r, 'act', 1); Ta.set(r, 'seg', s); Ta.set(r, 't', t)
                Ta.setv(r, 'kd', pack2(kdi))
                Ta.set(r, 'cp', c[0]); Ta.set(r, 'cl', c[1]); Ta.setv(r, 'cv', pack2(c[2])); Ta.set(r, 'wr', wr)
                idp = last_t.get(i, 0)
                Ta.set(r, 'idp', idp)
                Ta.set(r, 'ncp', ref[0]); Ta.set(r, 'ncl', ref[1]); Ta.setv(r, 'ncv', pack2(ref[2]))
                gap = t - idp - 1
                assert 0 <= gap < 1 << 24
                dt = [(gap >> (8 * k)) & 255 for k in range(3)]
                Ta.setv(r, 'dt', dt)
                for x in dt:
                    self.rng(x)
                last_t[i] = t
                state[i] = (kdi, p, ref, 1)
            # touched leaves: old → new
            old_d = list(digs)
            new_d = list(digs)
            for i in touched:
                kdi, p, c, wr = seg_start[i]
                nk, np_, nc, nwr = state[i]
                r = Tl.new()
                Tl.set(r, 'act', 1); Tl.set(r, 'seg', s); Tl.set(r, 'i', i)
                Tl.setv(r, 'kd', pack2(kdi)); Tl.setv(r, 'kb', list(kdi))
                Tl.set(r, 'pp', p[0]); Tl.set(r, 'pl', p[1]); Tl.setv(r, 'pv', pack2(p[2]))
                Tl.setv(r, 'plx', self.len_chunks(p[1]))
                Tl.set(r, 'cp', c[0]); Tl.set(r, 'cl', c[1]); Tl.setv(r, 'cv', pack2(c[2])); Tl.set(r, 'wr', wr)
                Tl.setv(r, 'clx', self.len_chunks(c[1]))
                Tl.set(r, 'ncp', nc[0]); Tl.set(r, 'ncl', nc[1]); Tl.setv(r, 'ncv', pack2(nc[2])); Tl.set(r, 'nwr', nwr)
                Tl.setv(r, 'nclx', self.len_chunks(nc[1]))
                Tl.set(r, 'idl', last_t[i])
                # M5a-5: the touched leaf is a real entry, `i < wsLen` (bytes of `wsLen - 1 - i`)
                ix = [((n - 1 - i) >> (8 * k)) & 255 for k in range(3)]
                Tl.setv(r, 'ix', ix)
                for x in ix:
                    self.rng(x)
                for x in list(kdi) + self.len_chunks(p[1]) + self.len_chunks(c[1]) + self.len_chunks(nc[1]):
                    self.rng(x)
                cO, outO = self.leaf_hash(self.leaf_words(kdi, p, c, wr))
                cN, outN = self.leaf_hash(self.leaf_words(kdi, p, nc, nwr))
                assert outO[:6] == digs[i]
                Tl.set(r, 'cidO', cO); Tl.setv(r, 'dgO', self.l18(outO[:6])); Tl.setv(r, 'dxO', self.l18(outO[6:]))
                Tl.set(r, 'cidN', cN); Tl.setv(r, 'dgN', self.l18(outN[:6])); Tl.setv(r, 'dxN', self.l18(outN[6:]))
                new_d[i] = outN[:6]
            # the union of the touched paths, level by level
            cur_t = set(touched)
            lo_lv, ln_lv = old_d, new_d
            for l in range(D):
                par = sorted(set(i >> 1 for i in cur_t))
                no, nn = list(lo_lv[::2]), list(ln_lv[::2])
                for j in par:
                    r = Tp.new()
                    top = int(l == D - 1)
                    Tp.set(r, 'act', 1); Tp.set(r, 'seg', s); Tp.set(r, 'lvl', l); Tp.set(r, 'idx', j)
                    Tp.set(r, 'top', top)
                    Tp.set(r, 'tl', int(2 * j in cur_t)); Tp.set(r, 'tr', int(2 * j + 1 in cur_t))
                    a_o, a_n, b_o, b_n = lo_lv[2 * j], ln_lv[2 * j], lo_lv[2 * j + 1], ln_lv[2 * j + 1]
                    Tp.setv(r, 'lo', self.l18(a_o)); Tp.setv(r, 'ln', self.l18(a_n))
                    Tp.setv(r, 'ro', self.l18(b_o)); Tp.setv(r, 'rn', self.l18(b_n))
                    cO, oO = self.node_hash(a_o, b_o)
                    cN, oN = self.node_hash(a_n, b_n)
                    Tp.set(r, 'cidO', cO); Tp.set(r, 'cidN', cN)
                    Tp.setv(r, 'oo', self.l18(oO[:6])); Tp.setv(r, 'oox', self.l18(oO[6:]))
                    Tp.setv(r, 'on', self.l18(oN[:6])); Tp.setv(r, 'onx', self.l18(oN[6:]))
                    no[j], nn[j] = oO[:6], oN[:6]
                # untouched parents keep their old digest (recompute from the old tree)
                full_o = self.tree_levels(1, lo_lv)[1]
                full_n = self.tree_levels(1, ln_lv)[1]
                for j in range(len(full_o)):
                    if j in par:
                        assert full_o[j] == no[j] and full_n[j] == nn[j]
                lo_lv, ln_lv = full_o, full_n
                cur_t = set(par)
            assert lo_lv[0] == rch[-1]
            rch.append(ln_lv[0])
            digs = new_d
        assert digs == [list(x) for x in dig[1]], 'segments end at the FINAL leaves'
        assert rch[-1] == self.tree_levels(D, dig[1])[D][0]
        build(1, dig[1])
        self.rch = rch
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

    def build_rng(self):
        T = self.T['RNG']
        for v in range(256):
            r = T.new()
            T.set(r, 'v', v)
            cnt = self.rng_count.get(v, 0)
            assert cnt < 1 << 20
            for t in range(20):
                T.set(r, 'm', (cnt >> t) & 1, t)

    # ------------------------------------------------------------------ output
    def write(self, out):
        os.makedirs(out, exist_ok=True)
        heights = {}
        for nm, T in self.T.items():
            if nm == 'WSB':
                heights[nm] = T.dump(os.path.join(out, nm + '.bin'), exact=2 << self.D)
            elif nm == 'RNG':
                heights[nm] = T.dump(os.path.join(out, nm + '.bin'), exact=256)
            else:
                if nm in ('BR', 'SN'):
                    w = T.width
                    rid_i = T.ix('rid')
                    n0 = len(T.rows)
                    T.pad_row = (lambda rid_i, w: (lambda i: [i if c == rid_i else 0 for c in range(w)]))(rid_i, w)
                heights[nm] = T.dump(os.path.join(out, nm + '.bin'))
        json.dump(self.sha_msgs, open(os.path.join(out, 'sha_msgs.json'), 'w'))
        json.dump(self.comps, open(os.path.join(out, 'comps.json'), 'w'))
        # public values: prev_state_root (16 limbs), then the working-set entry count (M5a-5)
        wslen = len(self.keys)
        if self.mutant == 'wslen':
            wslen += 1
        elif self.mutant == 'wslenlo':
            wslen -= 1
        pubs = pack2(self.pre_root) + [wslen]
        with open(os.path.join(out, 'pubs.bin'), 'wb') as f:
            f.write(struct.pack('<17I', *pubs))
        tape = []
        for (t, seg, key, ref) in self.writes:
            tape.append([13, True, [seg, t] + pack2(sha(key)) + [ref[0], ref[1]] + pack2(ref[2])])
        post = self.post_root
        if self.mutant == 'postroot':
            post = bytes([post[0] ^ 1]) + post[1:]
        tape.append([14, True, [0, 0] + pack2(self.pre_root)])
        tape.append([14, False, [len(self.final), 0] + pack2(post)])
        json.dump(tape, open(os.path.join(out, 'tape.json'), 'w'))
        stats = dict(heights=heights, sha_msgs=len(self.sha_msgs),
                     sha_blocks=sum((len(m['bytes']) // 2 + 9 + 63) // 64 for m in self.sha_msgs),
                     compressions=len(self.comps), keys=len(self.keybytes), ws_keys=len(self.keys),
                     changes=len(self.final), writes=len(self.writes), segments=self.nseg,
                     rch=[bytes(b for w in r for b in w.to_bytes(8, 'big')).hex() for r in self.rch], rows={k: len(T.rows) for k, T in self.T.items()},
                     ops=self.op_census, pre_root=self.pre_root.hex(), post_root=bytes(self.roots[-1][1]).hex(),
                     versions=dict(published=sum(self.plan['nref'].values()) if self.plan else 0,
                                   hashed_old=sum(1 for m in self.sha_msgs if m['id'] >= ID_BR and m['id'] % 2 == 0),
                                   hashed_new=sum(1 for m in self.sha_msgs if m['id'] >= ID_BR and m['id'] % 2 == 1)))
        json.dump(stats, open(os.path.join(out, 'stats.json'), 'w'), indent=1)
        return stats


def _first(T, op):
    return next(r for r in T.rows if T.get(r, op) == 1)


def _t_absent(g):
    T = g.T['SN']
    r = _first(T, 'oLF')
    k0 = T.get(r, 'k', 0)
    T.set(r, 'oLF', 0); T.set(r, 'oLA', 1); T.set(r, 'gA', 1); T.set(r, 'mN', 1)
    for j in range(KMAX):
        T.set(r, 'b', 0, j)
    T.set(r, 'jm', 0); T.set(r, 'kj', k0); T.set(r, 'ajm', 1); T.set(r, 'y', k0); T.set(r, 'iy', 0)


def _t_extabsent(g):
    T = g.T['SN']
    r = _first(T, 'oEA')
    jm = T.get(r, 'jm')
    T.set(r, 'b', 1, jm); T.set(r, 'jm', jm + 1)
    T.set(r, 'kj', T.get(r, 'k', jm + 1)); T.set(r, 'ajm', T.get(r, 'a', jm + 1))


def _t_branchval(g):
    T = g.T['BR']
    T.set(_first(T, 'oFV'), 'hasv', 0)


def _t_split(g):
    T = g.T['BR']
    r = _first(T, 'oSL')
    x = next(i for i in range(16) if T.get(r, 'sr', i))
    x2 = next(i for i in range(16) if i != x and not T.get(r, 'sel', i))
    T.set(r, 'sr', 0, x); T.set(r, 'sr', 1, x2)
    T.set(r, 'nf', 0, x); T.set(r, 'nf', 1, x2)


def _t_splitext(g):
    T = g.T['SN']
    r = _first(T, 'oEX')
    T.set(r, 'cmb', T.get(r, 'cmb', 0) + 1, 0)


def _t_absdel(g):
    T = g.T['SN']
    r = _first(T, 'oLZ')
    T.set(r, 'y', T.get(r, 'kj'))


def _t_squash(g):
    T = g.T['SN']
    r = _first(T, 'oEB')
    T.set(r, 'nmem', T.get(r, 'nmem', 0) + 1, 0)


def _t_chain(g):
    T = g.T['SNC']
    r = T.rows[0]
    k0 = T.get(r, 'k', 0)
    k1 = (k0 + 1) % 16
    T.set(r, 'k', k1, 0)
    T.set(r, 'hp', T.get(r, 'hp', 0) + 16 * (k1 - k0), 0)


def _ver_reader(g):
    """A FINAL branch row that reads its old node from an in-memory version (`oref = 1`)."""
    T = g.T['BR']
    return T, next(r for r in T.rows if T.get(r, 'oref') == 1 and T.get(r, 'w') >= W_FINAL)


def _t_verslot(g):
    T, r = _ver_reader(g)
    i = next(i for i in range(16) if T.get(r, 'f', i) == 1 and T.get(r, 'sel', i) == 0)
    T.set(r, 'ch', T.get(r, 'ch', 32 * i) ^ 1, 32 * i)


def _t_vernid(g):
    T, r = _ver_reader(g)
    nid = T.get(r, 'ho', 0)
    other = next(T.get(q, 'hn', 0) for q in T.rows if T.get(q, 'nref') == 1 and T.get(q, 'hn', 0) != nid)
    T.set(r, 'ho', other, 0)


def _t_vmcount(g):
    T = g.T['BR']
    r = next(r for r in T.rows if T.get(r, 'gsha') == 1 and any(T.get(r, 'vm', t) for t in range(VBITS)))
    n = sum(T.get(r, 'vm', t) << t for t in range(VBITS)) + 1
    g.set_bits(T, r, 'vm', n)


def _t_finroot(g):
    T = g.T['BR']
    last = max(T.get(r, 'w') for r in T.rows if T.get(r, 'w') >= W_FINAL)
    rid, r = next((i, r) for i, r in enumerate(T.rows) if T.get(r, 'w') == last and T.get(r, 'd') == 0)
    assert T.get(r, 'gnew') == 1 and T.get(r, 'nref') == 0
    nid = Gen.nid('BR', rid)
    T.set(r, 'nref', 1)
    T.setv(r, 'hn', [nid] + [0] * 31)
    g.sha_msgs = [m for m in g.sha_msgs if m['id'] != ID_BR + 2 * rid + 1]
    W = g.T['WSB']
    wr = [q for q in W.rows if W.get(q, 'ph') == 1 and W.get(q, 'wr') == 1][-1]
    W.set(wr, 'rof', 1)
    W.setv(wr, 'rout', pack2([nid] + [0] * 31))


def _t_nidforge(g):
    T = g.T['BR']
    rs = [r for r in T.rows if T.get(r, 'nref') == 1]
    T.set(rs[1], 'hn', T.get(rs[0], 'hn', 0), 0)


def _t_bvalue(g):
    T = g.T['BR']
    r = _first(T, 'oUV')
    T.set(r, 'nvh', T.get(r, 'nvh', 0) ^ 1, 0)


def _t_bvmem(g):
    T = g.T['BR']
    r = _first(T, 'oDV')
    T.set(r, 'nmem', T.get(r, 'nmem', 0) + 1, 0)


# ---- M5a-3 working-set segment mutants
def _t_wsstale(g):
    # a write access consumes another value than the entry's latest (its old `cv` limb + 1)
    T = g.T['WSA']
    r = T.rows[0]
    T.set(r, 'cv', T.get(r, 'cv', 0) + 1, 0)


def _t_wsorder(g):
    # two accesses to one entry (needs --extra-writes): the later one (final value) is put first
    # on the chain (it consumes the opening value) and the earlier one consumes the later one's
    # value — its gap t - idp - 1 is negative, so no bytes `dt` exist (written mod 2^24)
    T = g.T['WSA']
    rows = T.rows
    pair = next((a, b) for a in rows for b in rows
                if a is not b and T.get(a, 'kd', 0) == T.get(b, 'kd', 0) and T.get(b, 'idp') == T.get(a, 't'))
    a, b = pair            # a: earlier (t1), b: later (t2), b consumed a
    t1, t2 = T.get(a, 't'), T.get(b, 't')
    for nm, n in (('cp', 1), ('cl', 1), ('cv', 16), ('wr', 1), ('idp', 1)):
        for j in range(n):
            T.set(b, nm, T.get(a, nm, j if n > 1 else None), j if n > 1 else None)
    T.set(a, 'cp', T.get(b, 'ncp')); T.set(a, 'cl', T.get(b, 'ncl')); T.set(a, 'wr', 1)
    T.setv(a, 'cv', [T.get(b, 'ncv', j) for j in range(16)])
    T.set(a, 'idp', t2)
    gap = (t1 - t2 - 1) % (1 << 24)
    T.setv(a, 'dt', [(gap >> (8 * k)) & 255 for k in range(3)])
    T.setv(b, 'dt', [((t2 - 1) >> (8 * k)) & 255 for k in range(3)])


def _t_wsseg(g):
    # a write access attributed to another segment than the one the write log states
    T = g.T['WSA']
    r = T.rows[-1]
    T.set(r, 'seg', T.get(r, 'seg') - 1)


def _t_wssib(g):
    # a segment path node changes an untouched sibling between the old and the new tree
    T = g.T['WSP']
    r = next(r for r in T.rows if T.get(r, 'tr') == 0 or T.get(r, 'tl') == 0)
    nm = 'rn' if T.get(r, 'tr') == 0 else 'ln'
    T.set(r, nm, T.get(r, nm, 0) ^ 1, 0)


def _t_wsdrop(g):
    # a segment path node that receives no touched child (a free subtree)
    T = g.T['WSP']
    r = next(r for r in T.rows if T.get(r, 'top') == 0)
    T.set(r, 'tl', 0); T.set(r, 'tr', 0)


def _t_wsabsorb(g):
    # an inactive path-node row absorbs a touched child without hashing (drops its update)
    T = g.T['WSP']
    r = next(r for r in T.rows if T.get(r, 'top') == 0)
    T.set(r, 'act', 0)


def _t_wsleaf(g):
    # a touched leaf claims another pre-value length (+1), consistently hashed: its old digest is
    # not the working set's leaf, so the segment's old path does not reach `RCH(seg)`
    T = g.T['WSL']
    r = T.rows[0]
    pl = T.get(r, 'pl') + 1
    for x in g.len_chunks(pl - 1):
        g.rng_count[x] -= 1
    for x in g.len_chunks(pl):
        g.rng(x)
    T.set(r, 'pl', pl); T.setv(r, 'plx', g.len_chunks(pl))
    g.T['RNG'].rows = []
    g.build_rng()
    kd = bytes(T.get(r, 'kb', j) for j in range(32))
    pv = b''.join(T.get(r, 'pv', j).to_bytes(2, 'big') for j in range(16))
    cv = b''.join(T.get(r, 'cv', j).to_bytes(2, 'big') for j in range(16))
    words = g.leaf_words(kd, (T.get(r, 'pp'), pl, pv), (T.get(r, 'cp'), T.get(r, 'cl'), cv), T.get(r, 'wr'))
    out = S5.compress(S5.IV384, words)
    g.comps[T.get(r, 'cidO') // 128] = dict(h=[str(x) for x in S5.IV384], block=[str(x) for x in words])
    T.setv(r, 'dgO', g.l18(out[:6])); T.setv(r, 'dxO', g.l18(out[6:]))

TAMPERS = dict(absent=_t_absent, extabsent=_t_extabsent, branchval=_t_branchval, split=_t_split,
               splitext=_t_splitext, absdel=_t_absdel, squash=_t_squash, chain=_t_chain,
               verslot=_t_verslot, vernid=_t_vernid, vmcount=_t_vmcount, finroot=_t_finroot,
               nidforge=_t_nidforge, bvalue=_t_bvalue, bvmem=_t_bvmem, wsstale=_t_wsstale,
               wsorder=_t_wsorder, wsseg=_t_wsseg, wssib=_t_wssib, wsdrop=_t_wsdrop, wsabsorb=_t_wsabsorb,
               wsleaf=_t_wsleaf)


def make_gen(st, names, mutant, plan, segs=1, extra_writes=0):
    g = Gen(st, names, mutant, plan, segs, extra_writes)
    if mutant == 'node':
        # A tampered pre-state node: the leaf of the first written key carries memory usage + 1
        # (still a well-formed node), while its parent keeps the true child hash.  Every row that
        # visits the leaf holds the tampered content.

        def tamper(t, K, d):
            if t[0] == 'leaf':
                bad = ('leaf', t[1], t[2], t[3] + 1)
                PT.OVERRIDE[id(bad)] = PT.hash_of(t)
                g.keep.append(bad)
                return bad
            if t[0] == 'ext':
                return ('ext', t[1], tamper(t[2], K, d + len(t[1])), t[3])
            kids = list(t[2])
            kids[K[d]] = tamper(kids[K[d]], K, d + 1)
            return ('branch', t[1], kids, t[3])
        k0 = g.changes[0][0]
        g.tamper_fn = lambda t: tamper(t, PT.nibbles(k0), 0)
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
    return g


def main():
    st = json.load(open(sys.argv[1]))
    names = json.load(open(sys.argv[2]))
    out = sys.argv[3]
    args = sys.argv[4:]
    mutant = args[args.index('--mutant') + 1] if '--mutant' in args else None
    segs = int(args[args.index('--segs') + 1]) if '--segs' in args else 1
    extra = int(args[args.index('--extra-writes') + 1]) if '--extra-writes' in args else 0
    # pass 1: every node hashed (the unbatched trace, still a valid one); pass 2: batched FINAL
    g = make_gen(st, names, mutant, None, segs, extra)
    if '--unbatched' not in args:
        plan = g.make_plan()
        PT.OVERRIDE.clear()
        g = make_gen(st, names, mutant, plan, segs, extra)
    if mutant in TAMPERS:
        TAMPERS[mutant](g)
    stats = g.write(out)
    print(json.dumps(dict((k, stats[k]) for k in ('rows', 'heights', 'sha_msgs', 'sha_blocks', 'compressions',
                                                  'ops', 'versions', 'writes', 'segments'))))


if __name__ == '__main__':
    main()
