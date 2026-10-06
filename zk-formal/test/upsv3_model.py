#!/usr/bin/env python3
"""Model check of the upsV3 table.

Usage: lake env lean --run test/UpsExport.lean > ups_air.txt
       python3 test/upsv3_model.py ups_air.txt [seed] [instances] [chain_prob] [long_chain]

chain_prob: probability that a node on the [0,15] path sits below a chain of empty-key
extensions (`.ext [] c m`, lengths 1 … 50); long_chain: if > 0, one more chain of that length
above the root (depth ≤ 399 needs long_chain + path ≤ 399).

Model check of the upsV3 table (Tables/Ups.lean) against the spec PTrie.upsert.

For random well-formed partial tries (post-lockstep trie, revealed along [0,15]) and random
new values: build the nodeV3 record view (ids, depths, post bytes, edges, BMAP), generate the
upsV3 segment by the design rules, then check
  * every exported constraint is 0 on every row (field P);
  * emitted Q bytes == ser of the spec upsert's new path nodes, post root == hashOf(upsert);
  * UPB reads are record bytes (id, pos, byte, len, depth) of path records only;
  * EDGE/BMAP reads exist in the record providers; MEMD sends == receives;
  * DIGEST lookups == sha256 of the emitted bytes of that id with that length.
"""
import hashlib, random, sys, re

P = 2013265921
END, START = 16, 18
EK_DOWN, EK_KEY, EK_VAL, EK_LEND = 0, 1, 2, 3
U64 = 1 << 64

def sha(b): return list(hashlib.sha256(bytes(b)).digest())
def leN(w, x): return [(x >> (8 * i)) & 255 for i in range(w)]
def u16(x): return leN(2, x)
def u32(x): return leN(4, x)
def u64(x): return leN(8, x)

def pack(n):
    out = []
    while len(n) >= 2:
        out.append(n[0] * 16 + n[1]); n = n[2:]
    return out
def hexPrefix(n, leaf):
    lb = 32 if leaf else 0
    if len(n) % 2 == 1: return [16 + n[0] + lb] + pack(n[1:])
    return [lb] + pack(n)

# PTrie: ('hash',h) ('leaf',k,slot,mem) ('ext',k,c,mem) ('branch',bv,kids[16],mem)
# slot: ('val',bytes) ('ref',len,h)
def valueRef(s): return u32(len(s[1])) + sha(s[1]) if s[0] == 'val' else u32(s[1]) + s[2]
def hashOf(t):
    if t[0] == 'hash': return t[1]
    return sha(ser(t))
def ser(t):
    if t[0] == 'leaf':
        hp = hexPrefix(t[1], True); return [0] + u32(len(hp)) + hp + valueRef(t[2]) + u64(t[3])
    if t[0] == 'ext':
        hp = hexPrefix(t[1], False); return [3] + u32(len(hp)) + hp + hashOf(t[2]) + u64(t[3])
    bv, kids, m = t[1], t[2], t[3]
    bm = sum(1 << i for i in range(16) if kids[i] is not None)
    body = u16(bm) + sum((hashOf(c) for c in kids if c is not None), []) + u64(m)
    return ([1] if bv is None else [2] + valueRef(bv)) + body
def memD(t): return 0 if t[0] == 'hash' else t[3]
def slen(s): return len(s[1]) if s[0] == 'val' else s[1]
def nsub(a, b): return max(0, a - b)

def leafMem(k, vl): return 50 + 2 * len(hexPrefix(k, True)) + (vl + 50)
def extOwnMem(k): return 50 + 2 * len(hexPrefix(k, False))
def valueMem(vl): return vl + 50
def commonPrefix(a, b):
    p = []
    for x, y in zip(a, b):
        if x != y: break
        p.append(x)
    return p
def kids1(x, c):
    ks = [None] * 16; ks[x] = c; return ks
def kids2(x, c, y, d):
    ks = [None] * 16; ks[x] = c; ks[y] = d; return ks
def newLeaf(k, v): return ('leaf', k, ('val', v), leafMem(k, len(v)))
def wrapExt(p, b): return b if not p else ('ext', p, b, extOwnMem(p) + memD(b))
def splitLeaf(k, s, key, v):
    p = commonPrefix(k, key); a, bb = k[len(p):], key[len(p):]
    if not a and bb:
        return wrapExt(p, ('branch', s, kids1(bb[0], newLeaf(bb[1:], v)), 50 + valueMem(slen(s)) + leafMem(bb[1:], len(v))))
    if a and not bb:
        return wrapExt(p, ('branch', ('val', v), kids1(a[0], ('leaf', a[1:], s, leafMem(a[1:], slen(s)))),
                           50 + valueMem(len(v)) + leafMem(a[1:], slen(s))))
    if a and bb:
        return wrapExt(p, ('branch', None, kids2(a[0], ('leaf', a[1:], s, leafMem(a[1:], slen(s))), bb[0], newLeaf(bb[1:], v)),
                           50 + leafMem(a[1:], slen(s)) + leafMem(bb[1:], len(v))))
    return newLeaf(key, v)
def splitExt(k, c, m, key, v):
    p = commonPrefix(k, key); cm = nsub(m, extOwnMem(k)); a = k[len(p):]
    x, xs = a[0], a[1:]
    sub = c if not xs else ('ext', xs, c, extOwnMem(xs) + cm)
    subMem = cm if not xs else extOwnMem(xs) + cm
    bb = key[len(p):]
    if not bb: return wrapExt(p, ('branch', ('val', v), kids1(x, sub), 50 + valueMem(len(v)) + subMem))
    return wrapExt(p, ('branch', None, kids2(x, sub, bb[0], newLeaf(bb[1:], v)), 50 + subMem + leafMem(bb[1:], len(v))))
def isPrefix(a, b): return len(a) <= len(b) and b[:len(a)] == a
def upsert(t, key, v):
    if t[0] == 'hash': return None
    if t[0] == 'leaf':
        return newLeaf(t[1], v) if t[1] == key else splitLeaf(t[1], t[2], key, v)
    if t[0] == 'ext':
        k, c, m = t[1], t[2], t[3]
        if isPrefix(k, key):
            if c[0] == 'hash': return None
            c2 = upsert(c, key[len(k):], v)
            if c2 is None: return None
            return ('ext', k, c2, nsub(m + memD(c2), c[3]))
        return splitExt(k, c, m, key, v)
    bv, kids, m = t[1], t[2], t[3]
    if not key:
        return ('branch', ('val', v), kids, nsub(m + valueMem(len(v)), valueMem(slen(bv)) if bv else 0))
    n, rest = key[0], key[1:]
    c = kids[n]
    if c is None:
        ks = list(kids); ks[n] = newLeaf(rest, v); return ('branch', bv, ks, m + leafMem(rest, len(v)))
    if c[0] == 'hash': return None
    c2 = upsert(c, rest, v)
    if c2 is None: return None
    ks = list(kids); ks[n] = c2
    return ('branch', bv, ks, nsub(m + memD(c2), c[3]))

# ---------------------------------------------------------------- random tries
def rhash(): return [random.randrange(256) for _ in range(32)]
def rmem():
    r = random.random()
    if r < 0.25: return random.randrange(0, 60)          # small: truncation cases
    if r < 0.4: return U64 - 1 - random.randrange(1000)   # near the top
    return random.randrange(0, U64)
def rslot(reveal=True):
    if reveal and random.random() < 0.7: return ('val', [random.randrange(256) for _ in range(random.randrange(0, 40))])
    return ('ref', random.choice([random.randrange(0, 1 << 32), random.randrange(0, 300)]), rhash())
def rkey(lo=0, hi=5): return [random.randrange(16) for _ in range(random.randrange(lo, hi))]
def rnode(rem, depth):
    """A node on the path of `rem` (remaining key), revealed along it."""
    r = random.random()
    if depth > 3 or r < 0.3:  # leaf
        if random.random() < 0.35: k = list(rem)
        elif random.random() < 0.5 and rem: k = rem[:random.randrange(len(rem))] + ([random.randrange(16)] if random.random() < 0.5 else [])
        else: k = list(rem[:random.randrange(len(rem) + 1)]) + rkey(0, 4)
        return ('leaf', k, rslot(k == rem or True), rmem())
    if r < 0.55:  # extension (non-empty key)
        if rem and random.random() < 0.6:
            l = random.randrange(1, len(rem) + 1); k = rem[:l]
            return ('ext', k, rchild(rem[l:], depth + 1), rmem())
        k = rem[:random.randrange(len(rem) + 1)] + rkey(1, 4)
        if isPrefix(k, rem) and len(k) <= len(rem):
            return ('ext', k, rchild(rem[len(k):], depth + 1), rmem())
        return ('ext', k, ('hash', rhash()) if random.random() < 0.5 else rnode([], depth + 5), rmem())
    kids = [None] * 16
    for i in range(16):
        if random.random() < 0.3: kids[i] = ('hash', rhash())
    bv = None
    if random.random() < 0.5: bv = rslot()
    if rem:
        if random.random() < 0.75: kids[rem[0]] = rchild(rem[1:], depth + 1)
        else: kids[rem[0]] = None
    elif bv is not None and bv[0] == 'ref' and random.random() < 0.7:
        bv = ('val', [1, 2, 3])
    return ('branch', bv, kids, rmem())
def rchild(rem, depth): return rnode_c(rem, depth)
CHAIN = [0.0]   # probability of an empty-key extension chain above a path node
LONG = [0]      # if > 0: one chain of this length above the root
def chainLen():
    r = random.random()
    if r < 0.5: return random.randrange(1, 4)
    if r < 0.8: return random.randrange(4, 16)
    return random.randrange(16, 51)
def eextChain(t, k):
    for _ in range(k):
        # rarely an unrevealed child: the walk dead-ends there (instance skipped)
        t = ('ext', [], t, rmem())
    return t
def rnode_c(rem, depth):
    t = rnode(rem, depth)
    if random.random() < CHAIN[0]: t = eextChain(t, chainLen())
    return t
def rroot():
    t = rnode_c([0, 15], 0)
    if LONG[0]: t = eextChain(t, LONG[0])
    return t

# ---------------------------------------------------------------- record view (nodeV3)
class Rec: pass
def records(root, tau):
    """Revealed nodes -> records (id, depth, bytes, edges). Values -> value records."""
    recs, vals, edges, bmaps = {}, {}, [], {}
    ctr = [100]
    def rid():
        ctr[0] += 1; return ctr[0]
    def build(t, depth, parent=None):
        n = rid(); r = Rec(); r.id = n; r.depth = depth; r.node = t; r.bytes = ser(t); recs[n] = r
        r.parent = parent; r.cid = {}; r.res = n
        if t[0] == 'ext' and not t[1]:
            # empty-key extension: no edges; its walk target is its child's
            c = t[2]
            if c[0] != 'hash':
                cn = build(c, depth + 1, n); r.res = recs[cn].res
                for i in range(32): r.cid[6 + i] = cn
            return n
        if t[0] == 'leaf':
            k = t[1]
            for i, x in enumerate(k): edges.append((n, i, x, n, i + 1, EK_KEY))
            if t[2][0] == 'val':
                v = rid(); vals[v] = t[2][1]; edges.append((n, len(k), END, v, 0, EK_VAL))
            edges.append((n, len(k), END, n, len(k), EK_LEND))
        elif t[0] == 'ext':
            k = t[1]; c = t[2]
            cres = None
            if c[0] != 'hash':
                cn = build(c, depth + 1, n); cres = recs[cn].res
                off = 5 + len(hexPrefix(k, False))
                for i in range(32): r.cid[off + i] = cn
            for i, x in enumerate(k[:-1]): edges.append((n, i, x, n, i + 1, EK_KEY))
            if cres is not None: edges.append((n, len(k) - 1, k[-1], cres, 0, EK_KEY))
            else: edges.append((n, len(k) - 1, k[-1], n, len(k), EK_KEY))
        else:
            bv, kids = t[1], t[2]
            off = 1 + (36 if bv is not None else 0) + 2
            for i, c in enumerate(kids):
                if c is None: continue
                if c[0] != 'hash':
                    cn = build(c, depth + 1, n); cr = recs[cn].res
                    edges.append((n, 0, i, cr, 0, EK_DOWN))
                    for ii in range(32): r.cid[off + ii] = cn
                off += 32
            if bv is not None and bv[0] == 'val':
                v = rid(); vals[v] = bv[1]; edges.append((n, 0, END, v, 0, EK_VAL))
            bmaps[n] = (sum(1 << i for i in range(16) if kids[i] is not None), 1 if bv is not None else 0)
        return n
    r0 = build(root, 0)
    edges.append((0, tau, START, recs[r0].res, 0, EK_DOWN))
    return r0, recs, vals, edges, bmaps

def walk(edges, bmaps, tau):
    """walkV3 over [START, 0, 15, END]; returns rows (mode, e, bm, hv) or None if stuck."""
    emap = {}
    for e in edges: emap.setdefault((e[0], e[1]), []).append(e)
    rows = []
    e0 = [e for e in edges if e[0] == 0 and e[1] == tau][0]
    rows.append(('S', e0)); pos = (e0[3], e0[4]); absent = False
    for t, s in enumerate([0, 15, END]):
        if absent: rows.append(('D', None)); continue
        last = (t == 2)
        cand = [e for e in emap.get(pos, []) if e[2] == s and ((e[5] == EK_VAL) if last else e[5] in (EK_DOWN, EK_KEY))]
        if cand:
            e = cand[0]; rows.append(('S', e)); pos = (e[3], e[4]); continue
        ck = [e for e in emap.get(pos, []) if e[5] in (EK_KEY, EK_LEND) and e[2] != s]
        if ck:
            rows.append(('K', ck[0])); absent = True; continue
        if pos[1] == 0 and pos[0] in bmaps:
            bm, hv = bmaps[pos[0]]
            if (s == END and hv == 0) or (s < 16 and not (bm >> s) & 1):
                rows.append(('B', (pos[0], 0), bm, hv)); absent = True; continue
        return None
    return rows

# ---------------------------------------------------------------- AIR
def parse(s):
    toks = s.replace('(', ' ( ').replace(')', ' ) ').split()
    def go(i):
        assert toks[i] == '('
        op = toks[i + 1]; i += 2; args = []
        while toks[i] != ')':
            if toks[i] == '(':
                a, i = go(i); args.append(a)
            else:
                args.append(int(toks[i])); i += 1
        return (op, args), i + 1
    out = []; i = 0
    while i < len(toks):
        e, i = go(i); out.append(e)
    return out
def ev(e, row, nxt, first, last):
    op, a = e
    if op == 'k': return a[0] % P
    if op == 'c': return (nxt if a[1] else row).get(a[0], 0) % P
    if op == 'F': return 1 if first else 0
    if op == 'L': return 1 if last else 0
    if op == 'T': return 0 if last else 1
    if op == '+': return (ev(a[0], row, nxt, first, last) + ev(a[1], row, nxt, first, last)) % P
    if op == '*':
        x = ev(a[0], row, nxt, first, last)
        return 0 if x == 0 else x * ev(a[1], row, nxt, first, last) % P
    if op == '-': return (-ev(a[0], row, nxt, first, last)) % P
    raise Exception(op)

def pysrc(e):
    op, a = e
    if op == 'k': return str(a[0])
    if op == 'c': return '%s.get(%d,0)' % ('N' if a[1] else 'R', a[0])
    if op in ('F', 'L', 'T'): return op
    if op == '+': return '(%s+%s)' % (pysrc(a[0]), pysrc(a[1]))
    if op == '*': return '(%s*%s)' % (pysrc(a[0]), pysrc(a[1]))
    if op == '-': return '(-%s)' % pysrc(a[0])
    raise Exception(op)

NEGS = []
AIR = sys.argv[1] if len(sys.argv) > 1 else 'ups_air.txt'
CONS, INTS = [], []
for line in open(AIR):
    if line.startswith('C '): CONS.append(parse(line[2:])[0])
    elif line.startswith('I '):
        parts = line.split(' ', 3)
        es = parse(parts[3])
        INTS.append((int(parts[1]), int(parts[2]), es[0], es[1:]))
# all constraints compiled into one function of (row, next row, isFirst, isLast, isTransition)
CFUN = eval('lambda R,N,F,L,T: [' + ','.join(pysrc(e) for e in CONS) + ']')

# ---------------------------------------------------------------- column map (Ups.lean)
C = dict(act=0, wk=1, vb=2, qb=3, sf=4, wt1=5, wt2=6, wt3=7, pf=8, pl=9, tau=10, N0=11, N1=12, N2=13,
         L0=14, L1=15, L2=16, cLP=17, cBR=18, cBV=19, cBI=20, cLSa=21, cLSb=22, cLSc=23, cESl0=24,
         cESl1=25, cESn0=26, cESn1=27, dd0=28, dd1=29, dd2=30, ts1=31, ts2=32, ts3=33, ti0=34,
         ti1=35, ti2=36, tX=37, px=42, bmL=43, bmH=44, pres=45, vid=46, nQ=47, rlen=48,
         j=49, kRDB=50, kRDE=51, kRLP=52, kRBR=53, kRBV=54, kRBI=55, kMVL=56, kMVE=57, kNLF=58,
         kWEX=59, kSPB=60, sd0=65, sd1=66, sd2=67, sN=68, plen=69, qtl=70, qte=71, qtb1=72,
         qtb2=73, qhk=74, qodd=75, nokey=76, nochild=77, qlen=78, rootP=79, jm=80, clen=81,
         Kc=82, eL=83, eS=84, useA=85, bN=86, bL=87, cO=88, cS=89, Cc=90, neg=91, phk=92,
         podd=93, vcp=94, xcp=95, ba0=96, ba1=97, spY1=98, spY2=99,
         nN=49, nI=50, nib=51, nN2=52, nI2=53, ek=54, inv=55, hv=56, wbm=57, enter=58, lv0=59,
         lv1=60, lv2=61, trm=62,
         qpos=100, b=101, rd=102, rb=103, spos=104, u=105, sTAG=106, sHPL=107, sHPF=108,
         sKEY=109, sVLEN=110, sVH=111, sBM=112, sCH=113, sMEM=114, fs=115, fe=116, idx=117,
         fw=118, lastw=119, wfr=120, tgt=121, wy=122, wn=123, gD=124, dI=125, dL=126, cp=127,
         aft=128, gMs=168, gMr=169, rx=170, mBv=171, mCv=172, mS=173, mK=174, mB=175,
         dep0=176, dep1=177, dep2=178, kPT=179, up=180, rc=181, pdep=182, cN=183, rcid=184, rdc=185)
def XB(i): return 38 + i
def JO(i): return 60 + i
def REG(i): return 129 + i
def LR(i): return 161 + i
def SR(i): return 164 + i
WIDTH = 186
KIND = ['RDB', 'RDE', 'RLP', 'RBR', 'RBV', 'RBI', 'MVL', 'MVE', 'NLF', 'WEX', 'SPB', 'PT']
CASES = ['LP', 'BR', 'BV', 'BI', 'LSa', 'LSb', 'LSc', 'ESl0', 'ESl1', 'ESn0', 'ESn1']
def upsId(tau, jx):
    assert 0 <= jx < 512
    return 12 + 16 * (512 * tau + jx)
def inv(x): return pow(x % P, P - 2, P)

STATES = ['sTAG', 'sHPL', 'sHPF', 'sKEY', 'sVLEN', 'sVH', 'sBM', 'sCH', 'sMEM']
def fields(t):
    """Field list [(state, len, extra)] of node t (Q side), windows annotated with child idx."""
    if t[0] in ('leaf', 'ext'):
        hp = hexPrefix(t[1], t[0] == 'leaf')
        f = [('sTAG', 1), ('sHPL', 4), ('sHPF', 1)]
        if len(hp) > 1: f.append(('sKEY', len(hp) - 1))
        f += [('sVLEN', 4), ('sVH', 32)] if t[0] == 'leaf' else [('sCH', 32)]
        return f + [('sMEM', 8)]
    f = [('sTAG', 1)]
    if t[1] is not None: f += [('sVLEN', 4), ('sVH', 32)]
    f.append(('sBM', 2))
    f += [('sCH', 32)] * sum(1 for c in t[2] if c is not None)
    return f + [('sMEM', 8)]

# ---------------------------------------------------------------- generator
def gen(root, tau, v, maxQ=4):
    r0, recs, vals, edges, bmaps = records(root, tau)
    wr = walk(edges, bmaps, tau)
    if wr is None: return None
    spec = upsert(root, [0, 15], v)
    assert spec is not None
    L = len(v)
    seg = {}
    # walk-derived
    lv = 0; Ns = [wr[0][1][3]]; tstar = None; I = None; x = 0; mode_t = None; termrec = None
    rows = []
    for t, w in enumerate(wr):
        row = {C['act']: 1, C['wk']: 1}
        if t == 0: row[C['sf']] = 1
        else: row[[0, C['wt1'], C['wt2'], C['wt3']][t]] = 1
        sym = [START, 0, 15, END][t]
        if w[0] in ('S', 'K'):
            e = w[1]
            for nm, val in zip(['nN', 'nI', 'nib', 'nN2', 'nI2', 'ek'], e): row[C[nm]] = val
            row[C['mS' if w[0] == 'S' else 'mK']] = 1
            if w[0] == 'K': row[C['inv']] = inv(sym - e[2])
        elif w[0] == 'B':
            row[C['mB']] = 1; row[C['nN']] = w[1][0]; row[C['nI']] = 0; row[C['wbm']] = w[2]; row[C['hv']] = w[3]
            if t in (1, 2):
                for i in range(16): row[REG(i)] = (w[2] >> i) & 1
        if t >= 1:
            for l in range(3): row[C['lv%d' % l]] = 1 if lv == l else 0
        if t >= 1 and w[0] == 'S' and t < 3:
            ent = 1 if w[1][4] == 0 else 0
            row[C['enter']] = ent
            if ent: lv += 1; Ns.append(w[1][3])
        if t >= 1 and tstar is None and (w[0] in ('K', 'B') or (t == 3 and w[0] == 'S')):
            tstar = t; row[C['trm']] = 1; I = row[C['nI']]; mode_t = w[0]; termrec = row[C['nN']]
            D = lv
            if w[0] == 'K': x = w[1][2] if w[1][5] == EK_KEY else 0; ekt = w[1][5]
        rows.append(row)
    # drain rows: lv columns must still satisfy nothing; fine
    Dn = D
    assert Ns[Dn] == termrec
    P_D = recs[termrec].node
    # case
    if mode_t == 'S':
        case = 'LP' if P_D[0] == 'leaf' else 'BR'
    elif mode_t == 'B':
        case = 'BV' if tstar == 3 else 'BI'
    else:
        if ekt == EK_LEND: case = 'LSa'
        elif P_D[0] == 'leaf': case = 'LSb' if tstar == 3 else 'LSc'
        else:
            xe = 1 if len(P_D[1]) == I + 1 else 0
            case = ('ESl' if tstar == 3 else 'ESn') + str(xe)
    pw = 1 if (case not in ('LP', 'BR', 'BV', 'BI') and I >= 1) else 0
    # plan
    T = dict(LP=['RLP'], BR=['RBR'], BV=['RBV'], BI=['NLF', 'RBI'], LSa=['NLF', 'SPB'], LSb=['MVL', 'SPB'],
             LSc=['MVL', 'NLF', 'SPB'], ESl0=['MVE', 'SPB'], ESl1=['SPB'], ESn0=['MVE', 'NLF', 'SPB'],
             ESn1=['NLF', 'SPB'])[case]
    plan = list(T) + (['WEX'] if pw else [])
    nT = len(plan)
    # the path: every record from the root down to N_D (walked records and the empty-key
    # extensions between them, which the walk skips)
    chain = []; cur = Ns[Dn]
    while cur is not None: chain.append(cur); cur = recs[cur].parent
    chain.reverse()
    depD = recs[Ns[Dn]].depth
    assert len(chain) == depD + 1 and chain[0] == r0
    deps = [recs[n_].depth for n_ in Ns]
    lvl = {Ns[d]: d for d in range(Dn)}
    for dl in range(depD - 1, -1, -1):
        if chain[dl] not in lvl: assert recs[chain[dl]].node[0] == 'ext' and not recs[chain[dl]].node[1]
        plan.append('RD' if chain[dl] in lvl else 'PT')
    nQ = len(plan)
    # spec Q nodes along the path of the result
    pathres = []  # result nodes at depths 0..dep_D (positions of the path records)
    t = spec; key = [0, 15]
    for d in range(depD):
        pathres.append(t)
        if t[0] == 'branch': t = t[2][key[0]]; key = key[1:]
        else: key = key[len(t[1]):]; t = t[2]
    top = t; pathres.append(top)
    Q = {}
    # terminal nodes
    y = [0, 15, END][tstar - 1]
    if case in ('LP', 'BR', 'BV'): Q[1] = top
    elif case == 'BI': Q[2] = top; Q[1] = top[2][y]
    else:
        spb = top[2] if pw else top
        if pw: Q[len(T) + 1] = top
        Q[len(T)] = spb
        if case in ('LSa', 'LSc', 'ESn0', 'ESn1'): Q[{'LSa': 1, 'LSc': 2, 'ESn0': 2, 'ESn1': 1}[case]] = spb[2][y]
        if case in ('LSb', 'LSc', 'ESl0', 'ESn0'): Q[1] = spb[2][x]
    for d in range(depD):
        Q[nQ - d] = pathres[d]
    assert sorted(Q) == list(range(1, nQ + 1)), (Q.keys(), plan)
    seg.update({C['tau']: tau, C['N0']: Ns[0], C['N1']: Ns[1] if len(Ns) > 1 else 0, C['N2']: Ns[2] if len(Ns) > 2 else 0,
                C['L0']: L & 255, C['L1']: (L >> 8) & 255, C['L2']: L >> 16})
    for l in range(3): seg[C['dep%d' % l]] = deps[l] if l < len(deps) else 0
    for cn in CASES: seg[C['c' + cn]] = 1 if cn == case else 0
    for l in range(3): seg[C['dd%d' % l]] = 1 if Dn == l else 0
    for l in (1, 2, 3): seg[C['ts%d' % l]] = 1 if tstar == l else 0
    for l in range(3): seg[C['ti%d' % l]] = 1 if I == l else 0
    seg[C['tX']] = x
    for i in range(4): seg[XB(i)] = (x >> i) & 1
    seg[C['px']] = 1 << (x % 8)
    ay = 1 if case in ('LSa', 'LSc', 'ESn0', 'ESn1') else 0
    ax = 0 if case == 'LSa' else 1
    seg[C['bmL']] = ax * (1 - (x >> 3)) * (1 << (x % 8)) + ay * (1 if tstar == 1 else 0)
    seg[C['bmH']] = ax * (x >> 3) * (1 << (x % 8)) + 128 * ay * (0 if tstar == 1 else 1)
    pres = 1 if mode_t == 'S' else 0
    seg[C['pres']] = pres; seg[C['vid']] = wr[3][1][3] if pres else 0
    seg[C['nQ']] = nQ
    rootQ = Q[nQ]; seg[C['rlen']] = len(ser(rootQ))
    for r in rows: r.update(seg)
    # W0 MIDROOT reg = digest of root record; W3 = new root digest
    for i, x_ in enumerate(hashOf(root)): rows[0][REG(i)] = x_
    newroot = hashOf(spec)
    for i, x_ in enumerate(newroot): rows[3][REG(i)] = x_
    rows[3][C['gD']] = 1; rows[3][C['dI']] = upsId(tau, nQ); rows[3][C['dL']] = len(ser(rootQ))
    # value part
    for p_, by in enumerate(v):
        r = dict(seg); r.update({C['act']: 1, C['vb']: 1, C['qpos']: p_, C['b']: by})
        if p_ == 0: r[C['pf']] = 1
        if p_ == L - 1: r[C['pl']] = 1
        rows.append(r)
    for r in rows[4:]:
        r[C['sd%d' % Dn]] = 1; r[C['sN']] = Ns[Dn]; r[C['pdep']] = depD; r[C['rc']] = Dn
    # node parts
    exact = {}   # j -> exact mem
    memrows = {}  # j -> list of (rx, rb) for MEMD
    upb = []; memd_s = []; memd_r = []; digs = []
    Lb = [L & 255, (L >> 8) & 255, L >> 16, 0]
    srcs = {}
    for jj in range(1, nQ + 1):
        q = Q[jj]; kind = plan[jj - 1]
        if jj > nT:
            pdep = depD - (jj - nT); src = chain[pdep]; sd = lvl.get(src, 0)
            rcv = sum(1 for d in range(Dn) if deps[d] <= pdep)
        else:
            pdep = depD; src = Ns[Dn]; sd = Dn; rcv = Dn
        srcs[jj] = src
        cNv = srcs.get(jj - 1, 0)
        prec = recs[src]; pb = prec.bytes; plen = len(pb)
        if kind == 'RD': kind = 'RDB' if prec.node[0] == 'branch' else 'RDE'
        upv = 1 if jj > nT else 0
        qb_ = ser(q); qlen = len(qb_)
        pc = {C['j']: jj, C['sN']: src, C['plen']: plen, C['qlen']: qlen, C['rootP']: 1 if jj == nQ else 0,
              C['up']: upv, C['rc']: rcv, C['pdep']: pdep, C['cN']: cNv}
        for kn in KIND: pc[C['k' + kn]] = 1 if kn == kind else 0
        for i in range(1, 5): pc[JO(i)] = 1 if i == jj else 0
        for l in range(3): pc[C['sd%d' % l]] = 1 if sd == l else 0
        typ = q[0]
        pc[C['qtl']] = 1 if typ == 'leaf' else 0; pc[C['qte']] = 1 if typ == 'ext' else 0
        pc[C['qtb1']] = 1 if typ == 'branch' and q[1] is None else 0
        pc[C['qtb2']] = 1 if typ == 'branch' and q[1] is not None else 0
        if typ != 'branch':
            hp = hexPrefix(q[1], typ == 'leaf'); pc[C['qhk']] = len(hp); pc[C['qodd']] = len(q[1]) % 2
            pc[C['nokey']] = 1 if len(hp) == 1 else 0
        else:
            pc[C['nochild']] = 1 if all(c is None for c in q[2]) else 0
        pnode = prec.node
        if pnode[0] != 'branch':
            php = hexPrefix(pnode[1], pnode[0] == 'leaf'); pc[C['phk']] = len(php); pc[C['podd']] = len(pnode[1]) % 2
        spRecv = case in ('LSb', 'LSc', 'ESl0', 'ESn0')
        xcp = 1 if kind == 'SPB' and case in ('ESl1', 'ESn1') else 0
        pc[C['xcp']] = xcp
        if kind in ('RDB', 'RDE', 'WEX', 'PT'): pc[C['jm']] = jj - 1
        if kind == 'SPB' and spRecv: pc[C['jm']] = 1
        recvM = kind in ('RDB', 'RDE', 'WEX', 'PT') or (kind == 'SPB' and spRecv)
        if recvM: pc[C['clen']] = len(ser(Q[pc[C['jm']]]))
        useA = 1 if kind in ('RDB', 'RDE', 'RBR', 'RBV', 'RBI', 'MVE', 'PT') or xcp else 0
        bN = 1 if recvM else 0
        bL = cS = 1 if kind == 'RBR' else 0
        cO = 1 if kind in ('RDB', 'RDE', 'PT') else 0
        Cc = (50 + 2 * pc.get(C['phk'], 0)) if (kind == 'MVE' or xcp) else 0
        eL = 1 if kind in ('RLP', 'RBV', 'RBI', 'NLF', 'SPB') else 0
        eS = 1 if kind == 'MVL' or (kind == 'SPB' and case == 'LSa') else 0
        qhk = pc.get(C['qhk'], 0)
        Kc = {'RLP': 100 + 2 * qhk, 'RBV': 50, 'RBI': 102, 'MVL': 100 + 2 * qhk, 'MVE': 50 + 2 * qhk, 'NLF': 102,
              'WEX': 50 + 2 * qhk}.get(kind, 0)
        if kind == 'SPB': Kc = 202 if case == 'LSa' else (100 if case in ('LSb', 'ESl0', 'ESl1') else 152)
        for nm, val in dict(useA=useA, bN=bN, bL=bL, cO=cO, cS=cS, Cc=Cc, eL=eL, eS=eS, Kc=Kc).items(): pc[C[nm]] = val
        pc[C['ba0']] = 1 if kind == 'RBI' and tstar == 1 else 0
        pc[C['ba1']] = 128 if kind == 'RBI' and tstar != 1 else 0
        two = case in ('LSc', 'ESn0', 'ESn1')
        pc[C['spY1']] = 1 if kind == 'SPB' and (case == 'LSa' or (tstar == 1 and two)) else 0
        pc[C['spY2']] = 1 if kind == 'SPB' and tstar != 1 and two else 0
        s15 = (kind == 'RDB' and sd == 1) or (kind == 'RBI' and tstar != 1)
        pc[C['vcp']] = 1 if kind in ('RDB', 'RBI', 'MVL') or (kind == 'SPB' and case == 'LSa') else 0
        # memory arithmetic inputs
        m = int.from_bytes(bytes(pb[-8:]), 'little')
        sl = 0; slb = [0, 0, 0, 0]
        readsV = kind == 'RBR' or (pc[C['vcp']] and (pnode[0] == 'leaf' or (pnode[0] == 'branch' and pnode[1] is not None)))
        if readsV:
            off = 1 if pnode[0] == 'branch' else 5 + len(hexPrefix(pnode[1], True))
            slb = pb[off:off + 4]; sl = int.from_bytes(bytes(slb), 'little')
        Bx = exact[pc[C['jm']]] if recvM else (L if bL else 0)
        Cx = 0
        if cO: Cx = int.from_bytes(bytes(recs[cNv].bytes[-8:]), 'little')
        if cS: Cx = sl
        Cx += Cc
        Ax = m if useA else 0
        Ex = Kc + eL * L + eS * sl
        Tv = Ax + Bx - Cx; negv = 1 if Tv < 0 else 0; Tp = -Tv if negv else Tv
        R = Ex + (0 if negv else Tp)
        assert R == memD(q), (kind, case, R, memD(q))
        exact[jj] = R
        pc[C['neg']] = negv
        NEGS.append((kind, negv, R >= U64))
        # child exact limbs (B) and old (C) per row
        Blimbs = [0] * 8; Climbs = [0] * 8
        if recvM:
            Blimbs = memrows[pc[C['jm']]]['rx']; Climbs = memrows[pc[C['jm']]]['rb']
        # field walk
        fl = fields(q)
        assert sum(n_ for _, n_ in fl) == qlen
        qpos = 0; wins = [i for i, f in enumerate(fl) if f[0] == 'sCH']
        kidsl = [c for c in q[2] if c is not None] if typ == 'branch' else ([q[2]] if typ == 'ext' else [])
        kidslot = [i for i in range(16) if q[2][i] is not None] if typ == 'branch' else []
        prow = []
        aftv = 0
        e = (pc[C['phk']] - qhk) if kind in ('MVL', 'MVE') else 0
        SRv = list(slb)
        for fi, (st, ln) in enumerate(fl):
            wi = wins.index(fi) if st == 'sCH' else None
            for ix in range(ln):
                r = dict(seg); r.update(pc)
                r.update({C['act']: 1, C['qb']: 1, C['qpos']: qpos, C['b']: qb_[qpos], C[st]: 1, C['idx']: ix})
                if qpos == 0: r[C['pf']] = 1
                if ix == 0: r[C['fs']] = 1
                if ix == ln - 1: r[C['fe']] = 1
                if qpos == qlen - 1: r[C['pl']] = 1
                for i in range(3): r[LR(i)] = Lb[i + (ix if st in ('sVLEN', 'sMEM') else 0)] if (st in ('sVLEN', 'sMEM') and i + ix < 3) else (0 if st in ('sVLEN', 'sMEM') else Lb[i])
                # SR: rotation on VLEN, shift on MEM
                if st == 'sVLEN': cur = SRv[ix:] + SRv[:ix]
                elif st == 'sMEM': cur = (SRv + [0] * 8)[ix:ix + 4]
                else: cur = SRv
                for i in range(4): r[SR(i)] = cur[i]
                prow.append((r, st, ix, wi))
                qpos += 1
        # per-row semantics
        nw = len(wins)
        for (r, st, ix, wi) in prow:
            qp = r[C['qpos']]
            cpv = 0; rdv = 0; sp = None; fresh_digest = None
            if st == 'sCH':
                fwv = 1 if wi == 0 else 0; lw = 1 if wi == nw - 1 else 0
                tg = (lw if s15 else fwv)
                r[C['fw']] = fwv; r[C['lastw']] = lw; r[C['tgt']] = tg
                slot = kidslot[wi] if typ == 'branch' else None
                if kind in ('RDB', 'RBI'): wf = tg
                elif kind in ('RDE', 'WEX', 'PT'): wf = 1
                elif kind in ('RBR', 'RBV', 'MVE'): wf = 0
                elif kind == 'SPB':
                    wyv = 1 if slot == y else 0; r[C['wy']] = wyv
                    wf = 1 - (1 - wyv) * xcp
                else: wf = 0
                r[C['wfr']] = wf
                wnv = (1 if kind == 'RBI' and tg else 0) + (r.get(C['wy'], 0) if kind == 'SPB' else 0)
                r[C['wn']] = wnv
                cpv = 1 - wf
                if wf:
                    child = kidsl[wi]; fresh_digest = hashOf(child)
                    if wnv: jx, ln_ = jj - 1, 50
                    else: jx, ln_ = pc[C['jm']], pc[C['clen']]
                    if ix == 0: digs.append((upsId(tau, jx), ln_, fresh_digest))
            if st == 'sTAG': cpv = 1 if kind in ('RDB', 'RDE', 'RLP', 'RBR', 'RBI', 'PT') else 0
            if st in ('sHPL', 'sHPF'): cpv = 1 if kind in ('RDE', 'RLP', 'PT') else 0
            if st == 'sKEY': cpv = 1 if kind in ('RDE', 'RLP', 'MVL', 'MVE') else 0
            if st in ('sVLEN', 'sVH'): cpv = pc[C['vcp']]
            if st == 'sBM': cpv = 1 if kind in ('RDB', 'RBR', 'RBV', 'RBI') else 0
            extra = 0
            if st == 'sTAG' and (kind in ('RBV', 'MVL', 'MVE') or xcp): extra = 1
            if st == 'sHPL' and ix == 0 and kind in ('MVL', 'MVE'): extra = 1
            if st == 'sHPF' and kind in ('MVL', 'MVE'): extra = 1
            if st == 'sVLEN' and kind == 'RBR': extra = 1
            if st == 'sBM' and ix == 0 and xcp: extra = 1
            if st == 'sMEM' and kind != 'NLF': extra = 1
            rdcv = 1 if (st == 'sCH' and ix == 0 and r[C['tgt']] and upv) else 0
            r[C['rdc']] = rdcv
            rdv = cpv + extra + rdcv
            # aft
            if kind == 'RBV': aftv = 1 if st in ('sBM', 'sCH', 'sMEM') else 0
            if kind == 'RBI':
                if st == 'sCH': aftv = (1 - r[C['fw']]) * (1 if tstar == 1 else 0)
                elif st == 'sMEM': aftv = 1
                else: aftv = 0
            r[C['aft']] = aftv
            if rdv:
                if st == 'sMEM': sp = plen - 8 + ix
                elif kind in ('RDB', 'RDE', 'RLP', 'RBR', 'PT'): sp = qp
                elif kind == 'RBV': sp = qp - 36 * aftv
                elif kind == 'RBI': sp = qp - 32 * aftv
                elif kind in ('MVL', 'MVE'):
                    sp = 5 if st == 'sTAG' else (1 if st == 'sHPL' else qp + e)
                elif kind == 'SPB':
                    sp = {'sTAG': 5, 'sBM': 1}.get(st)
                    if st in ('sVLEN', 'sVH'): sp = plen - 45 + qp
                    if st == 'sCH': sp = plen - 40 + ix
                assert sp is not None, (kind, st)
                r[C['spos']] = sp; r[C['rb']] = pb[sp]
                # cid: the provider row's window column (free off windows: 0 here)
                cidv = cNv if rdcv else prec.cid.get(sp, 0)
                r[C['rcid']] = cidv
                upb.append((src, sp, pb[sp], plen, prec.depth, cidv))
            r[C['cp']] = cpv; r[C['rd']] = rdv
            if (st in ('sTAG', 'sHPF')) and rdv and not cpv:
                rbv = r[C['rb']]
                for i in range(4): r[REG(i)] = (rbv >> (4 + i)) & 1; r[REG(4 + i)] = (rbv >> i) & 1
            if fresh_digest is not None:
                for i in range(32 - ix): r[REG(i)] = fresh_digest[ix + i]
                if ix == 0: r[C['gD']] = 1; r[C['dI']] = digs[-1][0]; r[C['dL']] = digs[-1][1]
            if st == 'sVH' and not cpv:
                vd = sha(v)
                for i in range(32 - ix): r[REG(i)] = vd[ix + i]
                if ix == 0:
                    r[C['gD']] = 1; r[C['dI']] = upsId(tau, 0); r[C['dL']] = L; digs.append((upsId(tau, 0), L, vd))
        # MEM arithmetic
        mrows = [pr for pr in prow if pr[1] == 'sMEM']
        tl = (Tp).to_bytes(16, 'little'); Rl = R.to_bytes(16, 'little')
        ci = 0; ci2 = 0; rxl = []; rbl = []
        for (r, st, ix, wi) in mrows:
            A = r[C['rb']] if useA else 0
            Bv = (Blimbs[ix] if recvM else (Lb[ix] if (bL and ix < 4) else 0))
            Cv = (Climbs[ix] if cO else 0) + (slb[ix] if (cS and ix < 4) else 0) + (Cc if ix == 0 else 0)
            X1 = A + Bv - Cv
            Ein = (Kc if ix == 0 else 0) + (eL * Lb[ix] if ix < 4 else 0) + (eS * slb[ix] if ix < 4 else 0)
            sig = -1 if negv else 1
            tt = tl[ix]
            num = sig * X1 + ci - tt
            assert num % 256 == 0; co = num // 256
            num2 = Ein + (0 if negv else tt) + ci2 - Rl[ix]
            assert num2 % 256 == 0; co2 = num2 // 256
            if ix == 7: assert co == Tp >> 64, (co, Tp >> 64)
            cbv = co if ix == 7 else co + 3
            assert 0 <= cbv < 8 and 0 <= co2 < 8, (cbv, co2)
            for i in range(8): r[REG(i)] = (tt >> i) & 1
            for i in range(3): r[REG(8 + i)] = (cbv >> i) & 1; r[REG(11 + i)] = (co2 >> i) & 1
            r[REG(14)] = ci % P; r[REG(15)] = ci2; r[REG(16)] = X1 % P; r[REG(17)] = Ein
            H = (0 if negv else Tp >> 64) + co2 if ix == 7 else 0
            if ix == 7: assert H == R >> 64
            rxv = Rl[ix] + 256 * H
            r[C['rx']] = rxv
            if recvM: r[C['mBv']] = Blimbs[ix]; r[C['mCv']] = Climbs[ix]; r[C['gMr']] = 1
            if jj != nQ and kind != 'NLF':
                r[C['gMs']] = 1; memd_s.append((tau, jj, ix, rxv, r[C['rb']], qlen))
            if recvM: memd_r.append((tau, pc[C['jm']], ix, Blimbs[ix], Climbs[ix], pc[C['clen']]))
            rxl.append(rxv); rbl.append(r.get(C['rb'], 0))
            ci = co; ci2 = co2
        memrows[jj] = dict(rx=rxl, rb=rbl)
        rows += [pr[0] for pr in prow]
        # check spec bytes of Q against the spec
        assert qb_ == ser(q)
    # pad
    rows.append({})
    rows.append({})
    return dict(rows=rows, spec=spec, newroot=newroot, upb=upb, recs=recs, memd=(memd_s, memd_r), digs=digs,
                case=case, D=Dn, nQ=nQ, chain=chain, nPT=plan.count('PT'), edges=edges, bmaps=bmaps, wr=wr, Q=Q, tau=tau, v=v, vals=vals)

def check(g):
    rows = g['rows']; n = len(rows)
    bad = []
    for ri in range(n):
        row = rows[ri]; nxt = rows[(ri + 1) % n]
        last = ri == n - 1
        for ci_, x in enumerate(CFUN(row, nxt, 1 if ri == 0 else 0, 1 if last else 0, 0 if last else 1)):
            if x % P != 0:
                bad.append((ri, ci_))
    # bytes / digests
    byid = {}
    for row in rows:
        if row.get(C['vb']) or row.get(C['qb']):
            byid.setdefault(upsId(row[C['tau']], row.get(C['j'], 0)), {})[row[C['qpos']]] = row[C['b']]
    for (iid, ln, dg) in g['digs']:
        bs = byid[iid]; assert sorted(bs) == list(range(len(bs))) and len(bs) == ln, (iid, ln, len(bs))
        assert sha([bs[i] for i in range(ln)]) == dg
    for jj, q in g['Q'].items():
        bs = byid[upsId(g['tau'], jj)]; assert [bs[i] for i in range(len(bs))] == ser(q)
    assert hashOf(g['Q'][g['nQ']]) == g['newroot'] == hashOf(g['spec'])
    # UPB: path records only, bytes exact
    path = set(g['chain'])
    for (src, sp, by, ln, dep, cid) in g['upb']:
        rr = g['recs'][src]
        assert src in path
        assert rr.bytes[sp] == by and len(rr.bytes) == ln and rr.depth == dep
        if sp in rr.cid: assert rr.cid[sp] == cid, (sp, rr.cid[sp], cid)
    s, r = g['memd']; assert sorted(s) == sorted(r), (s, r)
    return bad

def main(seed=1, iters=300, chain=0.0, long_=0):
    random.seed(seed)
    CHAIN[0] = chain; LONG[0] = long_
    stats = {}; fails = 0; tried = 0; ptStats = {}; maxNQ = 0
    names = {v: k for k, v in C.items()}
    while tried < iters:
        root = rroot()
        tau = random.randrange(0, 5)
        v = [random.randrange(256) for _ in range(random.randrange(1, 60))]
        g = gen(root, tau, v)
        if g is None: continue
        tried += 1
        stats[(g['case'], g['D'])] = stats.get((g['case'], g['D']), 0) + 1
        b_ = 0 if g['nPT'] == 0 else (1 if g['nPT'] < 4 else (2 if g['nPT'] < 16 else 3))
        ptStats[b_] = ptStats.get(b_, 0) + 1; maxNQ = max(maxNQ, g['nQ'])
        bad = check(g)
        if bad:
            fails += 1
            if fails <= 3:
                print('FAIL case', g['case'], 'D', g['D'], 'nQ', g['nQ'], 'first bad', bad[:8])
                ri, ci_ = bad[0]
                row = g['rows'][ri]
                print(' row', ri, {names.get(k, k): v for k, v in row.items() if v})
                print(' constraint #', ci_)
    print('instances', tried, 'failures', fails)
    from collections import Counter
    print('neg/overflow by kind', sorted(Counter(NEGS).items()))
    for k in sorted(stats): print(' ', k, stats[k])
    print('pass-through parts per instance: 0 / 1-3 / 4-15 / >=16:', [ptStats.get(i, 0) for i in range(4)],
          'max nQ', maxNQ)
    return fails

if __name__ == '__main__':
    a = sys.argv
    sys.exit(1 if main(int(a[2]) if len(a) > 2 else 1, int(a[3]) if len(a) > 3 else 300,
                       float(a[4]) if len(a) > 4 else 0.0, int(a[5]) if len(a) > 5 else 0) else 0)
