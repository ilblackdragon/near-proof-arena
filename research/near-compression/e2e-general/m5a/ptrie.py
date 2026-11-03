"""Python transcription of the spec's partial-trie functions, used only by the M5a trace
generator (never by a check): `NearSpec.PTrie` (`spec/lean/NearSpec/Trie.lean`), `upsert`
(`TrieUpsert.lean`), `del`/`squashBranch`/`extendChild`/`revealAll`/`applyChanges`/`rootHash`
(`spec/lean/v3/NearSpecV3/D2/{Trie,State}.lean`).

Tries are tuples:
  ('hash', h) | ('leaf', key, slot, mem) | ('ext', key, child, mem) | ('branch', vslot|None, kids, mem)
with `kids` a 16-list of child-or-None and `slot = (len, vh)` (the `valueRef`; the spec's
`Slot.val v` and `Slot.ref len h` have the same `valueRef`, which is all hashing reads).
Each operation also records the path cases it took (`ops`), which is what the AIR must cover.
"""
import hashlib
import struct

EMPTY_ROOT = bytes(32)


def sha(b):
    return hashlib.sha256(b).digest()


def u16(n):
    return struct.pack('<H', n)


def u32(n):
    return struct.pack('<I', n)


def u64(n):
    return struct.pack('<Q', n)


def nibbles(b):
    out = []
    for x in b:
        out += [x >> 4, x & 15]
    return out


def pack_nibbles(n):
    return bytes(n[i] * 16 + n[i + 1] for i in range(0, len(n) - 1, 2))


def hex_prefix(nibs, leaf):
    lb = 32 if leaf else 0
    if len(nibs) % 2 == 1:
        return bytes([16 + nibs[0] + lb]) + pack_nibbles(nibs[1:])
    return bytes([lb]) + pack_nibbles(nibs)


def hp_decode(b):
    if not b:
        return None
    f = b[0]
    hi = f >> 4
    if hi > 3:
        return None
    odd = hi % 2 == 1
    if not odd and f % 16 != 0:
        return None
    return (([f % 16] if odd else []) + nibbles(b[1:]), (hi // 2) % 2 == 1)


def leaf_mem(k, vlen):
    return 50 + 2 * len(hex_prefix(k, True)) + (vlen + 50)


def ext_own_mem(k):
    return 50 + 2 * len(hex_prefix(k, False))


def value_mem(vlen):
    return vlen + 50


def mem_of(t):
    return None if t[0] == 'hash' else t[3]


def memD(t):
    m = mem_of(t)
    return 0 if m is None else m


def bitmap(kids):
    return sum(1 << i for i, c in enumerate(kids) if c is not None)


def serialize(t):
    """`PTrie.hashOf`'s preimage of a revealed node (children by hash)."""
    k = t[0]
    if k == 'leaf':
        hp = hex_prefix(t[1], True)
        return b'\x00' + u32(len(hp)) + hp + u32(t[2][0]) + t[2][1] + u64(t[3])
    if k == 'ext':
        hp = hex_prefix(t[1], False)
        return b'\x03' + u32(len(hp)) + hp + hash_of(t[2]) + u64(t[3])
    hs = b''.join(hash_of(c) for c in t[2] if c is not None)
    if t[1] is None:
        return b'\x01' + u16(bitmap(t[2])) + hs + u64(t[3])
    return b'\x02' + u32(t[1][0]) + t[1][1] + u16(bitmap(t[2])) + hs + u64(t[3])


#: Mutation testing only: `id(node) -> hash` claimed for a tampered node by its parent.
OVERRIDE = {}


def hash_of(t):
    if t[0] == 'hash':
        return t[1]
    if id(t) in OVERRIDE:
        return OVERRIDE[id(t)]
    return sha(serialize(t))


def root_hash(t):
    return EMPTY_ROOT if t is None else hash_of(t)


# ---------------------------------------------------------------- reveal (decode)
def le(b):
    return int.from_bytes(b, 'little')


def kid_hashes(bm, bs):
    out = []
    for i in range(16):
        if bm >> i & 1:
            out.append(bs[:32])
            bs = bs[32:]
        else:
            out.append(None)
    return out


def reveal_all(store, h, fuel=10000):
    """`revealAll` (value slots kept as refs)."""
    if fuel == 0 or h not in store:
        return ('hash', h)
    node = store[h]
    if len(node) < 9:
        return ('hash', h)
    mem = le(node[-8:])
    body = node[:-8]
    tag, rest = body[0], body[1:]
    if tag in (0, 3):
        klen = le(rest[:4])
        d = hp_decode(rest[4:4 + klen])
        if d is None or d[1] != (tag == 0):
            return ('hash', h)
        r2 = rest[4 + klen:]
        if tag == 0:
            if len(r2) != 36:
                return ('hash', h)
            return ('leaf', d[0], (le(r2[:4]), r2[4:]), mem)
        if len(r2) != 32:
            return ('hash', h)
        return ('ext', d[0], reveal_all(store, r2, fuel - 1), mem)
    if tag in (1, 2):
        v = None
        if tag == 2:
            if len(rest) < 36:
                return ('hash', h)
            v = (le(rest[:4]), rest[4:36])
            rest = rest[36:]
        bm = le(rest[:2])
        hs = kid_hashes(bm, rest[2:])
        if len(rest) != 2 + 32 * sum(1 for x in hs if x is not None):
            return ('hash', h)
        return ('branch', v, [None if x is None else reveal_all(store, x, fuel - 1) for x in hs], mem)
    return ('hash', h)


# ---------------------------------------------------------------- find
def find(t, key):
    """`PTrie.findRef`: None undetermined, ('absent',) or ('present', slot)."""
    k = t[0]
    if k == 'hash':
        return None
    if k == 'leaf':
        return ('present', t[2]) if t[1] == key else ('absent',)
    if k == 'ext':
        if key[:len(t[1])] == t[1]:
            return find(t[2], key[len(t[1]):])
        return ('absent',)
    if not key:
        return ('absent',) if t[1] is None else ('present', t[1])
    c = t[2][key[0]]
    if c is None:
        return ('absent',)
    return find(c, key[1:])


# ---------------------------------------------------------------- upsert
def common_prefix(a, b):
    n = 0
    while n < min(len(a), len(b)) and a[n] == b[n]:
        n += 1
    return a[:n]


def kids_with(pairs):
    ks = [None] * 16
    for i, c in pairs:
        ks[i] = c
    return ks


def new_leaf(k, s):
    return ('leaf', k, s, leaf_mem(k, s[0]))


def wrap_ext(p, b):
    if not p:
        return b
    return ('ext', p, b, ext_own_mem(p) + memD(b))


def split_leaf(k, s, key, v, ops):
    p = common_prefix(k, key)
    a, b = k[len(p):], key[len(p):]
    if not a and b:
        ops.append('splitLeaf.oldEnds')
        return wrap_ext(p, ('branch', s, kids_with([(b[0], new_leaf(b[1:], v))]),
                            50 + value_mem(s[0]) + leaf_mem(b[1:], v[0])))
    if a and not b:
        ops.append('splitLeaf.newEnds')
        return wrap_ext(p, ('branch', v, kids_with([(a[0], ('leaf', a[1:], s, leaf_mem(a[1:], s[0])))]),
                            50 + value_mem(v[0]) + leaf_mem(a[1:], s[0])))
    if a and b:
        ops.append('splitLeaf.two')
        return wrap_ext(p, ('branch', None, kids_with([(a[0], ('leaf', a[1:], s, leaf_mem(a[1:], s[0]))),
                                                         (b[0], new_leaf(b[1:], v))]),
                            50 + leaf_mem(a[1:], s[0]) + leaf_mem(b[1:], v[0])))
    ops.append('splitLeaf.same')
    return new_leaf(key, v)


def split_ext(k, c, m, key, v, ops):
    p = common_prefix(k, key)
    cm = max(m - ext_own_mem(k), 0)
    xs = k[len(p):]
    x, xs = xs[0], xs[1:]
    sub = c if not xs else ('ext', xs, c, ext_own_mem(xs) + cm)
    sub_mem = cm if not xs else ext_own_mem(xs) + cm
    b = key[len(p):]
    if not b:
        ops.append('splitExt.newEnds')
        return wrap_ext(p, ('branch', v, kids_with([(x, sub)]), 50 + value_mem(v[0]) + sub_mem))
    ops.append('splitExt.two')
    return wrap_ext(p, ('branch', None, kids_with([(x, sub), (b[0], new_leaf(b[1:], v))]),
                        50 + sub_mem + leaf_mem(b[1:], v[0])))


def nsub(a, b):
    return a - b if a >= b else 0


def upsert(t, key, v, ops):
    k = t[0]
    if k == 'hash':
        return None
    if k == 'leaf':
        if t[1] == key:
            ops.append('leaf.replace')
            return new_leaf(key, v)
        return split_leaf(t[1], t[2], key, v, ops)
    if k == 'ext':
        if key[:len(t[1])] == t[1]:
            cm = mem_of(t[2])
            c2 = upsert(t[2], key[len(t[1]):], v, ops)
            if cm is None or c2 is None:
                return None
            ops.append('ext.descend')
            return ('ext', t[1], c2, nsub(t[3] + memD(c2), cm))
        return split_ext(t[1], t[2], t[3], key, v, ops)
    bv, cs, m = t[1], t[2], t[3]
    if not key:
        ops.append('branch.value')
        return ('branch', v, cs, nsub(m + value_mem(v[0]), value_mem(bv[0]) if bv else 0))
    c = cs[key[0]]
    cs2 = list(cs)
    if c is None:
        ops.append('branch.newChild')
        cs2[key[0]] = new_leaf(key[1:], v)
        return ('branch', bv, cs2, nsub(m + leaf_mem(key[1:], v[0]), 0))
    cm = mem_of(c)
    c2 = upsert(c, key[1:], v, ops)
    if cm is None or c2 is None:
        return None
    ops.append('branch.descend')
    cs2[key[0]] = c2
    return ('branch', bv, cs2, nsub(m + memD(c2), cm))


# ---------------------------------------------------------------- delete
def extend_child(k, c, ops):
    if c[0] == 'hash':
        return 'missing'
    if c[0] == 'leaf':
        ops.append('extend.leaf')
        return ('leaf', k + c[1], c[2], leaf_mem(k + c[1], c[2][0]))
    if c[0] == 'branch':
        ops.append('extend.branch')
        return ('ext', k, c, ext_own_mem(k) + c[3])
    ops.append('extend.ext')
    return ('ext', k + c[1], c[2], ext_own_mem(k + c[1]) + nsub(c[3], ext_own_mem(c[1])))


def squash_branch(v, cs, m, ops):
    pres = [(i, c) for i, c in enumerate(cs) if c is not None]
    if not pres and v is None:
        ops.append('squash.empty')
        return None
    if not pres:
        ops.append('squash.valueLeaf')
        return ('leaf', [], v, leaf_mem([], v[0]))
    if len(pres) == 1 and v is None:
        ops.append('squash.oneChild')
        return extend_child([pres[0][0]], pres[0][1], ops)
    ops.append('squash.keep')
    return ('branch', v, cs, m)


MISSING = 'missing'


def delete(t, key, ops):
    """`PTrie.del`: MISSING | (deleted, trie-or-None)."""
    k = t[0]
    if k == 'hash':
        return MISSING
    if k == 'leaf':
        if t[1] == key:
            ops.append('leaf.delete')
            return (True, None)
        ops.append('leaf.absent')
        return (False, t)
    if k == 'ext':
        if key[:len(t[1])] == t[1]:
            if mem_of(t[2]) is None:
                return MISSING
            r = delete(t[2], key[len(t[1]):], ops)
            if r == MISSING:
                return MISSING
            if not r[0]:
                return (False, t)
            if r[1] is None:
                ops.append('ext.childGone')
                return (True, None)
            e = extend_child(t[1], r[1], ops)
            return MISSING if e == MISSING else (True, e)
        ops.append('ext.absent')
        return (False, t)
    v, cs, m = t[1], t[2], t[3]
    if not key:
        if v is None:
            return (False, t)
        r = squash_branch(None, cs, nsub(m, value_mem(v[0])), ops)
        return MISSING if r == MISSING else (True, r)
    c = cs[key[0]]
    if c is None:
        ops.append('branch.absent')
        return (False, t)
    cm = mem_of(c)
    if cm is None:
        return MISSING
    r = delete(c, key[1:], ops)
    if r == MISSING:
        return MISSING
    if not r[0]:
        return (False, t)
    ops.append('branch.descendDel')
    cs2 = list(cs)
    cs2[key[0]] = r[1]
    new = 0 if r[1] is None else memD(r[1])
    s = squash_branch(v, cs2, nsub(m, cm) + new, ops)
    return MISSING if s == MISSING else (True, s)


def apply_change(t, key, v, ops):
    """`applyChange` (`t = None` is the empty trie). Returns ('ok', t') or ('missing',)."""
    nk = nibbles(key)
    if v is not None:
        if t is None:
            ops.append('empty.insert')
            return ('ok', new_leaf(nk, v))
        r = upsert(t, nk, v, ops)
        return ('missing',) if r is None else ('ok', r)
    if t is None:
        return ('ok', None)
    r = delete(t, nk, ops)
    return ('missing',) if r == MISSING else ('ok', r[1])


def apply_changes(t, changes):
    """`applyChanges` over sorted changes [(key bytes, slot|None)]; returns (trie, per-change ops)."""
    allops = []
    for k, v in changes:
        ops = []
        r = apply_change(t, k, v, ops)
        if r[0] != 'ok':
            raise ValueError('finalize: missing node on path of %s' % k.hex())
        t = r[1]
        allops.append(ops)
    return t, allops
