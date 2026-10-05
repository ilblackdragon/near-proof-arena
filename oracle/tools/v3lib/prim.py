"""Primitives for the independent v3 checker, written from the nearcore 2.13.4
sources and the third-party crates it pins (rand 0.8.5, rand_chacha 0.3.1,
reed-solomon-erasure 6.0.0, borsh 1.5.3, near-account-id 2.0.0).

Nothing here is derived from the Lean formalization.
"""
import hashlib
import math
import struct
from fractions import Fraction


class Reject(Exception):
    """In D0 (as far as decided so far) but nearcore's validator rejects."""


class OOD(Exception):
    """The case leaves domain D0."""


class DecodeError(Reject):
    pass


def sha(b):
    return hashlib.sha256(b).digest()


def u8(x): return bytes([x])
def u16(x): return struct.pack('<H', x)
def u32(x): return struct.pack('<I', x)
def u64(x): return struct.pack('<Q', x)
def u128(x): return x.to_bytes(16, 'little')
def bstr(b): return u32(len(b)) + b


U64_MAX = (1 << 64) - 1
U128_MAX = (1 << 128) - 1
ZERO32 = b'\0' * 32


class R:
    """Strict borsh-style reader."""

    def __init__(self, b, i=0):
        self.b, self.i = b, i

    def take(self, n):
        if n < 0 or self.i + n > len(self.b):
            raise DecodeError("truncated")
        r = self.b[self.i:self.i + n]
        self.i += n
        return r

    def u8(self): return self.take(1)[0]
    def u16(self): return struct.unpack('<H', self.take(2))[0]
    def u32(self): return struct.unpack('<I', self.take(4))[0]
    def u64(self): return struct.unpack('<Q', self.take(8))[0]
    def u128(self): return int.from_bytes(self.take(16), 'little')
    def hash(self): return self.take(32)
    def bytes(self): return self.take(self.u32())

    def boolean(self):
        b = self.u8()
        if b > 1:
            raise DecodeError("bool")
        return b == 1

    def option(self, f):
        t = self.u8()
        if t == 0:
            return None
        if t == 1:
            return f()
        raise DecodeError("option tag")

    def vec(self, f):
        return [f() for _ in range(self.u32())]

    def account(self):
        s = self.bytes()
        if not valid_account_id(s):
            raise DecodeError("invalid AccountId")
        return s

    def end(self):
        if self.i != len(self.b):
            raise DecodeError("trailing bytes")


# ---------------- near-account-id 2.0.0 ----------------
def valid_account_id(s):
    if not (2 <= len(s) <= 64):
        return False
    last_sep = True
    for c in s:
        if 97 <= c <= 122 or 48 <= c <= 57:
            sep = False
        elif c in b'-_.':
            sep = True
            if last_sep:
                return False
        else:
            return False
        last_sep = sep
    return not last_sep


_HEX = set(b'0123456789abcdef')


def is_eth_implicit(s): return len(s) == 42 and s[:2] == b'0x' and all(c in _HEX for c in s[2:])
def is_near_deterministic(s): return len(s) == 42 and s[:2] == b'0s' and all(c in _HEX for c in s[2:])
def is_near_implicit(s): return len(s) == 64 and all(c in _HEX for c in s)


def account_type(s):
    if is_eth_implicit(s): return 'eth'
    if is_near_implicit(s): return 'near'
    if is_near_deterministic(s): return 'det'
    return 'named'


# ---------------- keys / signatures (core/crypto/src/signature.rs) ----------------
PK_LEN = {0: 32, 1: 64, 2: 1952}
SIG_LEN = {0: 64, 1: 65, 2: 3309}


def read_public_key(r):
    t = r.u8()
    if t not in PK_LEN:
        raise DecodeError("PublicKey tag")
    return u8(t) + r.take(PK_LEN[t])


def read_signature(r):
    t = r.u8()
    if t not in SIG_LEN:
        raise DecodeError("Signature tag")
    s = r.take(SIG_LEN[t])
    if t == 0 and s[63] & 0xE0:
        raise DecodeError("ed25519 signature high bits")
    return u8(t) + s


# ---------------- merkle (core/primitives/src/merkle.rs) ----------------
def merkle_root_of_hashes(hs):
    """merklize over already-hashed leaves (leaf = sha256(borsh(item)))."""
    if not hs:
        return ZERO32
    hs = list(hs)
    while len(hs) > 1:
        hs = [sha(hs[i] + hs[i + 1]) if i + 1 < len(hs) else hs[i] for i in range(0, len(hs), 2)]
    return hs[0]


def merklize(items_borsh):
    return merkle_root_of_hashes([sha(x) for x in items_borsh])


def compute_root_from_path(path, item_hash):
    res = item_hash
    for h, d in path:
        res = sha(h + res) if d == 0 else sha(res + h)
    return res


# ---------------- ChaCha20 (rand_chacha 0.3.1) + rand 0.8.5 ----------------
_M = 0xffffffff


def _rotl(x, n):
    return ((x << n) & _M) | (x >> (32 - n))


def chacha20_block(key_words, counter):
    st = [0x61707865, 0x3320646e, 0x79622d32, 0x6b206574] + key_words + \
         [counter & _M, (counter >> 32) & _M, 0, 0]
    x = list(st)

    def qr(a, b, c, d):
        x[a] = (x[a] + x[b]) & _M; x[d] = _rotl(x[d] ^ x[a], 16)
        x[c] = (x[c] + x[d]) & _M; x[b] = _rotl(x[b] ^ x[c], 12)
        x[a] = (x[a] + x[b]) & _M; x[d] = _rotl(x[d] ^ x[a], 8)
        x[c] = (x[c] + x[d]) & _M; x[b] = _rotl(x[b] ^ x[c], 7)
    for _ in range(10):
        qr(0, 4, 8, 12); qr(1, 5, 9, 13); qr(2, 6, 10, 14); qr(3, 7, 11, 15)
        qr(0, 5, 10, 15); qr(1, 6, 11, 12); qr(2, 7, 8, 13); qr(3, 4, 9, 14)
    return [(x[i] + st[i]) & _M for i in range(16)]


class ChaCha20Rng:
    """ChaCha20Rng::from_seed(seed): 20 rounds, 64-bit block counter from 0,
    stream id 0; next_u32 reads the keystream word by word."""

    def __init__(self, seed):
        assert len(seed) == 32
        self.key = list(struct.unpack('<8I', seed))
        self.counter = 0
        self.buf = []
        self.pos = 0

    def next_u32(self):
        if self.pos >= len(self.buf):
            self.buf = chacha20_block(self.key, self.counter)
            self.counter += 1
            self.pos = 0
        w = self.buf[self.pos]
        self.pos += 1
        return w

    def gen_range_u32(self, ubound):
        """rng.gen_range(0..ubound as u32) — UniformInt<u32>::sample_single
        (widening multiply with the `(range << lz) - 1` zone)."""
        rng = ubound & _M  # high - low + 1 with low = 0, high = ubound - 1
        if rng == 0:
            return self.next_u32()
        lz = 32 - rng.bit_length()
        zone = ((rng << lz) & _M) - 1
        zone &= _M
        while True:
            v = self.next_u32()
            m = v * rng
            hi, lo = m >> 32, m & _M
            if lo <= zone:
                return hi

    def shuffle(self, lst):
        """SliceRandom::shuffle (rand 0.8.5)."""
        for i in range(len(lst) - 1, 0, -1):
            j = self.gen_range_u32(i + 1)
            lst[i], lst[j] = lst[j], lst[i]


# ---------------- GF(2^8) Reed-Solomon (reed-solomon-erasure 6.0.0 galois_8) ----------------
def _gf_tables():
    log = [0] * 256
    b = 1
    for lg in range(255):
        log[b] = lg
        b <<= 1
        if b >= 256:
            b = (b - 256) ^ 29
    exp = [0] * 510
    for i in range(1, 256):
        exp[log[i]] = i
        exp[log[i] + 255] = i
    return log, exp


GF_LOG, GF_EXP = _gf_tables()


def gf_mul(a, b):
    if a == 0 or b == 0:
        return 0
    return GF_EXP[GF_LOG[a] + GF_LOG[b]]


def gf_div(a, b):
    if b == 0:
        raise ZeroDivisionError
    if a == 0:
        return 0
    lr = GF_LOG[a] - GF_LOG[b]
    if lr < 0:
        lr += 255
    return GF_EXP[lr]


def gf_exp(a, n):
    if n == 0:
        return 1
    if a == 0:
        return 0
    return GF_EXP[(GF_LOG[a] * n) % 255]


_MUL_ROWS = {}


def _mul_row(c):
    t = _MUL_ROWS.get(c)
    if t is None:
        t = bytes(gf_mul(c, x) for x in range(256))
        _MUL_ROWS[c] = t
    return t


def gf_mat_inv(m):
    n = len(m)
    a = [list(row) + [1 if i == j else 0 for j in range(n)] for i, row in enumerate(m)]
    for col in range(n):
        piv = next((r for r in range(col, n) if a[r][col] != 0), None)
        if piv is None:
            raise ValueError("singular")
        a[col], a[piv] = a[piv], a[col]
        inv = gf_div(1, a[col][col])
        a[col] = [gf_mul(inv, x) for x in a[col]]
        for r in range(n):
            if r != col and a[r][col]:
                f = a[r][col]
                a[r] = [x ^ gf_mul(f, y) for x, y in zip(a[r], a[col])]
    return [row[n:] for row in a]


_RS_CACHE = {}


def rs_matrix(d, total):
    key = (d, total)
    if key not in _RS_CACHE:
        v = [[gf_exp(r, c) for c in range(d)] for r in range(total)]
        top_inv = gf_mat_inv([row[:] for row in v[:d]])
        m = []
        for r in range(total):
            m.append([0] * d)
            for c in range(d):
                acc = 0
                for k in range(d):
                    acc ^= gf_mul(v[r][k], top_inv[k][c])
                m[r][c] = acc
        _RS_CACHE[key] = m
    return _RS_CACHE[key]


def rs_encode(data, d, total):
    """near_primitives::reed_solomon::reed_solomon_encode -> (parts, encoded_length)."""
    n = len(data)
    plen = (n + d - 1) // d
    padded = data + b'\0' * (d * plen - n)
    parts = [padded[k * plen:(k + 1) * plen] for k in range(d)]
    m = rs_matrix(d, total)
    for r in range(d, total):
        acc = 0
        for c in range(d):
            coef = m[r][c]
            if coef:
                acc ^= int.from_bytes(parts[c].translate(_mul_row(coef)), 'little')
        parts.append(acc.to_bytes(plen, 'little'))
    return parts, n


def encoded_merkle_root(data, d, total):
    parts, n = rs_encode(data, d, total)
    return merklize([bstr(p) for p in parts]), n


# ---------------- congestion control floats (core/primitives/src/congestion_info.rs) ----------------
MAX_CONGESTION_INCOMING_GAS = 400_000_000_000_000_000
MAX_CONGESTION_OUTGOING_GAS = 10_000_000_000_000_000
MAX_CONGESTION_MEMORY = 1_000_000_000
MAX_CONGESTION_MISSED = 125
MAX_OUTGOING_GAS = 300_000_000_000_000_000
MIN_OUTGOING_GAS = 1_000_000_000_000_000
ALLOWED_SHARD_OUTGOING_GAS = 1_000_000_000_000_000


def clamped_f64_fraction(value, mx):
    # Python float(int) rounds to nearest-even exactly as Rust `as f64`;
    # float division is IEEE binary64.
    if mx <= value:
        return 1.0
    return float(value) / float(mx)


def congestion_level(info, missed):
    delayed, buffered, rbytes, _allowed = info
    inc = clamped_f64_fraction(delayed, MAX_CONGESTION_INCOMING_GAS)
    out = clamped_f64_fraction(buffered, MAX_CONGESTION_OUTGOING_GAS)
    mem = clamped_f64_fraction(rbytes, MAX_CONGESTION_MEMORY)
    mis = 0.0 if missed <= 1 else clamped_f64_fraction(missed, MAX_CONGESTION_MISSED)
    return max(max(max(inc, out), mem), mis)


def rust_round_to_u64(x):
    """f64::round (half away from zero) then `as u64` (saturating, NaN -> 0)."""
    if x != x:
        return 0
    if x <= 0:
        # round of a value in (-0.5, 0] is -0.0 -> 0; negatives saturate to 0
        return 0
    if x == math.inf:
        return U64_MAX
    f = Fraction(x)
    fl = math.floor(f)
    r = fl + 1 if f - fl >= Fraction(1, 2) else fl
    return min(int(r), U64_MAX)


def mix(left, right, ratio):
    left_part = float(left) * (1.0 - ratio)
    right_part = float(right) * ratio
    total = left_part + right_part
    return rust_round_to_u64(total)


def outgoing_gas_limit(info, missed, sender_shard):
    lvl = congestion_level(info, missed)
    if lvl == 1.0:
        return ALLOWED_SHARD_OUTGOING_GAS if sender_shard == info[3] else 0
    return mix(MAX_OUTGOING_GAS, MIN_OUTGOING_GAS, lvl)


# ---------------- partial trie (core/store/src/trie) ----------------
NODE_COST = 50
BYTE_OF_KEY = 2
BYTE_OF_VALUE = 1


def nibbles(key):
    out = []
    for b in key:
        out += [b >> 4, b & 15]
    return out


def hp_encode(nibs, leaf):
    """NibbleSlice::encoded."""
    odd = len(nibs) % 2
    out = bytearray([(0x10 + nibs[0] if odd else 0) + (0x20 if leaf else 0)])
    i = odd
    while i < len(nibs):
        out.append(nibs[i] * 16 + nibs[i + 1])
        i += 2
    return bytes(out)


def hp_decode(e):
    """NibbleSlice::from_encoded (the leaf flag is ignored)."""
    if not e:
        raise Reject("empty encoded nibble slice")
    out = [e[0] & 15] if e[0] & 0x10 else []
    return out + nibbles(e[1:])


def value_mem(vlen):
    return vlen * BYTE_OF_VALUE + NODE_COST


class Node:
    __slots__ = ('kind', 'key', 'vref', 'children', 'child', 'mem')

    # kind: 'leaf' (key=nibbles, vref=(len,hash)), 'branch' (vref or None, children dict),
    #       'ext' (key=nibbles, child=hash)
    def __init__(self, kind, key=None, vref=None, children=None, child=None, mem=0):
        self.kind, self.key, self.vref, self.children, self.child, self.mem = kind, key, vref, children, child, mem

    def direct(self):
        if self.kind == 'leaf':
            return NODE_COST + len(hp_encode(self.key, True)) * BYTE_OF_KEY + value_mem(self.vref[0])
        if self.kind == 'ext':
            return NODE_COST + len(hp_encode(self.key, False)) * BYTE_OF_KEY
        return NODE_COST + (value_mem(self.vref[0]) if self.vref is not None else 0)

    def encode(self):
        if self.kind == 'leaf':
            body = u8(0) + bstr(hp_encode(self.key, True)) + u32(self.vref[0]) + self.vref[1]
        elif self.kind == 'ext':
            body = u8(3) + bstr(hp_encode(self.key, False)) + self.child
        else:
            bm = 0
            hs = b''
            for i in range(16):
                if i in self.children:
                    bm |= 1 << i
                    hs += self.children[i]
            if self.vref is None:
                body = u8(1) + u16(bm) + hs
            else:
                body = u8(2) + u32(self.vref[0]) + self.vref[1] + u16(bm) + hs
        return body + u64(self.mem)


def decode_node(data):
    r = R(data)
    t = r.u8()
    if t == 0:
        key = hp_decode(r.bytes())
        vref = (r.u32(), r.hash())
        n = Node('leaf', key=key, vref=vref)
    elif t in (1, 2):
        vref = (r.u32(), r.hash()) if t == 2 else None
        bm = r.u16()
        ch = {}
        for i in range(16):
            if bm >> i & 1:
                ch[i] = r.hash()
        n = Node('branch', vref=vref, children=ch)
    elif t == 3:
        key = hp_decode(r.bytes())
        n = Node('ext', key=key, child=r.hash())
    else:
        raise Reject("bad trie node tag")
    n.mem = r.u64()
    r.end()
    return n


class PartialTrie:
    """Trie over a recorded PartialState: nodes and values looked up by sha256.
    A lookup that needs a missing node/value raises Reject (MissingTrieValue)."""

    def __init__(self, values, root):
        self.store = {}
        for v in values:
            self.store[sha(v)] = v
        self.root = root
        self.cache = {}

    def node(self, h):
        n = self.cache.get(h)
        if n is None:
            if h not in self.store:
                raise Reject("MissingTrieValue (node)")
            n = decode_node(self.store[h])
            self.cache[h] = n
        return n

    def get(self, key):
        if self.root == ZERO32:
            return None
        nib = nibbles(key)
        h = self.root
        while True:
            n = self.node(h)
            if n.kind == 'leaf':
                if n.key != nib:
                    return None
                vh = n.vref[1]
                break
            if n.kind == 'ext':
                if nib[:len(n.key)] != n.key:
                    return None
                nib = nib[len(n.key):]
                h = n.child
                continue
            if not nib:
                if n.vref is None:
                    return None
                vh = n.vref[1]
                break
            if nib[0] not in n.children:
                return None
            h = n.children[nib[0]]
            nib = nib[1:]
        if vh not in self.store:
            raise Reject("MissingTrieValue (value)")
        return self.store[vh]

    # ---- insert (core/store/src/trie/ops/insert_delete.rs), canonical result ----
    def _put(self, n):
        data = n.encode()
        h = sha(data)
        self.store[h] = data
        self.cache[h] = n
        return h, n.mem

    def _leaf(self, key, vref):
        n = Node('leaf', key=key, vref=vref)
        n.mem = n.direct()
        return n

    def _ins(self, h, key, vref):
        """returns (new_hash, new_mem) of the subtree after inserting key->vref."""
        if h is None:
            return self._put(self._leaf(key, vref))
        n = self.node(h)
        if n.kind == 'leaf':
            if n.key == key:
                return self._put(self._leaf(key, vref))
            cp = 0
            while cp < min(len(n.key), len(key)) and n.key[cp] == key[cp]:
                cp += 1
            br = Node('branch', vref=None, children={})
            mem = 0
            old_rest, new_rest = n.key[cp:], key[cp:]
            if not old_rest:
                br.vref = n.vref
            else:
                ch, m = self._put(self._leaf(old_rest[1:], n.vref))
                br.children[old_rest[0]] = ch
                mem += m
            if not new_rest:
                br.vref = vref
            else:
                ch, m = self._put(self._leaf(new_rest[1:], vref))
                br.children[new_rest[0]] = ch
                mem += m
            br.mem = br.direct() + mem
            return self._wrap(key[:cp], br)
        if n.kind == 'ext':
            k = n.key
            child_mem = n.mem - n.direct()
            if key[:len(k)] == k:
                ch, m = self._ins(n.child, key[len(k):], vref)
                e = Node('ext', key=k, child=ch)
                e.mem = e.direct() + m
                return self._put(e)
            cp = 0
            while cp < min(len(k), len(key)) and k[cp] == key[cp]:
                cp += 1
            br = Node('branch', vref=None, children={})
            mem = 0
            if len(k) - cp - 1 > 0:
                e = Node('ext', key=k[cp + 1:], child=n.child)
                e.mem = e.direct() + child_mem
                ch, m = self._put(e)
            else:
                ch, m = n.child, child_mem
            br.children[k[cp]] = ch
            mem += m
            new_rest = key[cp:]
            if not new_rest:
                br.vref = vref
            else:
                ch2, m2 = self._put(self._leaf(new_rest[1:], vref))
                br.children[new_rest[0]] = ch2
                mem += m2
            br.mem = br.direct() + mem
            return self._wrap(key[:cp], br)
        # branch
        if not key:
            nb = Node('branch', vref=vref, children=dict(n.children))
            nb.mem = n.mem - n.direct() + nb.direct()
            return self._put(nb)
        c = key[0]
        nb = Node('branch', vref=n.vref, children=dict(n.children))
        if c in n.children:
            old_mem = self.node(n.children[c]).mem
            ch, m = self._ins(n.children[c], key[1:], vref)
        else:
            old_mem = 0
            ch, m = self._ins(None, key[1:], vref)
        nb.children[c] = ch
        nb.mem = n.mem - old_mem + m
        return self._put(nb)

    def _wrap(self, prefix, br):
        bh, bm = self._put(br)
        if not prefix:
            return bh, bm
        e = Node('ext', key=prefix, child=bh)
        e.mem = e.direct() + bm
        return self._put(e)

    def insert(self, key, value):
        vref = (len(value), sha(value))
        self.store[vref[1]] = value
        h = None if self.root == ZERO32 else self.root
        self.root, _ = self._ins(h, nibbles(key), vref)
