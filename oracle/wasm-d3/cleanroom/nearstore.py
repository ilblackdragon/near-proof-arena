"""Clean-room trie-backed contract storage with trie-node accounting (checkpoint 3b).

Written from docs/research/d3-trie-accounting.md section 4 (prose spec) only; points where the prose is
silent were settled by black-box comparison against nearcore op-level traces (README, "Storage cost
model (checkpoint 3b)").  Standard library only.

Two storage backends share one interface used by nearwasm's storage_* host functions:

  write(inst, k, v)  -> old value or None   (charges evicted bytes and trie nodes)
  remove(inst, k)    -> old value or None   (charges removed bytes and trie nodes)
  read(inst, k)      -> value or None       (charges value bytes / large-read overhead)
  has(inst, k)       -> bool                (charges nothing)

`MockStore` is the harness's MockedExternal (a plain map, no trie-node charges, no evicted/removed byte
charges).  `TrieStore` is the chunk-scoped trie External of section 4.
"""
import os
import struct

import nearcrypto

# Deliberately wrong variants, for showing the difftest is sensitive to each prose rule (README 3b):
# NEARSTORE_ABLATE=fresh-cache,no-overlay,keep-failed,read-touch-path,no-read-warm,no-value-touch,
#                  ttn-before-bytes,no-absent-remove
ABLATE = set(filter(None, os.environ.get("NEARSTORE_ABLATE", "").split(",")))

LARGE_READ_THRESHOLD = 4000
REMOVED = object()


class StorageError(Exception):
    """A storage error (missing trie node or value): not a contract failure."""


class MockStore:
    def __init__(self):
        self.trie = {}

    def write(self, inst, k, v):
        old = self.trie.get(k)
        self.trie[k] = v
        return old

    def remove(self, inst, k):
        return self.trie.pop(k, None)

    def read(self, inst, k):
        v = self.trie.get(k)
        if v is not None:
            _value_charges(inst, v)
        return v

    def has(self, inst, k):
        return k in self.trie

    def items(self):
        return self.trie.items()


def _value_charges(inst, v):
    from nearwasm import pay
    pay(inst, "storage_read_value_byte", len(v))
    if len(v) > LARGE_READ_THRESHOLD:
        pay(inst, "storage_large_read_overhead_base")
        pay(inst, "storage_large_read_overhead_byte", len(v))


# ---------------------------------------------------------------- nodes (4.2)

def _hp_decode(b):
    """Hex-prefix key -> (nibbles, is_leaf)."""
    if not b:
        raise StorageError("empty hex-prefix key")
    f = b[0] >> 4
    nib = []
    if f & 1:
        nib.append(b[0] & 0xF)
    elif b[0] & 0xF:
        raise StorageError("bad hex-prefix padding")
    for x in b[1:]:
        nib.append(x >> 4)
        nib.append(x & 0xF)
    return tuple(nib), bool(f & 2)


def _children(body, p):
    (bm,) = struct.unpack_from("<H", body, p)
    p += 2
    ch = {}
    for i in range(16):
        if bm >> i & 1:
            ch[i] = body[p:p + 32]
            p += 32
    return ch, p


def parse_node(raw):
    """borsh(RawTrieNodeWithSize) -> ('leaf', key, (len, hash)) | ('ext', key, child)
    | ('branch', children, valueref|None).  The trailing 8-byte memory_usage is ignored."""
    if len(raw) < 9:
        raise StorageError("short node")
    body = raw[:-8]
    tag = body[0]
    if tag == 0 or tag == 3:
        (n,) = struct.unpack_from("<I", body, 1)
        key, _ = _hp_decode(body[5:5 + n])
        p = 5 + n
        if tag == 0:
            (vl,) = struct.unpack_from("<I", body, p)
            return ("leaf", key, (vl, body[p + 4:p + 36]))
        return ("ext", key, body[p:p + 32])
    if tag == 1:
        ch, _ = _children(body, 1)
        return ("branch", ch, None)
    if tag == 2:
        (vl,) = struct.unpack_from("<I", body, 1)
        vr = (vl, body[5:37])
        ch, _ = _children(body, 37)
        return ("branch", ch, vr)
    raise StorageError(f"bad node tag {tag}")


def nibbles(key):
    out = []
    for x in key:
        out.append(x >> 4)
        out.append(x & 0xF)
    return tuple(out)


# ---------------------------------------------------------------- chunk state (4.1, 4.4)

class Chunk:
    """Pre-state (root + recorded storage), committed overlay and the chunk-scoped accounting cache."""

    def __init__(self, root, blobs):
        self.root = root
        self.db = {nearcrypto.sha256(b): b for b in blobs}
        self.parsed = {}
        self.overlay = {}
        self.cache = set()
        self.n_db = 0
        self.n_mem = 0

    def touch(self, h):
        if h in self.cache:
            self.n_mem += 1
        else:
            self.n_db += 1
            self.cache.add(h)

    def node(self, h):
        n = self.parsed.get(h)
        if n is None:
            raw = self.db.get(h)
            if raw is None:
                raise StorageError("MissingTrieValue")
            n = self.parsed[h] = parse_node(raw)
        return n

    def lookup(self, key):
        """-> (visited hashes root first, valueref or None)."""
        visited = []
        if self.root == bytes(32):
            return visited, None
        h = self.root
        rest = nibbles(key)
        while True:
            n = self.node(h)
            visited.append(h)
            if n[0] == "leaf":
                return visited, (n[2] if n[1] == rest else None)
            if n[0] == "ext":
                k = n[1]
                if rest[:len(k)] != k:
                    return visited, None
                rest = rest[len(k):]
                h = n[2]
                continue
            if not rest:
                return visited, n[2]
            c = n[1].get(rest[0])
            if c is None:
                return visited, None
            rest = rest[1:]
            h = c

    def value(self, vr):
        v = self.db.get(vr[1])
        if v is None:
            raise StorageError("MissingTrieValue")
        return v

    def store_for(self, account):
        if "fresh-cache" in ABLATE:
            self.cache = set()
        if "no-overlay" in ABLATE:
            self.overlay = {}
        return TrieStore(self, account)


class TrieStore:
    """One call's External: the chunk's committed overlay plus this call's own changes."""

    def __init__(self, chunk, account):
        self.c = chunk
        self.prefix = b"\x09" + account + b","
        self.changes = {}

    def _ov(self, fk):
        if fk in self.changes:
            return True, self.changes[fk]
        if fk in self.c.overlay:
            return True, self.c.overlay[fk]
        return False, None

    def finish(self, ok):
        """End of the call: keep this call's changes iff its receipt succeeded (4.4)."""
        if ok or "keep-failed" in ABLATE:
            self.c.overlay.update(self.changes)

    def _commit_nodes(self, inst, db0, mem0):
        from nearwasm import pay
        pay(inst, "touching_trie_node", self.c.n_db - db0)
        pay(inst, "read_cached_trie_node", self.c.n_mem - mem0)

    def _evict(self, inst, fk, B):
        from nearwasm import pay
        c = self.c
        db0, mem0 = c.n_db, c.n_mem
        hit, ov = self._ov(fk)
        if hit:
            if ov is REMOVED:
                return None
            pay(inst, B, len(ov))
            return ov
        visited, vr = c.lookup(fk)
        for h in visited:
            c.touch(h)
        old = None
        if vr is not None and "ttn-before-bytes" in ABLATE:
            c.touch(vr[1])
            self._commit_nodes(inst, db0, mem0)
            pay(inst, B, vr[0])
            return c.value(vr)
        if vr is not None:
            pay(inst, B, vr[0])
            if "no-value-touch" not in ABLATE:
                c.touch(vr[1])
            old = c.value(vr)
        self._commit_nodes(inst, db0, mem0)
        return old

    def write(self, inst, k, v):
        fk = self.prefix + k
        old = self._evict(inst, fk, "storage_write_evicted_byte")
        self.changes[fk] = v
        return old

    def remove(self, inst, k):
        fk = self.prefix + k
        old = self._evict(inst, fk, "storage_remove_ret_value_byte")
        if old is None and "no-absent-remove" in ABLATE and not self._ov(fk)[0]:
            return None
        self.changes[fk] = REMOVED
        return old

    def read(self, inst, k):
        fk = self.prefix + k
        c = self.c
        hit, ov = self._ov(fk)
        if hit:
            if ov is REMOVED:
                return None
            _value_charges(inst, ov)
            return ov
        db0, mem0 = c.n_db, c.n_mem
        visited, vr = c.lookup(fk)
        if "read-touch-path" in ABLATE:
            for h in visited:
                c.touch(h)
        self._commit_nodes(inst, db0, mem0)
        if vr is None:
            return None
        _value_charges(inst, _Len(vr[0]))
        if "no-read-warm" not in ABLATE:
            c.touch(vr[1])
        return c.value(vr)

    def has(self, inst, k):
        fk = self.prefix + k
        hit, ov = self._ov(fk)
        if hit:
            return ov is not REMOVED
        _, vr = self.c.lookup(fk)
        return vr is not None

    def items(self):
        return ()


class _Len:
    """Stand-in carrying only a length (value charges before the value is fetched)."""
    __slots__ = ("n",)

    def __init__(self, n):
        self.n = n

    def __len__(self):
        return self.n
