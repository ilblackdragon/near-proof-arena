"""Partial trie for domain D2: lookups by reference, prefix iteration and batched
insert/delete exactly as nearcore 2.13.4 performs them on a trie built from a recorded
`PartialState` (the chunk validator's path):

  * lookups      core/store/src/trie/mod.rs:1270-1325 (`lookup_from_state_column`): every node
                 on the key's path is read; `get` then reads the value (`retrieve_value`),
                 `get_ref` / `contains` read no value;
  * iteration    core/store/src/trie/ops/iter.rs (`seek_prefix`, `iter_step`, `next`): the
                 disk-trie iterator reads every node of the prefix subtree and the value of
                 every key it yields;
  * update       core/store/src/trie/mod.rs:1678-1706 (`update_with_trie_storage`),
                 ops/insert_delete.rs (`generic_insert`, `generic_delete`), ops/squash.rs
                 (`squash_node`, `extend_child`), trie_storage_update.rs (`flatten_nodes`):
                 changes applied in key order to one arena of updated nodes; a stored node
                 is read when it is first moved to the arena (`ensure_updated`), values of
                 deleted keys are never read.

A node or value that the recorded state does not hold raises Reject (MissingTrieValue).
Nothing here is derived from the Lean formalization.
"""
from .prim import (Reject, sha, u8, u16, u32, u64, bstr, ZERO32, nibbles, hp_encode, decode_node,
                   NODE_COST, BYTE_OF_KEY, BYTE_OF_VALUE, PartialTrie)


def _value_mem(vlen):
    return vlen * BYTE_OF_VALUE + NODE_COST


class UNode:
    """An updated node: kind E (empty) / L (leaf) / B (branch) / X (extension).
    ext: nibble list; val: (len, hash, bytes-or-None); children: list of 16 entries
    None | ('o', hash) | ('u', id); child: ('o', hash) | ('u', id)."""
    __slots__ = ('kind', 'ext', 'val', 'children', 'child')

    def __init__(self, kind, ext=None, val=None, children=None, child=None):
        self.kind, self.ext, self.val, self.children, self.child = kind, ext, val, children, child

    def direct(self):
        k = self.kind
        if k == 'E':
            return 0
        if k == 'L':
            return NODE_COST + len(hp_encode(self.ext, True)) * BYTE_OF_KEY + _value_mem(self.val[0])
        if k == 'B':
            return NODE_COST + (_value_mem(self.val[0]) if self.val is not None else 0)
        return NODE_COST + len(hp_encode(self.ext, False)) * BYTE_OF_KEY


EMPTY = UNode('E')


def _cp(a, b):
    n = 0
    m = min(len(a), len(b))
    while n < m and a[n] == b[n]:
        n += 1
    return n


def _sat_sub(a, b):
    return a - b if a > b else 0


class Trie2(PartialTrie):
    """PartialTrie (v3lib.prim) plus the D2 operations."""

    def value(self, vh):
        if vh not in self.store:
            raise Reject("MissingTrieValue (value)")
        return self.store[vh]

    def get_ref(self, key):
        """(length, hash) of the value at key, or None; reads the path nodes only."""
        if self.root == ZERO32:
            return None
        nib = nibbles(key)
        h = self.root
        while True:
            n = self.node(h)
            if n.kind == 'leaf':
                return n.vref if n.key == nib else None
            if n.kind == 'ext':
                if nib[:len(n.key)] != n.key:
                    return None
                nib = nib[len(n.key):]
                h = n.child
                continue
            if not nib:
                return n.vref
            if nib[0] not in n.children:
                return None
            h = n.children[nib[0]]
            nib = nib[1:]

    # ------------------------------------------------------------------ iteration
    def iter_prefix(self, prefix):
        """Yields (key, value) for every key with the given prefix, in key order, reading
        exactly the nodes and values nearcore's DiskTrieIterator reads after seek_prefix."""
        key = nibbles(prefix)
        trail = []      # [node(or None for empty), status, prefix_boundary]
        key_nibbles = []
        ptr = None if self.root == ZERO32 else self.root
        prev = None
        while True:
            if prev is not None:
                prev[2] = True
            node = self.node(ptr) if ptr is not None else None
            crumb = [node, 'Entering', False]
            trail.append(crumb)
            prev = crumb
            if node is None:
                break
            if node.kind == 'leaf':
                if node.key[:len(key)] != key:          # !existing.starts_with(key)
                    key_nibbles.extend(node.key)
                    crumb[1] = 'Exiting'
                break
            if node.kind == 'branch':
                if not key:
                    break
                idx = key[0]
                key_nibbles.append(idx)
                crumb[1] = ('AtChild', idx)
                if idx in node.children:
                    ptr = node.children[idx]
                    key = key[1:]
                else:
                    crumb[2] = True
                    break
                continue
            # extension
            ek = node.key
            if key[:len(ek)] == ek:
                key = key[len(ek):]
                ptr = node.child
                crumb[1] = 'At'
                key_nibbles.extend(ek)
            else:
                if ek[:len(key)] != key:
                    crumb[1] = 'Exiting'
                    key_nibbles.extend(ek)
                break
        while True:
            if not trail:
                return
            last = trail[-1]
            node, status, boundary = last
            # increment
            if boundary:
                status = 'Exiting'
            elif node is None:
                status = 'Exiting'
            elif status == 'Entering':
                status = 'At'
            elif status == 'At' and node.kind == 'branch':
                status = ('AtChild', 0)
            elif isinstance(status, tuple) and node.kind == 'branch' and status[1] < 15:
                status = ('AtChild', status[1] + 1)
            else:
                status = 'Exiting'
            last[1] = status
            if status == 'Exiting':
                if node is not None:
                    if node.kind in ('leaf', 'ext'):
                        del key_nibbles[len(key_nibbles) - len(node.key):]
                    elif node.kind == 'branch':
                        key_nibbles.pop()
                trail.pop()
                continue
            if status == 'At':
                if node.kind == 'branch':
                    if node.vref is not None:
                        yield self._item(key_nibbles), self.value(node.vref[1])
                    continue
                if node.kind == 'leaf':
                    key_nibbles.extend(node.key)
                    yield self._item(key_nibbles), self.value(node.vref[1])
                    continue
                key_nibbles.extend(node.key)
                trail.append([self.node(node.child), 'Entering', False])
                continue
            i = status[1]
            if i == 0:
                key_nibbles.append(0)
            if i in node.children:
                if i != 0:
                    key_nibbles[-1] = i
                trail.append([self.node(node.children[i]), 'Entering', False])

    @staticmethod
    def _item(kn):
        return bytes(kn[i - 1] * 16 + kn[i] for i in range(1, len(kn), 2))

    # ------------------------------------------------------------------ update
    def update(self, changes):
        """Apply [(key, value-or-None)] (sorted by key) and return the new root."""
        self.arena = []
        self.mem = []
        root_id = self._ensure(('o', self.root))
        for k, v in changes:
            if v is not None:
                self._insert(root_id, nibbles(k), v)
            else:
                self._delete(root_id, nibbles(k))
        self.root = self._flatten(root_id)
        del self.arena, self.mem
        return self.root

    def _new(self, n, mem):
        self.arena.append(n)
        self.mem.append(mem)
        return len(self.arena) - 1

    def _take(self, i):
        n, m = self.arena[i], self.mem[i]
        assert n is not None
        self.arena[i] = None
        return n, m

    def _place(self, i, n, mem):
        assert self.arena[i] is None
        self.arena[i] = n
        self.mem[i] = mem

    def _ensure(self, c):
        if c[0] == 'u':
            return c[1]
        h = c[1]
        if h == ZERO32:
            return self._new(EMPTY, 0)
        raw = self.node(h)
        if raw.kind == 'leaf':
            n = UNode('L', ext=list(raw.key), val=(raw.vref[0], raw.vref[1], None))
        elif raw.kind == 'ext':
            n = UNode('X', ext=list(raw.key), child=('o', raw.child))
        else:
            ch = [None] * 16
            for i, x in raw.children.items():
                ch[i] = ('o', x)
            n = UNode('B', val=(raw.vref[0], raw.vref[1], None) if raw.vref is not None else None, children=ch)
        return self._new(n, raw.mem)

    def _calc_store(self, i, children_mem, n, old_child):
        m = children_mem + n.direct()
        if old_child is not None:
            m = _sat_sub(m, self.mem[old_child])
        self._place(i, n, m)

    def _insert(self, node_id, partial, value):
        vh = (len(value), sha(value), value)
        path = []
        while True:
            path.append(node_id)
            n, mem = self._take(node_id)
            children_mem = _sat_sub(mem, n.direct())
            if n.kind == 'E':
                leaf = UNode('L', ext=partial, val=vh)
                self._place(node_id, leaf, leaf.direct())
                break
            if n.kind == 'B':
                if not partial:
                    nb = UNode('B', val=vh, children=n.children)
                    self._place(node_id, nb, children_mem + nb.direct())
                    break
                ch = list(n.children)
                c = ch[partial[0]]
                new_id = self._ensure(c) if c is not None else self._new(EMPTY, 0)
                ch[partial[0]] = ('u', new_id)
                self._calc_store(node_id, children_mem, UNode('B', val=n.val, children=ch), new_id)
                node_id = new_id
                partial = partial[1:]
                continue
            if n.kind == 'L':
                existing = n.ext
                cp = _cp(partial, existing)
                if cp == len(existing) and cp == len(partial):
                    leaf = UNode('L', ext=existing, val=vh)
                    self._place(node_id, leaf, leaf.direct())
                    break
                if cp == 0:
                    ch = [None] * 16
                    if not existing:
                        cm = 0
                        br = UNode('B', val=n.val, children=ch)
                    else:
                        nl = UNode('L', ext=existing[1:], val=n.val)
                        cm = nl.direct()
                        ch[existing[0]] = ('u', self._new(nl, cm))
                        br = UNode('B', val=None, children=ch)
                    self._place(node_id, br, br.direct() + cm)
                    path.pop()
                    continue
                leaf = UNode('L', ext=existing[cp:], val=n.val)
                lid = self._new(leaf, leaf.direct())
                ext = UNode('X', ext=partial[:cp], child=('u', lid))
                self._place(node_id, ext, ext.direct())
                node_id = lid
                partial = partial[cp:]
                continue
            # extension
            existing = n.ext
            cp = _cp(partial, existing)
            if cp == 0:
                idx = existing[0]
                if len(existing) == 1:
                    child = n.child
                    child_mem = children_mem
                else:
                    inner = UNode('X', ext=existing[1:], child=n.child)
                    child_mem = children_mem + inner.direct()
                    child = ('u', self._new(inner, child_mem))
                ch = [None] * 16
                ch[idx] = child
                br = UNode('B', val=None, children=ch)
                self._place(node_id, br, br.direct() + child_mem)
                path.pop()
                continue
            if cp == len(existing):
                cid = self._ensure(n.child)
                nx = UNode('X', ext=existing, child=('u', cid))
                self._place(node_id, nx, nx.direct())
                node_id = cid
                partial = partial[cp:]
                continue
            inner = UNode('X', ext=existing[cp:], child=n.child)
            inner_mem = children_mem + inner.direct()
            iid = self._new(inner, inner_mem)
            cn = UNode('X', ext=existing[:cp], child=('u', iid))
            self._place(node_id, cn, cn.direct())
            node_id = iid
            partial = partial[cp:]
        for i in range(len(path) - 2, -1, -1):
            self.mem[path[i]] += self.mem[path[i + 1]]

    def _delete(self, node_id, partial):
        path = []
        deleted = True
        while True:
            path.append(node_id)
            n, mem = self._take(node_id)
            children_mem = _sat_sub(mem, n.direct())
            if n.kind == 'E':
                self._place(node_id, EMPTY, 0)
                deleted = False
                break
            if n.kind == 'L':
                if n.ext == partial:
                    self._place(node_id, EMPTY, 0)
                else:
                    self._place(node_id, n, mem)
                    deleted = False
                break
            if n.kind == 'B':
                if not partial:
                    if n.val is None:
                        self._place(node_id, n, mem)
                        deleted = False
                        break
                    self._calc_store(node_id, children_mem, UNode('B', val=None, children=n.children), None)
                    break
                c = n.children[partial[0]]
                if c is None:
                    self._place(node_id, n, mem)
                    deleted = False
                    break
                new_id = self._ensure(c)
                ch = list(n.children)
                ch[partial[0]] = ('u', new_id)
                self._calc_store(node_id, children_mem, UNode('B', val=n.val, children=ch), new_id)
                node_id = new_id
                partial = partial[1:]
                continue
            ek = n.ext
            if _cp(ek, partial) == len(ek):
                new_id = self._ensure(n.child)
                self._calc_store(node_id, children_mem, UNode('X', ext=ek, child=('u', new_id)), new_id)
                node_id = new_id
                partial = partial[len(ek):]
                continue
            self._place(node_id, n, mem)
            deleted = False
            break
        child_mem = 0
        for nid in reversed(path):
            self.mem[nid] += child_mem
            if deleted:
                self._squash(nid)
            child_mem = self.mem[nid]

    def _squash(self, nid):
        n, mem = self._take(nid)
        if n.kind == 'E':
            self._place(nid, EMPTY, 0)
            return
        if n.kind == 'L':
            raise AssertionError("squash of a leaf")
        if n.kind == 'B':
            ch = []
            for c in n.children:
                if c is not None and c[0] == 'u' and self.arena[c[1]] is not None and self.arena[c[1]].kind == 'E':
                    c = None
                ch.append(c)
            idxs = [i for i, c in enumerate(ch) if c is not None]
            if not idxs:
                if n.val is None:
                    self._place(nid, EMPTY, 0)
                else:
                    leaf = UNode('L', ext=[], val=n.val)
                    self._place(nid, leaf, leaf.direct())
            elif len(idxs) == 1 and n.val is None:
                self._extend_child(nid, [idxs[0]], ch[idxs[0]])
            else:
                self._place(nid, UNode('B', val=n.val, children=ch), mem)
            return
        self._extend_child(nid, n.ext, n.child)

    def _extend_child(self, nid, ext, child):
        cid = self._ensure(child)
        cn, cmem = self._take(cid)
        ccm = _sat_sub(cmem, cn.direct())
        if cn.kind == 'E':
            self._place(nid, EMPTY, 0)
        elif cn.kind == 'L':
            leaf = UNode('L', ext=list(ext) + cn.ext, val=cn.val)
            self._place(nid, leaf, leaf.direct())
        elif cn.kind == 'B':
            self._place(cid, cn, cmem)
            x = UNode('X', ext=list(ext), child=('u', cid))
            self._place(nid, x, cmem + x.direct())
        else:
            x = UNode('X', ext=list(ext) + cn.ext, child=cn.child)
            self._place(nid, x, x.direct() + ccm)

    def _flatten(self, i):
        n = self.arena[i]
        mem = self.mem[i]
        if n.kind == 'E':
            return ZERO32

        def vref(v):
            if v[2] is not None:
                self.store[v[1]] = v[2]
            return u32(v[0]) + v[1]
        if n.kind == 'L':
            body = u8(0) + bstr(hp_encode(n.ext, True)) + vref(n.val)
        elif n.kind == 'X':
            c = n.child
            ch = c[1] if c[0] == 'o' else self._flatten(c[1])
            body = u8(3) + bstr(hp_encode(n.ext, False)) + ch
        else:
            bm = 0
            hs = b''
            for k in range(16):
                c = n.children[k]
                if c is None:
                    continue
                h = c[1] if c[0] == 'o' else self._flatten(c[1])
                bm |= 1 << k
                hs += h
            if n.val is None:
                body = u8(1) + u16(bm) + hs
            else:
                body = u8(2) + vref(n.val) + u16(bm) + hs
        data = body + u64(mem)
        h = sha(data)
        self.store[h] = data
        self.cache.pop(h, None)
        return h
