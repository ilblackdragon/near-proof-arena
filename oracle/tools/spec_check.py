#!/usr/bin/env python3
"""Independent Python checker for near/pv86/receipt-transfer-batch/v0.

Written from spec/claim-v1.md and spec/near-transfer-receipt-v1.md only (no
nearcore code, no Lean code). Algorithmically independent of both:
  * the state root is rebuilt from the FULL key/value map (state.bin) with a
    from-scratch canonical Patricia-trie construction, before and after the
    batch (nearcore updates its trie in place; Lean updates a partial trie);
  * the witness is checked separately (every receiver path is resolvable from
    witness.bin nodes alone and hashes chain to pre_state_root).

Usage: spec_check.py <case-dir-or-parent>...   (prints one JSON line per case)
Exit 0 iff every case is consistent: claim file present <=> in domain, and the
derived claim bytes equal the claim file bytes.
"""
import hashlib, json, os, struct, sys

def sha(b): return hashlib.sha256(b).digest()
def u8(x): return bytes([x])
def u32(x): return struct.pack('<I', x)
def u64(x): return struct.pack('<Q', x)
def u128(x): return x.to_bytes(16, 'little')
def bstr(b): return u32(len(b)) + b

U128_MAX = (1 << 128) - 1
G = 108_059_500_000 + 115_123_062_500
STORAGE_PER_BYTE = 10 ** 19
ZBA_LIMIT = 770
MAX_BATCH = 256
MAX_WITNESS_BYTES = 3_000_000
STATEMENT = b"near/pv86/receipt-transfer-batch/v0"

class Out(Exception):
    """request is outside the slice domain"""

class R:
    def __init__(self, b): self.b, self.i = b, 0
    def take(self, n):
        if self.i + n > len(self.b): raise ValueError("truncated")
        r = self.b[self.i:self.i + n]; self.i += n; return r
    def u8(self): return self.take(1)[0]
    def u32(self): return struct.unpack('<I', self.take(4))[0]
    def u64(self): return struct.unpack('<Q', self.take(8))[0]
    def u128(self): return int.from_bytes(self.take(16), 'little')
    def bytes(self): return self.take(self.u32())
    def tag(self, want):
        if self.bytes() != want: raise ValueError(f"bad tag, want {want!r}")
    def end(self):
        if self.i != len(self.b): raise ValueError("trailing bytes")

def chain_ok(c): return 1 <= len(c) <= 64 and all(0x21 <= x <= 0x7e for x in c)

# ---------------- account ids (near-account-id 2.0.0) ----------------
def valid_id(s: bytes):
    if not (2 <= len(s) <= 64): return False
    last_sep = True
    for c in s:
        if 97 <= c <= 122 or 48 <= c <= 57: sep = False
        elif c in b'-_.': sep = True
        else: return False
        if sep and last_sep: return False
        last_sep = sep
    return not last_sep

HEX = set(b'0123456789abcdef')
def named(s: bytes):
    if len(s) == 64 and all(c in HEX for c in s): return False
    if len(s) == 42 and s[:2] in (b'0x', b'0s') and all(c in HEX for c in s[2:]): return False
    return True

# ---------------- receipts ----------------
def parse_receipt(r: R):
    pred = r.bytes(); recv = r.bytes(); rid = r.take(32)
    if r.u8() != 0: raise Out("ReceiptEnum not Action")
    signer = r.bytes()
    kt = r.u8()
    if kt == 0: pk = u8(0) + r.take(32)
    elif kt == 1: pk = u8(1) + r.take(64)
    else: raise Out("key type")
    gp = r.u128()
    if r.u32() != 0: raise Out("output_data_receivers")
    if r.u32() != 0: raise Out("input_data_ids")
    n = r.u32()
    if n != 1: raise Out(f"{n} actions")
    if r.u8() != 3: raise Out("not Transfer")
    dep = r.u128()
    return dict(pred=pred, recv=recv, rid=rid, signer=signer, pk=pk, gp=gp, dep=dep)

def enc_receipt(x):
    return (bstr(x['pred']) + bstr(x['recv']) + x['rid'] + u8(0) + bstr(x['signer']) + x['pk'] +
            u128(x['gp']) + u32(0) + u32(0) + u32(1) + u8(3) + u128(x['dep']))

def parse_request(b):
    r = R(b)
    r.tag(b"near-arena-request-v1"); r.tag(STATEMENT)
    req = dict(pv=r.u32(), chain=r.bytes())
    if not chain_ok(req['chain']): raise ValueError("chain id")
    req.update(shard=r.u64(), height=r.u64(), bgp=r.u128(), gas_limit=r.u64(), pre=r.take(32))
    req['receipts'] = [parse_receipt(r) for _ in range(r.u32())]
    r.end()
    return req

def parse_witness(b):
    r = R(b)
    r.tag(b"near-arena-witness-v1")
    root = r.take(32)
    if r.u8() != 0: raise ValueError("PartialState tag")
    vals = [r.bytes() for _ in range(r.u32())]
    r.end()
    if any(not (vals[i] < vals[i + 1]) for i in range(len(vals) - 1)): raise ValueError("unsorted witness")
    return root, vals

def parse_state(b):
    r = R(b); r.tag(b"near-arena-state-v1")
    kv = {}
    for _ in range(r.u32()):
        k = r.bytes(); kv[k] = r.bytes()
    r.end()
    return kv

# ---------------- full trie construction ----------------
def nibbles(key):
    out = []
    for b in key: out += [b >> 4, b & 15]
    return out

def hp(nibs, leaf):
    i = len(nibs) % 2
    out = bytes([(0x10 + nibs[0] if i else 0) + (0x20 if leaf else 0)])
    while i < len(nibs):
        out += bytes([nibs[i] * 16 + nibs[i + 1]]); i += 2
    return out

def vref(v): return u32(len(v)) + sha(v)

def build(items):
    """items: sorted list of (nibbles, value). Returns (hash, memory_usage)."""
    first = items[0][0]
    cp = len(first)
    for n, _ in items[1:]:
        j = 0
        while j < min(cp, len(n)) and n[j] == first[j]: j += 1
        cp = j
    if len(items) == 1:
        nibs, v = items[0]
        k = hp(nibs, True)
        mem = 50 + 2 * len(k) + len(v) + 50
        return sha(u8(0) + bstr(k) + vref(v) + u64(mem)), mem
    if cp > 0:
        k = hp(first[:cp], False)
        ch, cm = build([(n[cp:], v) for n, v in items])
        mem = 50 + 2 * len(k) + cm
        return sha(u8(3) + bstr(k) + ch + u64(mem)), mem
    val, groups = None, {}
    for n, v in items:
        if not n: val = v
        else: groups.setdefault(n[0], []).append((n[1:], v))
    mem, bitmap, hs = 50, 0, b''
    if val is not None: mem += len(val) + 50
    for i in range(16):
        if i in groups:
            h, m = build(groups[i]); bitmap |= 1 << i; hs += h; mem += m
    body = (u8(2) + vref(val) if val is not None else u8(1)) + struct.pack('<H', bitmap) + hs
    return sha(body + u64(mem)), mem

def state_root(kv):
    if not kv: return b'\0' * 32
    return build(sorted((nibbles(k), v) for k, v in kv.items()))[0]

# ---------------- witness walk ----------------
def witness_lookup(nodes, root, key):
    """Resolve key from witness nodes only; returns (value, bytes_of_nodes_on_path)."""
    nib, h, used = nibbles(key), root, 0
    while True:
        if h not in nodes: raise Out("witness missing node on path")
        n = nodes[h]; used += len(n); body, r = n[:-8], R(n[:-8])
        t = r.u8()
        def unhp(e):
            out = [e[0] & 15] if e[0] & 0x10 else []
            return out + nibbles(e[1:])
        if t == 0:
            k = unhp(r.bytes()); ln = r.u32(); vh = r.take(32)
            if k != nib: raise Out("receiver missing")
            break
        if t == 3:
            k = unhp(r.bytes()); ch = r.take(32)
            if nib[:len(k)] != k: raise Out("receiver missing")
            nib, h = nib[len(k):], ch; continue
        vh = None
        if t == 2: ln = r.u32(); vh = r.take(32)
        bm = struct.unpack('<H', r.take(2))[0]
        kids = {}
        for i in range(16):
            if bm >> i & 1: kids[i] = r.take(32)
        if not nib:
            if vh is None: raise Out("receiver missing")
            break
        if nib[0] not in kids: raise Out("receiver missing")
        h, nib = kids[nib[0]], nib[1:]
    if vh not in nodes or len(nodes[vh]) != ln: raise Out("witness missing value")
    return nodes[vh], used + ln

# ---------------- semantics ----------------
def merkle(leaves):
    if not leaves: return b'\0' * 32
    while len(leaves) > 1:
        leaves = [sha(leaves[i] + leaves[i + 1]) if i + 1 < len(leaves) else leaves[i]
                  for i in range(0, len(leaves), 2)]
    return leaves[0]

def derive(req, kv, wroot, wvals):
    if req['pv'] != 86: raise Out("protocol version")
    if req['chain'] != b'mainnet': raise Out("chain id")
    rs = req['receipts']; n = len(rs)
    if not (1 <= n <= MAX_BATCH): raise Out("batch size")
    if not ((n - 1) * G < req['gas_limit']): raise Out("gas limit")
    for x in rs:
        if not (valid_id(x['pred']) and valid_id(x['recv']) and valid_id(x['signer'])): raise Out("invalid account id")
        if x['pred'] == b'system': raise Out("system predecessor")
        if not named(x['recv']): raise Out("receiver not NamedAccount")
    if len({x['rid'] for x in rs}) != n: raise Out("duplicate receipt id")
    pre = state_root(kv)
    if pre != req['pre']: raise ValueError("state.bin root != request pre_state_root")
    if wroot != pre: raise ValueError("witness root mismatch")
    nodes = {sha(v): v for v in wvals}
    # witness: every receiver resolvable from witness alone; size bound over distinct path nodes
    for x in rs:
        val, _ = witness_lookup(nodes, pre, b'\0' + x['recv'])
        if val != kv.get(b'\0' + x['recv']): raise ValueError("witness value != state value")
    if sum(len(v) for v in wvals) > MAX_WITNESS_BYTES: raise Out("witness too large")
    kv = dict(kv); leaves = []; refunds = []; tokens = 0
    for x in rs:
        k = b'\0' + x['recv']
        if k not in kv: raise Out("receiver missing")
        v = kv[k]
        if len(v) != 72: raise Out("not AccountV1")
        amount = int.from_bytes(v[:16], 'little'); locked = int.from_bytes(v[16:32], 'little')
        su = struct.unpack('<Q', v[64:72])[0]
        if amount == U128_MAX: raise Out("V2 sentinel")
        na = amount + x['dep']
        if na >= U128_MAX: raise Out("balance overflow / sentinel")
        if na + locked > U128_MAX: raise Out("amount+locked overflow")
        if not (na + locked >= STORAGE_PER_BYTE * su or su <= ZBA_LIMIT): raise Out("storage stake")
        p = min(x['gp'], req['bgp'])
        burnt, surplus = G * p, G * (x['gp'] - p)
        if burnt > U128_MAX or surplus > U128_MAX: raise Out("burn/refund overflow")
        tokens += burnt
        if tokens > U128_MAX: raise Out("tokens total overflow")
        kv[k] = u128(na) + v[16:]
        rids = []
        if surplus > 0:
            rf = dict(pred=b'system', recv=x['signer'], rid=sha(x['rid'] + u64(req['height']) + u64(0)),
                      signer=x['signer'], pk=x['pk'], gp=0, dep=surplus)
            refunds.append(rf); rids.append(rf['rid'])
        partial = (u32(len(rids)) + b''.join(rids) + u64(G) + u128(burnt) + bstr(x['recv']) + u8(2) + u32(0))
        leaves.append(sha(u32(2) + x['rid'] + sha(partial)))
    post = state_root(kv)
    enc_list = lambda l: u32(len(l)) + b''.join(enc_receipt(y) for y in l)
    return (bstr(b"near-arena-claim-v1") + bstr(STATEMENT) + u32(req['pv']) + bstr(req['chain']) +
            u64(req['shard']) + u64(req['height']) + u128(req['bgp']) + u64(req['gas_limit']) + pre +
            u32(n) + sha(u64(req['shard']) + enc_list(rs)) + post + merkle(leaves) +
            u32(len(refunds)) + sha(enc_list(refunds)) + u64(G * n) + u128(tokens))

def check_case(d):
    claim_file = next((os.path.join(d, f) for f in ("claim.bin", "expected_claim.bin")
                       if os.path.exists(os.path.join(d, f))), None)
    try:
        req = parse_request(open(os.path.join(d, "request.bin"), "rb").read())
        kv = parse_state(open(os.path.join(d, "state.bin"), "rb").read())
        wroot, wvals = parse_witness(open(os.path.join(d, "witness.bin"), "rb").read())
        mine = derive(req, kv, wroot, wvals)
    except Out as e:
        return dict(status="out_of_domain", reason=str(e)), claim_file is None
    except Exception as e:
        return dict(status="error", reason=f"{type(e).__name__}: {e}"), False
    if claim_file is None:
        return dict(status="mismatch", reason="in domain but no claim file", claim=mine.hex()), False
    want = open(claim_file, "rb").read()
    if mine != want:
        return dict(status="mismatch", reason="claim bytes differ", claim=mine.hex()), False
    return dict(status="ok", claim=mine.hex()), True

def collect(p):
    if os.path.exists(os.path.join(p, "request.bin")): return [p]
    if not os.path.isdir(p): return []
    out = []
    for e in sorted(os.listdir(p)): out += collect(os.path.join(p, e))
    return out

def main():
    dirs = [d for a in sys.argv[1:] for d in collect(a)]
    bad = ok = ood = 0
    for d in dirs:
        res, good = check_case(d)
        bad += not good; ok += res['status'] == 'ok'; ood += res['status'] == 'out_of_domain'
        print(json.dumps(dict(case=d, consistent=good, **res)))
    print(f"spec_check.py: {len(dirs)} cases, {ok} ok, {ood} out_of_domain, {bad} inconsistent", file=sys.stderr)
    sys.exit(0 if bad == 0 and dirs else 1)

if __name__ == "__main__":
    main()
