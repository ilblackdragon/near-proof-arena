#!/usr/bin/env python3
"""Independent Python checker for near/pv86/receipt-transfer-batch/v1 (scope v2).

Written from spec/claim-v2.md and spec/near-transfer-receipt-v2.md only (no
nearcore code, no Lean code). It reuses the v1 checker's parsers, receipt
encoders and from-scratch canonical trie builder (spec_check.py, itself written
only from the v1 spec), and adds:

  * the v2 request/witness/claim formats;
  * the bandwidth-scheduler step for a one-shard layout, implemented as the
    scheduler ALGORITHM (fair-share increase capped at max_allowance, base-grant
    attempt gated by the link status, decrease, rebuild of the link list,
    sanity-hash chaining), not as the closed form the Lean spec states;
  * the post-state root rebuilt from the FULL key/value map (state.bin) after
    writing the receivers' accounts AND key 0x0f (an insert when absent);
  * a witness walk that resolves every receiver AND the path to 0x0f (proving
    presence or absence) from witness.bin nodes alone.

Usage: spec_check_v2.py <case-dir-or-parent>...   (one JSON line per case)
Exit 0 iff every case is consistent: claim file present <=> in domain, and the
derived claim bytes equal the claim file bytes.
"""
import json, os, struct, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import spec_check as sc
from spec_check import Out, R, sha, u8, u32, u64, u128, bstr, G, U128_MAX

STATEMENT = b"near/pv86/receipt-transfer-batch/v1"
BW_KEY = b"\x0f"

# PV86 mainnet RuntimeConfig.bandwidth_scheduler_config (74.yaml) and limits
MAX_SHARD_BANDWIDTH = 4_500_000
MAX_SINGLE_GRANT = 4_194_304
MAX_ALLOWANCE = 4_500_000
MAX_BASE_BANDWIDTH = 100_000
U64_MAX = (1 << 64) - 1

def parse_request(b):
    r = R(b)
    r.tag(b"near-arena-request-v2"); r.tag(STATEMENT)
    req = dict(pv=r.u32(), chain=r.bytes())
    if not sc.chain_ok(req['chain']): raise ValueError("chain id")
    req.update(shard=r.u64(), height=r.u64(), bgp=r.u128(), gas_limit=r.u64())
    req['cong'] = dict(delayed=r.u128(), buffered=r.u128(), rbytes=r.u64(),
                       allowed=struct.unpack('<H', r.take(2))[0], missed=r.u64())
    req['pre'] = r.take(32)
    req['receipts'] = [sc.parse_receipt(r) for _ in range(r.u32())]
    r.end()
    return req

def parse_witness(b):
    r = R(b)
    r.tag(b"near-arena-witness-v2")
    root = r.take(32)
    if r.u8() != 0: raise ValueError("PartialState tag")
    vals = [r.bytes() for _ in range(r.u32())]
    r.end()
    if any(not (vals[i] < vals[i + 1]) for i in range(len(vals) - 1)): raise ValueError("unsorted witness")
    return root, vals

# ---------------- bandwidth scheduler (one shard) ----------------
def bw_decode(v):
    """strict borsh BandwidthSchedulerState::V1; None if it does not decode"""
    try:
        r = R(v)
        if r.u8() != 0: return None
        links = [(r.u64(), r.u64(), r.u64()) for _ in range(r.u32())]
        h = r.take(32)
        r.end()
        return links, h
    except ValueError:
        return None

def bw_encode(links, h):
    return u8(0) + u32(len(links)) + b''.join(u64(s) + u64(t) + u64(a) for s, t, a in links) + h

def bw_step(prev, shard, missed):
    """BandwidthScheduler::run + sanity hash for layout [shard] with empty requests."""
    links, h = prev if prev is not None else ([], b'\0' * 32)
    num_shards = 1
    base = min((MAX_SHARD_BANDWIDTH - MAX_SINGLE_GRANT) // max(1, num_shards - 1), MAX_BASE_BANDWIDTH)
    # link allowances of the current layout (last entry for a link wins); default 0
    allowance = {}
    for s, t, a in links:
        if s == shard and t == shard: allowance[(s, t)] = a
    # link status: receiver status known (congestion info present), last chunk
    # missing <=> missed_chunks_count > 0; zero congestion => not fully congested
    allowed = missed == 0
    budget_send = budget_recv = MAX_SHARD_BANDWIDTH
    link = (shard, shard)
    # increase_allowances: fair share, saturating u64 add, cap at max_allowance
    a = allowance.get(link, 0)
    a = min(min(a + MAX_SHARD_BANDWIDTH // num_shards, U64_MAX), MAX_ALLOWANCE)
    # grant_base_bandwidth
    if allowed and budget_send >= base and budget_recv >= base:
        a = max(a - base, 0)
    # (no requests; distribute_remaining only grants, never touches allowances)
    new_links = [(shard, shard, a)]
    new_h = sha(h + sha(u32(1) + u64(shard)))
    return bw_encode(new_links, new_h)

# ---------------- witness walk with absence ----------------
def unhp(e):
    return ([e[0] & 15] if e[0] & 0x10 else []) + sc.nibbles(e[1:])

def witness_find(nodes, root, key):
    """('present', value) | ('absent', None) from witness nodes only, else raise."""
    nib, h = sc.nibbles(key), root
    while True:
        if h not in nodes: raise ValueError("witness missing node on path")
        r = R(nodes[h][:-8]); t = r.u8()
        if t == 0:
            k = unhp(r.bytes()); ln = r.u32(); vh = r.take(32)
            if k != nib: return ('absent', None)
            break
        if t == 3:
            k = unhp(r.bytes()); ch = r.take(32)
            if nib[:len(k)] != k: return ('absent', None)
            nib, h = nib[len(k):], ch; continue
        vh = None
        if t == 2: ln = r.u32(); vh = r.take(32)
        bm = struct.unpack('<H', r.take(2))[0]
        kids = {i: r.take(32) for i in range(16) if bm >> i & 1}
        if not nib:
            if vh is None: return ('absent', None)
            break
        if nib[0] not in kids: return ('absent', None)
        h, nib = kids[nib[0]], nib[1:]
    if vh not in nodes or len(nodes[vh]) != ln: raise ValueError("witness missing value")
    return ('present', nodes[vh])

# ---------------- semantics ----------------
def derive(req, kv, wroot, wvals):
    if req['pv'] != 86: raise Out("protocol version")
    if req['chain'] != b'mainnet': raise Out("chain id")
    rs = req['receipts']; n = len(rs)
    if not (1 <= n <= sc.MAX_BATCH): raise Out("batch size")
    if not ((n - 1) * G < req['gas_limit']): raise Out("gas limit")
    for x in rs:
        if not (sc.valid_id(x['pred']) and sc.valid_id(x['recv']) and sc.valid_id(x['signer'])): raise Out("invalid account id")
        if x['pred'] == b'system': raise Out("system predecessor")
        if not sc.named(x['recv']): raise Out("receiver not NamedAccount")
    if len({x['rid'] for x in rs}) != n: raise Out("duplicate receipt id")
    if req['shard'] >= 1 << 32: raise Out("shard id >= 2^32")
    cg = req['cong']
    if cg['delayed'] or cg['buffered'] or cg['rbytes']: raise Out("congestion not zero")
    pre = sc.state_root(kv)
    if pre != req['pre']: raise ValueError("state.bin root != request pre_state_root")
    if wroot != pre: raise ValueError("witness root mismatch")
    nodes = {sha(v): v for v in wvals}
    for x in rs:
        val, _ = sc.witness_lookup(nodes, pre, b'\0' + x['recv'])
        if val != kv.get(b'\0' + x['recv']): raise ValueError("witness value != state value")
    st, bwv = witness_find(nodes, pre, BW_KEY)
    if (st == 'present') != (BW_KEY in kv) or (st == 'present' and bwv != kv[BW_KEY]):
        raise ValueError("witness 0x0f lookup != state")
    if sum(len(v) for v in wvals) > sc.MAX_WITNESS_BYTES: raise Out("witness too large")
    kv = dict(kv)
    # 1) bandwidth scheduler (runs before receipts in Runtime::apply)
    prev = None
    if BW_KEY in kv:
        prev = bw_decode(kv[BW_KEY])
        if prev is None: raise Out("bandwidth scheduler state does not decode")
    kv[BW_KEY] = bw_step(prev, req['shard'], cg['missed'])
    # 2) receipts (v1 semantics)
    leaves = []; refunds = []; tokens = 0
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
        if not (na + locked >= sc.STORAGE_PER_BYTE * su or su <= sc.ZBA_LIMIT): raise Out("storage stake")
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
    # 3) refunds need granted bandwidth on the (S,S) link
    if refunds and cg['missed'] > 0: raise Out("refund with missed chunks (no grant)")
    post = sc.state_root(kv)
    enc_list = lambda l: u32(len(l)) + b''.join(sc.enc_receipt(y) for y in l)
    return (bstr(b"near-arena-claim-v2") + bstr(STATEMENT) + u32(req['pv']) + bstr(req['chain']) +
            u64(req['shard']) + u64(req['height']) + u128(req['bgp']) + u64(req['gas_limit']) +
            u128(cg['delayed']) + u128(cg['buffered']) + u64(cg['rbytes']) + struct.pack('<H', cg['allowed']) +
            u64(cg['missed']) + pre +
            u32(n) + sha(u64(req['shard']) + enc_list(rs)) + post + sc.merkle(leaves) +
            u32(len(refunds)) + sha(enc_list(refunds)) + u64(G * n) + u128(tokens))

def check_case(d):
    claim_file = next((os.path.join(d, f) for f in ("claim.bin", "expected_claim.bin")
                       if os.path.exists(os.path.join(d, f))), None)
    try:
        req = parse_request(open(os.path.join(d, "request.bin"), "rb").read())
        kv = sc.parse_state(open(os.path.join(d, "state.bin"), "rb").read())
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

def main():
    dirs = [d for a in sys.argv[1:] for d in sc.collect(a)]
    bad = ok = ood = 0
    for d in dirs:
        res, good = check_case(d)
        bad += not good; ok += res['status'] == 'ok'; ood += res['status'] == 'out_of_domain'
        print(json.dumps(dict(case=d, consistent=good, **res)))
    print(f"spec_check_v2.py: {len(dirs)} cases, {ok} ok, {ood} out_of_domain, {bad} inconsistent", file=sys.stderr)
    sys.exit(0 if bad == 0 and dirs else 1)

if __name__ == "__main__":
    main()
