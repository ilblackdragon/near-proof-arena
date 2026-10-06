#!/usr/bin/env python3
"""Independent Python reference checker for near/pv86/chunk-validation/v0, domain D1
(D0 + Transfer transactions; spec/near-chunk-validation-d1.md).

Written from the spec, docs/research/chunk-validation-boundary.md §12 and the nearcore
2.13.4 Rust sources. It does NOT use the Lean formalization. The D0 machinery (claim and
chain-context decoding, receipt proofs, shuffle, scheduler, congestion, trie, Reed-Solomon)
is imported from spec_check_v3.py; the transaction semantics, the signature check
(v3lib/ed25519.py, its own pure-Python Ed25519 with ed25519-dalek 2.2.0 `verify` semantics,
SHA-512 from hashlib) and the D1 main transition are implemented here.

Usage:
  spec_check_v3_d1.py CASE_DIR...      one JSON line per case:
                                       {"case", "verdict": accept|reject|out_of_domain, "reason"}
"""
import hashlib
import json
import os
import struct
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import spec_check_v3 as s3  # noqa: E402
from spec_check_v3 import (  # noqa: E402
    FORMAT_WITNESS, MAX_WITNESS, D0_MAX_WITNESS, D0_MAX_BASE_STATE, NEW_ACTION_RECEIPT_EXEC,
    TRANSFER_EXEC, CREATE_ACCOUNT_EXEC, ADD_FULL_ACCESS_KEY_EXEC, G, STORAGE_AMOUNT_PER_BYTE,
    ZERO_BALANCE_ACCOUNT_STORAGE_LIMIT, MAX_RECEIPT_SIZE, COL_ACCOUNT, COL_ACCESS_KEY, COL_DELAYED,
    COL_PROMISE_YIELD_INDICES, COL_BUFFERED_INDICES, COL_GROUPS_QUEUE_DATA)
from v3lib.prim import (  # noqa: E402
    R, Reject, OOD, DecodeError, sha, u8, u32, u64, u128, bstr, U64_MAX, U128_MAX, ZERO32,
    account_type, merklize, merkle_root_of_hashes, compute_root_from_path, ChaCha20Rng,
    encoded_merkle_root, outgoing_gas_limit, PartialTrie)
from v3lib import ed25519  # noqa: E402

# ---- PV 86 transaction parameters (near-arena-oracle-v3 params: d1_transaction_fees) ----
NAR_SEND = 108_059_500_000          # new_action_receipt send (sir = not sir)
TRANSFER_SEND = 115_123_062_500
CREATE_ACCOUNT_SEND = 500_000_000_000
ADD_FULL_ACCESS_KEY_SEND = 101_765_125_000
SIG_VERIFICATION_ED25519 = 0
MIN_GAS_PURCHASE_PRICE = 1_000_000_000
MAX_TRANSACTION_SIZE = 1_572_864
NONCE_RANGE_MULTIPLIER = 1_000_000
ALLOWED_SHARD_OUTGOING_GAS = 1_000_000_000_000_000


# ======================================================================
# SignedTransaction (core/primitives/src/transaction.rs)
# ======================================================================
class Tx:
    pass


def read_tx(r):
    start = r.i
    if r.i + 2 > len(r.b):
        raise DecodeError("transaction version bytes")
    u1, u2 = r.b[r.i], r.b[r.i + 1]
    if u2 == 0:
        v1 = False
    elif u1 == 1:
        v1 = True
        r.i += 1
    else:
        raise DecodeError("invalid transaction version tag %d" % u1)
    t = Tx()
    t.signer = r.account()
    kt = r.u8()
    if kt not in (0, 1, 2):
        raise DecodeError("PublicKey tag")
    t.pk = r.take({0: 32, 1: 64, 2: 1952}[kt])
    if kt != 0:
        raise OOD("w.tx_shape: transaction key is not ED25519")
    if v1:
        nt = r.u8()
        if nt == 0:
            t.nonce = r.u64()
        elif nt == 1:
            raise OOD("w.tx_shape: TransactionNonce::GasKeyNonce")
        else:
            raise DecodeError("TransactionNonce tag")
    else:
        t.nonce = r.u64()
    t.recv = r.account()
    t.block_hash = r.hash()
    na = r.u32()
    if na != 1:
        raise OOD("w.tx_shape: %d actions" % na)
    at = r.u8()
    if at != 3:
        raise OOD("w.tx_shape: action tag %d (not Transfer)" % at)
    t.deposit = r.u128()
    t.strict = False
    if v1:
        m = r.u8()
        if m not in (0, 1):
            raise DecodeError("NonceMode tag")
        t.strict = m == 1
    t.body = r.b[start:r.i]
    st = r.u8()
    if st in (1, 2):
        raise OOD("w.tx_shape: signature is not ED25519")
    if st != 0:
        raise DecodeError("Signature tag")
    t.sig = r.take(64)
    if t.sig[63] & 0xE0:
        raise DecodeError("ed25519 signature high bits")
    t.raw = r.b[start:r.i]
    t.hash = hashlib.sha256(t.body).digest()
    return t


def decode_state_witness_d1(b):
    r = R(b)
    if r.u8() != 1:
        raise DecodeError("ChunkStateWitness tag")
    w = dict(epoch_id=r.hash())
    if r.u8() != 2:
        raise Reject("ShardChunkHeader version is not V3")
    try:
        w['inner'] = s3.read_inner(r)
    except s3.UnsupportedInner as e:
        raise Reject("witness chunk header inner version tag %d" % e.args[0])
    w['height_included'] = r.u64()
    s3.read_signature(r)
    w['main'] = s3.read_transition(r)
    proofs = {}
    for _ in range(r.u32()):
        key = r.hash()
        receipts = r.vec(lambda: s3.read_receipt(r))
        from_shard, to_shard = r.u64(), r.u64()

        def item():
            h = r.hash()
            d = r.u8()
            if d > 1:
                raise DecodeError("Direction")
            return (h, d)
        path = r.vec(item)
        proofs[key] = (receipts, from_shard, to_shard, path)  # duplicate key: last wins
    w['proofs'] = proofs
    w['applied_receipts_hash'] = r.hash()
    w['txs'] = r.vec(lambda: read_tx(r))
    w['implicit'] = r.vec(lambda: s3.read_transition(r))
    w['new_txs'] = r.vec(lambda: read_tx(r))
    r.end()
    return w


# ======================================================================
# transaction semantics
# ======================================================================
def send_fee(recv):
    at = account_type(recv)
    if at == 'near':
        return TRANSFER_SEND + CREATE_ACCOUNT_SEND + ADD_FULL_ACCESS_KEY_SEND
    if at in ('eth', 'det'):
        return TRANSFER_SEND + CREATE_ACCOUNT_SEND
    return TRANSFER_SEND


def exec_fee(recv):
    at = account_type(recv)
    if at == 'near':
        return TRANSFER_EXEC + CREATE_ACCOUNT_EXEC + ADD_FULL_ACCESS_KEY_EXEC
    if at in ('eth', 'det'):
        return TRANSFER_EXEC + CREATE_ACCOUNT_EXEC
    return TRANSFER_EXEC


def tx_cost(t, gas_price):
    """config.rs tx_cost; None = IntegerOverflowError (CostOverflow)."""
    burnt = NAR_SEND + send_fee(t.recv) + SIG_VERIFICATION_ED25519
    remaining = NEW_ACTION_RECEIPT_EXEC + exec_fee(t.recv)
    if burnt > U64_MAX or remaining > U64_MAX:
        return None
    burnt_amount = gas_price * burnt
    rgp = max(gas_price, MIN_GAS_PURCHASE_PRICE)
    rem_amount = rgp * remaining
    if burnt_amount > U128_MAX or rem_amount > U128_MAX:
        return None
    gas_cost = burnt_amount + rem_amount
    if gas_cost > U128_MAX:
        return None
    total = gas_cost + t.deposit
    if total > U128_MAX:
        return None
    return dict(burnt=burnt, rgp=rgp, burnt_amount=burnt_amount, total=total)


def read_string(r):
    s = r.bytes()
    try:
        s.decode('utf-8', 'strict')
    except UnicodeDecodeError:
        raise DecodeError("invalid UTF-8")
    return s


def decode_access_key(v):
    """AccessKey borsh (try_from_slice): returns (nonce, kind, allowance); kind in
    full|fc|gas. Raises Reject (StorageInconsistentState) if it does not decode."""
    try:
        r = R(v)
        nonce = r.u64()
        tag = r.u8()
        allowance = None

        def fcp():
            al = r.u128() if r.u8() else None
            read_string(r)
            r.vec(lambda: read_string(r))
            return al
        if tag == 0:
            kind, allowance = 'fc', fcp()
        elif tag == 1:
            kind = 'full'
        elif tag == 2:
            r.u128(); r.u16()
            fcp()
            kind = 'gas'
        elif tag == 3:
            r.u128(); r.u16()
            kind = 'gas'
        else:
            raise DecodeError("AccessKeyPermission tag")
        r.end()
        return nonce, kind, allowance
    except DecodeError:
        raise Reject("StorageInconsistentState: access key does not decode")


def verify_and_charge(acct, ak, t, cost, height):
    """verify_and_charge_tx_ephemeral for a Transfer; returns the new amount or None."""
    amount, locked, su = acct
    ak_nonce, kind, allowance = ak
    if kind == 'gas':
        return None
    if t.strict:
        if ak_nonce + 1 > U64_MAX or t.nonce != ak_nonce + 1:
            return None
    elif t.nonce <= ak_nonce:
        return None
    if t.nonce >= min(height * NONCE_RANGE_MULTIPLIER, U64_MAX):
        return None
    if amount < cost['total']:
        return None
    new_amount = amount - cost['total']
    if kind == 'fc' and allowance is not None and allowance < cost['total']:
        return None
    required = STORAGE_AMOUNT_PER_BYTE * su
    if required > U128_MAX or new_amount + locked > U128_MAX:
        return None
    if new_amount + locked < required and su > ZERO_BALANCE_ACCOUNT_STORAGE_LIMIT:
        return None
    if kind == 'fc':
        return None  # RequiresFullAccess: a Transfer is never a FunctionCall
    return new_amount


# ======================================================================
# the D1 relation
# ======================================================================
def check_case_inner(claim_b, witness_b):
    c = s3.decode_claim(claim_b)
    wr = R(witness_b)
    if wr.bytes() != FORMAT_WITNESS:
        raise DecodeError("witness format id")
    sw = wr.bytes()
    codes = wr.vec(wr.bytes)
    wr.end()
    if len(sw) > MAX_WITNESS:
        raise Reject("state witness larger than 64 MiB")
    if codes:
        raise OOD("w.no_code: contract code present")
    if len(sw) > D0_MAX_WITNESS:
        raise OOD("w.size: state witness larger than 8 MiB")
    W = decode_state_witness_d1(sw)

    if not s3.chain_id_ok(c['chain_id']):
        raise Reject("claim: chain_id")
    tot, dat = c['rs_total'], c['rs_data']
    if not (2 <= tot <= 256) or dat != (1 if tot <= 3 else (tot - 1) // 3):
        raise Reject("claim: Reed-Solomon parameters inconsistent")
    blocks = c['blocks']
    n = len(blocks)
    if n < 1:
        raise Reject("claim: no blocks")
    for b in blocks:
        if b.header_version != 5:
            raise OOD("c.headers: block header version tag %d" % b.header_version)
        b.lite = s3.decode_inner_lite(b.lite_raw)
        b.rest = s3.decode_inner_rest_v6(b.rest_raw)
        b.height = b.lite['height']
        b.hash = s3.block_hash(b)
        b.slots = []
        for raw, hi in b.slots_raw:
            s = s3.Slot()
            try:
                s.inner = s3.decode_inner_bytes(raw)
            except s3.UnsupportedInner as e:
                raise OOD("c.headers: chunk inner version tag %d" % e.args[0])
            s.height_included = hi
            b.slots.append(s)
    try:
        H = s3.decode_inner_bytes(c['chunk_inner'])
    except s3.UnsupportedInner as e:
        raise OOD("c.headers: endorsed chunk inner version tag %d" % e.args[0])
    if blocks[0].hash != H.prev_block_hash:
        raise Reject("claim: blocks[0] hash != chunk prev_block_hash")
    for i in range(n - 1):
        if blocks[i].prev_hash != blocks[i + 1].hash:
            raise Reject("claim: block hash chain broken at %d" % i)
    for b in blocks:
        leaves = [s.inner.chunk_hash + u64(s.height_included) for s in b.slots]
        if merklize(leaves) != b.rest['chunk_headers_root']:
            raise Reject("claim: chunk_headers_root mismatch")
    eps = c['epochs']
    for i in range(1, len(eps)):
        if not (eps[i - 1]['epoch_id'] < eps[i]['epoch_id']):
            raise Reject("claim: epochs not strictly ascending")
    epmap = {e['epoch_id']: e for e in eps}
    referenced = {c['epoch_id']} | {b.lite['epoch_id'] for b in blocks}
    if set(epmap) != referenced:
        raise Reject("claim: epoch table does not hold exactly the referenced epochs")
    for e in eps:
        s3.check_sorted_accounts(e['validators'])
    if epmap[c['epoch_id']]['pv'] != c['pv']:
        raise Reject("claim: protocol_version != epochs[epoch_id].protocol_version")
    esa = c['epoch_start_after']
    if len(esa) != n:
        raise Reject("claim: epoch_start_after length")
    for i, b in enumerate(blocks):
        nxt = c['epoch_id'] if i == 0 else blocks[i - 1].lite['epoch_id']
        want = b.lite['next_epoch_id'] if esa[i] else b.lite['epoch_id']
        if nxt != want:
            raise Reject("claim: epoch_start_after[%d] inconsistent with header epoch ids" % i)
        if b.prev_hash == ZERO32 and not esa[i]:
            raise Reject("claim: genesis block must start an epoch")
    for af in c['apply_facts']:
        if af['validator_update'] is not None:
            st, rw, _tr = af['validator_update']
            s3.check_sorted_accounts(st)
            s3.check_sorted_accounts(rw)
    if W['epoch_id'] != c['epoch_id']:
        raise Reject("witness epoch_id != claim epoch_id")
    if W['inner'].raw != c['chunk_inner']:
        raise Reject("witness chunk header inner != claim chunk_inner")

    # ---- claim-level D1 conditions (D0's, minus c.no_tx_flags) ----
    if c['pv'] != 86:
        raise OOD("c.pv86")
    if len(eps) != 1 or any(b.lite['epoch_id'] != c['epoch_id'] for b in blocks) or any(esa):
        raise OOD("c.single_epoch")
    L = s3.decode_layout(epmap[c['epoch_id']]['layout_raw'])
    ns = len(L.shard_ids)
    if not (1 <= ns <= 64):
        raise OOD("c.layout: %d shards" % ns)
    for b in blocks:
        if len(b.slots) != ns:
            raise Reject("claim: slot count != number of shards")
    if any(af['split_gate'] is not None for af in c['apply_facts']):
        raise OOD("c.no_split_gate")
    if n > 32:
        raise OOD("c.segment: n_blocks > 32")
    # pre-validation P2: check_valid_for_config on new_transactions (size only at PV 86)
    for t in W['new_txs']:
        if len(t.body) + 65 > MAX_TRANSACTION_SIZE:
            raise Reject("new transaction exceeds max_transaction_size")

    # ---- backward walk ----
    s0 = H.shard_id
    if s0 not in L.index:
        raise Reject("chunk shard_id not in the epoch's layout")
    idx = L.index[s0]
    seen = 0
    implicit_idx, source_idx = [], []
    stop = None
    i = 0
    while True:
        if i >= n:
            raise Reject("claim: segment shorter than the backward walk")
        X = blocks[i]
        new = X.slots[idx].height_included == X.height
        cnt = seen + (1 if new else 0)
        if cnt == 0:
            implicit_idx.append(i)
        elif cnt == 1:
            source_idx.append(i)
        else:
            stop = i
            break
        if X.prev_hash == ZERO32:
            stop = i
            break
        seen = cnt
        i += 1
    if n != stop + 1:
        raise Reject("claim: segment longer than the backward walk")
    if not source_idx:
        raise Reject("no last new chunk found")
    b2i = source_idx[0]
    B2 = blocks[b2i]
    if len(c['apply_facts']) != 1 + len(implicit_idx):
        raise Reject("claim: apply_facts count")
    applied = [b2i] + list(reversed(implicit_idx))
    for af, bi in zip(c['apply_facts'], applied):
        starts = esa[bi + 1] if bi + 1 < n else 1
        if (af['validator_update'] is not None) != bool(starts):
            raise Reject("claim: validator_update presence inconsistent")
    if B2.prev_hash == ZERO32:
        if c['genesis_chunk_extra'] is None:
            raise Reject("claim: genesis_chunk_extra missing")
        raise OOD("c.not_genesis")
    if c['genesis_chunk_extra'] is not None:
        raise Reject("claim: genesis_chunk_extra present for a non-genesis B2")
    txs = W['txs']
    if len(c['tx_valid']) != len(txs):
        raise Reject("claim: tx_valid length != number of witness transactions")
    own_slot = B2.slots[idx]
    cong_b2 = s3.ctx_congestion(B2)
    if s0 not in cong_b2:
        raise OOD("c.own_congestion_zero: no congestion info for own shard")
    own_info = cong_b2[s0][0]
    if own_info[0] or own_info[1] or own_info[2]:
        raise OOD("c.own_congestion_zero")
    if sum(len(v) for v in W['main']['base_state']) > D0_MAX_BASE_STATE:
        raise OOD("w.size: main base_state > 3 000 000 bytes")

    # ---- source receipt proofs ----
    proofs = W['proofs']
    srcs = [blocks[j] for j in source_idx]
    R_list = []
    if any(S.prev_hash == ZERO32 for S in srcs):
        if len(srcs) != 1:
            raise Reject("genesis among several receipt source blocks")
        if proofs:
            raise Reject("genesis source_receipt_proofs not empty")
    else:
        expected = 0
        for S in srcs:
            block_proofs = []
            for s in S.slots:
                if s.height_included != S.height:
                    continue
                p = proofs.get(s.inner.chunk_hash)
                if p is None:
                    raise Reject("missing source receipt proof")
                receipts, from_shard, to_shard, path = p
                if from_shard != s.inner.shard_id:
                    raise Reject("receipt proof from_shard_id")
                if to_shard != s0:
                    raise Reject("receipt proof to_shard_id")
                leaf = sha(sha(u64(to_shard) + u32(len(receipts)) + b''.join(x.raw for x in receipts)))
                if compute_root_from_path(path, leaf) != s.inner.prev_outgoing_receipts_root:
                    raise Reject("receipt proof merkle path")
                expected += 1
                block_proofs.append(receipts)
            block_proofs = [[x for x in rs if s3.account_to_shard(L, x.recv) == s0] for rs in block_proofs]
            ChaCha20Rng(S.prev_hash).shuffle(block_proofs)
            for receipts in block_proofs:
                R_list.extend(receipts)
        if len(proofs) != expected:
            raise Reject("source_receipt_proofs contains too many proofs")
    if sha(u32(len(R_list)) + b''.join(x.raw for x in R_list)) != W['applied_receipts_hash']:
        raise Reject("applied_receipts_hash mismatch")
    if own_slot.inner.tx_root != merklize([t.raw for t in txs]):
        raise Reject("tx_root of last new chunk != merklize(witness transactions)")

    # ---- main transition ----
    gas_limit = own_slot.inner.gas_limit
    gas_price = blocks[b2i + 1].rest['next_gas_price']
    height = B2.height
    trie = PartialTrie(W['main']['base_state'], own_slot.inner.prev_state_root)
    overlay = {}

    def get(k):
        v = overlay.get(k)
        return v if v is not None else trie.get(k)

    d = s3.get_indices(trie, bytes([COL_DELAYED]), "DelayedReceiptIndices")
    if d is not None and d[0] != d[1]:
        raise OOD("e.queues_empty: delayed receipt queue not empty")
    grants = s3.run_scheduler_step(trie, overlay, L, B2)
    bi = trie.get(bytes([COL_BUFFERED_INDICES]))
    if bi is not None:
        try:
            r = R(bi)
            bufs = {}
            for _ in range(r.u32()):
                k = r.u64()
                bufs[k] = (r.u64(), r.u64())
            r.end()
        except DecodeError:
            raise OOD("e.queues_empty: BufferedReceiptIndices does not decode")
        for k, (f, nx) in bufs.items():
            if f != nx:
                raise OOD("e.queues_empty: outgoing buffer to shard %d not empty" % k)
        for k in sorted(bufs):
            trie.get(bytes([COL_GROUPS_QUEUE_DATA]) + u64(k))
    limits = {}
    for sid, (info, missed) in cong_b2.items():
        g = U64_MAX if sid == s0 else outgoing_gas_limit(info, missed, s0)
        limits[sid] = [g, grants.get((s0, sid), 0)]

    def forward(recv, rc, what):
        """ReceiptSink::forward_or_buffer_receipt for a Transfer receipt."""
        shard = s3.account_to_shard(L, recv)
        size = min(len(rc), MAX_RECEIPT_SIZE)
        cg = NEW_ACTION_RECEIPT_EXEC + exec_fee(recv)
        lim = limits.setdefault(shard, [U64_MAX, 0])
        if lim[0] >= min(cg, ALLOWED_SHARD_OUTGOING_GAS) and lim[1] >= size:
            lim[0] = max(lim[0] - cg, 0)
            lim[1] -= size
            outgoing.append((shard, recv, rc))
        else:
            raise OOD("e.forwarded: %s would be buffered" % what)

    leaves = []
    outgoing = []
    balance_burnt = 0
    gas_used = 0
    local = []        # (rid, signer, pk, gas_price, deposit, raw)

    # -- process_transactions (lib.rs:1882-2278)
    seen_hashes = set()
    for t, flag in zip(txs, c['tx_valid']):
        if t.hash in seen_hashes:
            continue
        seen_hashes.add(t.hash)
        failed = sha(u32(2) + t.hash + sha(u32(0) + u64(0) + u128(0) + bstr(t.signer) + u8(1)))
        if not flag:
            leaves.append(failed)
            continue
        if not (len(t.body) + 65 <= MAX_TRANSACTION_SIZE and ed25519.verify(t.pk, t.sig, t.hash)):
            leaves.append(failed)
            continue
        cost = tx_cost(t, gas_price)
        if cost is None:
            leaves.append(failed)
            continue
        akey = bytes([COL_ACCOUNT]) + t.signer
        av = get(akey)
        if av is None:
            leaves.append(failed)
            continue
        if int.from_bytes(av[:16], 'little') == U128_MAX:
            raise OOD("t.signer_v1: signer account is AccountV2")
        if len(av) != 72:
            raise Reject("StorageInconsistentState: signer account does not decode")
        acct = (int.from_bytes(av[:16], 'little'), int.from_bytes(av[16:32], 'little'),
                struct.unpack('<Q', av[64:72])[0])
        kkey = bytes([COL_ACCESS_KEY]) + t.signer + bytes([COL_ACCESS_KEY]) + u8(0) + t.pk
        kv = get(kkey)
        if kv is None:
            leaves.append(failed)
            continue
        ak = decode_access_key(kv)
        new_amount = verify_and_charge(acct, ak, t, cost, height)
        if new_amount is None:
            leaves.append(failed)
            continue
        rid = sha(t.hash + u64(height) + u64(0))
        pk = u8(0) + t.pk
        rc = (bstr(t.signer) + bstr(t.recv) + rid + u8(0) + bstr(t.signer) + pk + u128(cost['rgp']) +
              u32(0) + u32(0) + u32(1) + u8(3) + u128(t.deposit))
        if t.recv == t.signer:
            local.append((rid, t.signer, pk, cost['rgp'], t.deposit, rc))
        else:
            forward(t.recv, rc, "transaction receipt")
        if balance_burnt + cost['burnt_amount'] > U128_MAX:
            continue  # lib.rs:2224-2244: dropped without outcome or state change
        gas_used += cost['burnt']
        if gas_used > U64_MAX:
            raise Reject("chunk gas overflow (panic)")
        balance_burnt += cost['burnt_amount']
        partial = (u32(1) + rid + u64(cost['burnt']) + u128(cost['burnt_amount']) + bstr(t.signer) +
                   u8(3) + rid)
        leaves.append(sha(u32(2) + t.hash + sha(partial)))
        overlay[akey] = u128(new_amount) + av[16:]
        overlay[kkey] = u64(t.nonce) + bytes([1])

    # -- receipts: local first, then incoming (process_receipts, lib.rs:2658-2721)
    class LR:
        pass
    work = []
    for rid, signer, pk, gp, dep, raw in local:
        if account_type(signer) != 'named':
            raise OOD("r.shape: local receipt to a non-named account")
        x = LR()
        x.pred, x.recv, x.rid, x.signer, x.pk, x.gp, x.deposit, x.raw = signer, signer, rid, signer, pk, gp, dep, raw
        work.append(x)
    ids = [x.rid for x in work] + [x.rid for x in R_list]
    if len(set(ids)) != len(ids):
        raise OOD("e.distinct_ids")
    work.extend(R_list)
    for i, x in enumerate(work):
        if gas_used >= gas_limit:
            raise OOD("e.compute: receipt %d would be delayed" % i)
        akey = bytes([COL_ACCOUNT]) + x.recv
        v = get(akey)
        if v is None:
            raise OOD("r.success: receiver account missing")
        if len(v) != 72 or int.from_bytes(v[:16], 'little') == U128_MAX:
            raise OOD("r.success: receiver is not AccountV1")
        amount = int.from_bytes(v[:16], 'little')
        locked = int.from_bytes(v[16:32], 'little')
        su = struct.unpack('<Q', v[64:72])[0]
        is_system = x.pred == b'system'
        if is_system and x.signer == x.recv:
            ak = get(bytes([COL_ACCESS_KEY]) + x.recv + bytes([COL_ACCESS_KEY]) + x.pk)
            if ak is not None and not (len(ak) == 9 and ak[8] == 1):
                raise OOD("r.refunds: access key of gas refund is not FullAccess")
        na = amount + x.deposit
        if na > U128_MAX:
            raise OOD("r.success: balance overflow")
        if na == U128_MAX:
            raise OOD("r.success: balance hits the AccountV2 sentinel")
        if na + locked > U128_MAX:
            raise OOD("r.success: amount + locked overflow")
        if na + locked < STORAGE_AMOUNT_PER_BYTE * su and su > ZERO_BALANCE_ACCOUNT_STORAGE_LIMIT:
            raise OOD("r.success: storage stake")
        overlay[akey] = u128(na) + v[16:]
        rids = []
        if is_system:
            tokens = 0
        else:
            burn_price = min(x.gp, gas_price)
            tokens = G * burn_price
            refund = G * (x.gp - burn_price)
            if tokens > U128_MAX or refund > U128_MAX:
                raise OOD("r.success: burn/refund overflow")
            balance_burnt += tokens
            if balance_burnt > U128_MAX:
                raise OOD("r.success: total burnt overflow")
            if refund > 0:
                rid = sha(x.rid + u64(height) + u64(0))
                rc = s3.enc_refund_receipt(x.signer, rid, x.pk, refund)
                forward(x.signer, rc, "refund receipt")
                rids.append(rid)
        gas_used += G
        partial = (u32(len(rids)) + b''.join(rids) + u64(G) + u128(tokens) + bstr(x.recv) +
                   u8(2) + u32(0))
        leaves.append(sha(u32(2) + x.rid + sha(partial)))
    py = s3.get_indices(trie, bytes([COL_PROMISE_YIELD_INDICES]), "PromiseYieldIndices")
    if py is not None and py[0] < py[1]:
        raise OOD("e.queues_empty: promise yield queue not empty")
    state_root = s3.finalize(trie, overlay)
    if state_root != W['main']['post_state_root']:
        raise Reject("main transition post_state_root mismatch")
    outcome_root = merkle_root_of_hashes(leaves)
    allowed = L.shard_ids[((height + idx) & U64_MAX) % ns]
    congestion = (own_info[0], own_info[1], own_info[2], allowed)

    # ---- implicit transitions ----
    imp = list(reversed(implicit_idx))
    if len(imp) != len(W['implicit']):
        raise Reject("implicit transitions count mismatch")
    for bi_, T in zip(imp, W['implicit']):
        M = blocks[bi_]
        t2 = PartialTrie(T['base_state'], state_root)
        ov2 = {}
        s3.get_indices(t2, bytes([COL_DELAYED]), "DelayedReceiptIndices")
        s3.run_scheduler_step(t2, ov2, L, M)
        state_root = s3.finalize(t2, ov2)
        if state_root != T['post_state_root']:
            raise Reject("implicit transition post_state_root mismatch")

    # ---- comparison with the endorsed header ----
    if H.prev_state_root != state_root:
        raise Reject("InvalidStateRoot")
    if H.prev_outcome_root != outcome_root:
        raise Reject("InvalidOutcomesProof")
    if H.prev_validator_proposals:
        raise Reject("InvalidValidatorProposals")
    if H.gas_limit != gas_limit:
        raise Reject("InvalidGasLimit")
    if H.prev_gas_used != gas_used:
        raise Reject("InvalidGasUsed")
    if H.prev_balance_burnt != balance_burnt:
        raise Reject("InvalidBalanceBurnt")
    by_shard = {sid: [] for sid in L.shard_ids}
    for shard, _recv, rc in outgoing:
        by_shard[shard].append(rc)
    rh = [sha(sha(u64(sid) + u32(len(by_shard[sid])) + b''.join(by_shard[sid]))) for sid in L.shard_ids]
    if H.prev_outgoing_receipts_root != merkle_root_of_hashes(rh):
        raise Reject("InvalidReceiptsProof")
    if H.congestion_info != congestion:
        raise Reject("InvalidCongestionInfo")
    if H.bandwidth_requests != []:
        raise Reject("InvalidBandwidthRequests")
    if H.proposed_split is not None:
        raise Reject("InvalidChunkHeaderShardSplit")
    if H.tx_root != merklize([t.raw for t in W['new_txs']]):
        raise Reject("InvalidTxRoot")
    body = (u32(len(W['new_txs'])) + b''.join(t.raw for t in W['new_txs']) +
            u32(len(outgoing)) + b''.join(rc for _s, _r, rc in outgoing))
    root, length = encoded_merkle_root(body, dat, tot)
    if root != H.encoded_merkle_root:
        raise Reject("InvalidChunkEncodedMerkleRoot")
    if length != H.encoded_length:
        raise Reject("InvalidChunkEncodedLength")
    return "ok"


def check_case(d):
    try:
        claim_b = open(os.path.join(d, "claim.bin"), "rb").read()
        witness_b = open(os.path.join(d, "witness.bin"), "rb").read()
    except OSError as e:
        return "reject", "cannot read case: %s" % e
    try:
        check_case_inner(claim_b, witness_b)
        return "accept", "ok"
    except OOD as e:
        return "out_of_domain", str(e)
    except Reject as e:
        return "reject", "%s: %s" % (type(e).__name__, e)
    except Exception as e:  # a bug in this checker, never a verdict of the relation
        print("spec_check_v3_d1: INTERNAL ERROR on %s: %r" % (d, e), file=sys.stderr)
        return "reject", "INTERNAL ERROR %s: %s" % (type(e).__name__, e)


def main():
    for d in sys.argv[1:]:
        v, reason = check_case(d)
        print(json.dumps(dict(case=d, verdict=v, reason=reason)))
        sys.stdout.flush()


if __name__ == "__main__":
    main()
