#!/usr/bin/env python3
"""Independent Python reference checker for near/pv86/chunk-validation/v0,
restricted to domain D0.

Written from spec/near-chunk-validation-v0.md, spec/claim-v3.md,
docs/research/chunk-validation-boundary.md and the nearcore 2.13.4 Rust
sources (+ rand 0.8.5, rand_chacha 0.3.1, reed-solomon-erasure 6.0.0, borsh
1.5.3, near-account-id 2.0.0). It does NOT use the Lean formalization.

Usage:
  spec_check_v3.py CASE_DIR...      one JSON line per case:
                                    {"case", "verdict": accept|reject|out_of_domain, "reason"}
  spec_check_v3.py --selftest [VECTORS_DIR]
                                    check the primitives against oracle/fixtures/v3/vectors

Verdict order: claim/witness decoding and the hash/consistency discipline of
the claim are checked first (a malformed claim is `reject`); then the
claim-level D0 conditions (`out_of_domain`); then the relation, where any
witness/execution-level D0 violation met on the way yields `out_of_domain`
and any nearcore Err/panic yields `reject`.
"""
import json
import os
import struct
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from v3lib.prim import (  # noqa: E402
    R, Reject, OOD, DecodeError, sha, u8, u16, u32, u64, u128, bstr, U64_MAX, U128_MAX, ZERO32,
    valid_account_id, account_type, read_public_key, read_signature, merklize,
    merkle_root_of_hashes, compute_root_from_path, ChaCha20Rng, encoded_merkle_root,
    outgoing_gas_limit, PartialTrie)
from v3lib import sched  # noqa: E402

FORMAT_CLAIM = b"near-arena-claim-v3"
FORMAT_WITNESS = b"near-arena-witness-v3"
STATEMENT = b"near/pv86/chunk-validation/v0"

MAX_WITNESS = 64 * 1024 * 1024
D0_MAX_WITNESS = 8 * 1024 * 1024
D0_MAX_BASE_STATE = 3_000_000
D0_MAX_GAS_LIMIT = 10 ** 15  # A1 (mainnet genesis 1000 Tgas)

# PV 86 runtime config (runtime_configs/parameters.yaml + 85.yaml)
NEW_ACTION_RECEIPT_EXEC = 108_059_500_000
TRANSFER_EXEC = 115_123_062_500
CREATE_ACCOUNT_EXEC = 7_200_000_000_000
ADD_FULL_ACCESS_KEY_EXEC = 101_765_125_000
G = NEW_ACTION_RECEIPT_EXEC + TRANSFER_EXEC
STORAGE_AMOUNT_PER_BYTE = 10 ** 19
ZERO_BALANCE_ACCOUNT_STORAGE_LIMIT = 770
MAX_RECEIPT_SIZE = 4_194_304

# trie key columns (core/primitives/src/trie_key.rs)
COL_ACCOUNT = 0
COL_ACCESS_KEY = 2
COL_DELAYED = 7
COL_PROMISE_YIELD_INDICES = 10
COL_BUFFERED_INDICES = 13
COL_BW_STATE = 15
COL_GROUPS_QUEUE_DATA = 16


# ======================================================================
# decoding: nearcore types
# ======================================================================
def read_congestion(r):
    if r.u8() != 0:
        raise DecodeError("CongestionInfo tag")
    return (r.u128(), r.u128(), r.u64(), r.u16())


def read_bw_requests(r):
    if r.u8() != 0:
        raise DecodeError("BandwidthRequests tag")
    return r.vec(lambda: (r.u16(), r.take(5)))


def read_validator_stake(r):
    if r.u8() != 0:
        raise DecodeError("ValidatorStake tag")
    return (r.account(), read_public_key(r), r.u128())


class Inner:
    pass


def read_inner(r):
    """Tagged ShardChunkHeaderInner, V4 (tag 3) or V5 (tag 4) only.
    Returns Inner or raises Unsupported for other versions."""
    start = r.i
    tag = r.u8()
    if tag not in (3, 4):
        raise UnsupportedInner(tag)
    x = Inner()
    x.version = tag
    x.prev_block_hash = r.hash()
    x.prev_state_root = r.hash()
    x.prev_outcome_root = r.hash()
    x.encoded_merkle_root = r.hash()
    x.encoded_length = r.u64()
    x.height_created = r.u64()
    x.shard_id = r.u64()
    x.prev_gas_used = r.u64()
    x.gas_limit = r.u64()
    x.prev_balance_burnt = r.u128()
    x.prev_outgoing_receipts_root = r.hash()
    x.tx_root = r.hash()
    x.prev_validator_proposals = r.vec(lambda: read_validator_stake(r))
    x.congestion_info = read_congestion(r)
    x.bandwidth_requests = read_bw_requests(r)
    x.proposed_split = None
    if tag == 4:
        x.proposed_split = r.option(lambda: (r.account(), r.u64(), r.u64()))
    x.raw = r.b[start:r.i]
    x.chunk_hash = sha(sha(x.raw) + x.encoded_merkle_root)
    return x


class UnsupportedInner(Exception):
    pass


def decode_inner_bytes(b):
    r = R(b)
    x = read_inner(r)
    r.end()
    return x


class Receipt:
    pass


def read_receipt(r):
    """ReceiptV0 (untagged). Any receipt not of the D0 shape raises OOD (r.shape)."""
    start = r.i
    x = Receipt()
    x.pred = r.account()
    x.recv = r.account()
    x.rid = r.hash()
    tag = r.u8()
    if tag != 0:
        raise OOD("r.shape: ReceiptEnum tag %d (not Action)" % tag)
    x.signer = r.account()
    kt = r.u8()
    if kt == 2:
        raise OOD("r.shape: MLDSA65 signer key")
    if kt not in (0, 1):
        raise DecodeError("PublicKey tag")
    x.pk = u8(kt) + r.take(32 if kt == 0 else 64)
    x.gp = r.u128()
    if r.u32() != 0:
        raise OOD("r.shape: output_data_receivers")
    if r.u32() != 0:
        raise OOD("r.shape: input_data_ids")
    na = r.u32()
    if na != 1:
        raise OOD("r.shape: %d actions" % na)
    at = r.u8()
    if at != 3:
        raise OOD("r.shape: action tag %d (not Transfer)" % at)
    x.deposit = r.u128()
    if account_type(x.recv) != 'named':
        raise OOD("r.shape: receiver is not a named account")
    x.raw = r.b[start:r.i]
    return x


def enc_refund_receipt(recv, rid, pk, amount):
    return (bstr(b'system') + bstr(recv) + rid + u8(0) + bstr(recv) + pk + u128(0) +
            u32(0) + u32(0) + u32(1) + u8(3) + u128(amount))


def read_partial_state(r):
    if r.u8() != 0:
        raise DecodeError("PartialState tag")
    return r.vec(r.bytes)


def read_transition(r):
    return dict(block_hash=r.hash(), base_state=read_partial_state(r), post_state_root=r.hash())


def decode_state_witness(b):
    r = R(b)
    if r.u8() != 1:
        raise DecodeError("ChunkStateWitness tag")
    w = dict(epoch_id=r.hash())
    if r.u8() != 2:
        raise Reject("ShardChunkHeader version is not V3")
    try:
        w['inner'] = read_inner(r)
    except UnsupportedInner as e:
        raise Reject("witness chunk header inner version tag %d" % e.args[0])
    w['height_included'] = r.u64()
    read_signature(r)
    w['main'] = read_transition(r)
    proofs = {}
    n = r.u32()
    for _ in range(n):
        key = r.hash()
        receipts = r.vec(lambda: read_receipt(r))
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
    if r.u32() != 0:
        raise OOD("w.no_txs: witness transactions non-empty")
    w['implicit'] = r.vec(lambda: read_transition(r))
    if r.u32() != 0:
        raise OOD("w.no_txs: witness new_transactions non-empty")
    r.end()
    return w


# ---------------- ShardLayout ----------------
class Layout:
    pass


def decode_layout(b):
    r = R(b)
    tag = r.u8()
    if tag not in (2, 3):
        raise OOD("c.layout: ShardLayout V%d" % tag)
    L = Layout()
    L.version = tag
    L.boundary = r.vec(r.account)
    L.shard_ids = r.vec(r.u64)

    def bmap(kf, vf):
        d = {}
        for _ in range(r.u32()):
            k = kf()
            d[k] = vf()
        return d
    L.index = bmap(r.u64, r.u64)
    if tag == 2:
        bmap(r.u64, r.u64)  # index_to_id_map
        r.option(lambda: bmap(r.u64, lambda: r.vec(r.u64)))
        r.option(lambda: bmap(r.u64, r.u64))
        r.u32()
    else:
        bmap(r.u64, lambda: r.vec(r.u64))
        r.u64()
        bmap(r.u64, lambda: r.vec(r.u64))
    r.end()
    if len(L.shard_ids) != len(L.boundary) + 1:
        raise Reject("layout: boundary/shard count mismatch")
    return L


def account_to_shard(L, acc):
    lo, hi = 0, len(L.boundary)
    while lo < hi:  # partition_point(|b| b <= acc)
        mid = (lo + hi) // 2
        if L.boundary[mid] <= acc:
            lo = mid + 1
        else:
            hi = mid
    return L.shard_ids[lo]


# ---------------- claim ----------------
class Block:
    pass


def decode_inner_lite(b):
    r = R(b)
    x = dict(height=r.u64(), epoch_id=r.hash(), next_epoch_id=r.hash(), prev_state_root=r.hash(),
             prev_outcome_root=r.hash(), timestamp=r.u64(), next_bp_hash=r.hash(),
             block_merkle_root=r.hash())
    r.end()
    return x


def decode_inner_rest_v6(b):
    r = R(b)
    x = dict(block_body_hash=r.hash(), prev_chunk_outgoing_receipts_root=r.hash(),
             chunk_headers_root=r.hash(), chunk_tx_root=r.hash(), random_value=r.hash())
    x['prev_validator_proposals'] = r.vec(lambda: read_validator_stake(r))
    x['chunk_mask'] = r.vec(r.boolean)
    x['next_gas_price'] = r.u128()
    x['total_supply'] = r.u128()
    r.hash(); r.hash()  # last_final_block, last_ds_final_block
    r.u64(); r.u64()    # block_ordinal, prev_height
    r.option(r.hash)    # epoch_sync_data_hash
    r.vec(lambda: r.option(lambda: read_signature(r)))  # approvals
    r.u32()             # latest_protocol_version
    r.vec(r.bytes)      # chunk_endorsements bitmap
    r.option(lambda: (r.u64(), r.account()))  # shard_split
    r.end()
    return x


def chain_id_ok(c):
    return 1 <= len(c) <= 64 and all(0x21 <= x <= 0x7e for x in c)


def decode_claim(b):
    r = R(b)
    if r.bytes() != FORMAT_CLAIM:
        raise DecodeError("claim format id")
    if r.bytes() != STATEMENT:
        raise DecodeError("claim statement id")
    c = dict(pv=r.u32(), chain_id=r.bytes(), epoch_id=r.hash(), chunk_inner=r.bytes())
    nb = r.u32()
    blocks = []
    for _ in range(nb):
        x = Block()
        x.header_version = r.u8()
        x.prev_hash = r.hash()
        x.lite_raw = r.bytes()
        x.rest_raw = r.bytes()
        x.slots_raw = r.vec(lambda: (r.bytes(), r.u64()))
        blocks.append(x)
    c['blocks'] = blocks
    c['rs_data'] = r.u16()
    c['rs_total'] = r.u16()

    def epoch_rec():
        e = dict(epoch_id=r.hash(), pv=r.u32(), height=r.u64(), layout_raw=r.bytes())
        e['validators'] = r.vec(lambda: (r.bytes(), r.u128()))
        return e
    c['epochs'] = r.vec(epoch_rec)

    def flag():
        f = r.u8()
        if f > 1:
            raise DecodeError("flag not 0/1")
        return f
    c['epoch_start_after'] = r.vec(flag)

    def acct_list():
        return r.vec(lambda: (r.bytes(), r.u128()))

    def apply_facts():
        vu = r.option(lambda: (acct_list(), acct_list(), r.option(r.bytes)))
        ms = r.u128()
        sg = r.option(lambda: (r.u64(), r.u64(), r.u64(), r.vec(r.u64), r.vec(r.u64)))
        return dict(validator_update=vu, minimum_stake=ms, split_gate=sg)
    c['apply_facts'] = r.vec(apply_facts)
    c['tx_valid'] = r.vec(flag)
    c['genesis_chunk_extra'] = r.option(r.bytes)
    r.end()
    return c


def check_sorted_accounts(lst):
    for i, (a, _) in enumerate(lst):
        if not valid_account_id(a):
            raise Reject("claim: invalid account id")
        if i and not (lst[i - 1][0] < a):
            raise Reject("claim: account list not strictly ascending")


# ======================================================================
# the relation
# ======================================================================
def block_hash(b):
    return sha(sha(sha(b.lite_raw) + sha(b.rest_raw)) + b.prev_hash)


def ctx_congestion(blk):
    """BlockCongestionInfo: BTreeMap keyed by each slot header's shard_id."""
    d = {}
    for s in blk.slots:
        missed = blk.height - s.height_included
        if missed < 0:
            raise Reject("slot height_included > block height (panic)")
        d[s.inner.shard_id] = (s.inner.congestion_info, missed)
    return d


def ctx_bw_requests(blk):
    d = {}
    for s in blk.slots:
        d[s.inner.shard_id] = s.inner.bandwidth_requests
    return d


class Slot:
    pass


def get_indices(trie, key, what):
    v = trie.get(key)
    if v is None:
        return None
    if len(v) != 16:
        raise OOD("e.queues_empty: %s does not decode" % what)
    return struct.unpack('<QQ', v)


def run_scheduler_step(trie, overlay, L, blk, write=True):
    """reads 0x0f, runs the scheduler for block `blk`, writes 0x0f into overlay."""
    v = trie.get(bytes([COL_BW_STATE]))
    prev = None
    if v is not None:
        try:
            prev = sched.decode_state(v)
        except DecodeError:
            raise OOD("e.scheduler_state: 0x0f does not decode as BandwidthSchedulerState::V1")
    new_state, grants = sched.run(L, prev, ctx_congestion(blk), ctx_bw_requests(blk), blk.prev_hash)
    overlay[bytes([COL_BW_STATE])] = new_state
    return grants


def finalize(trie, overlay):
    for k in sorted(overlay):
        trie.insert(k, overlay[k])
    return trie.root


def check_case_inner(claim_b, witness_b):
    # ---------------- decoding ----------------
    c = decode_claim(claim_b)
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
    W = decode_state_witness(sw)

    # ---------------- claim well-formedness / hash discipline ----------------
    if not chain_id_ok(c['chain_id']):
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
        b.lite = decode_inner_lite(b.lite_raw)
        b.rest = decode_inner_rest_v6(b.rest_raw)
        b.height = b.lite['height']
        b.hash = block_hash(b)
        b.slots = []
        for raw, hi in b.slots_raw:
            s = Slot()
            try:
                s.inner = decode_inner_bytes(raw)
            except UnsupportedInner as e:
                raise OOD("c.headers: chunk inner version tag %d" % e.args[0])
            s.height_included = hi
            b.slots.append(s)
    try:
        H = decode_inner_bytes(c['chunk_inner'])
    except UnsupportedInner as e:
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
    # epochs table
    eps = c['epochs']
    for i in range(1, len(eps)):
        if not (eps[i - 1]['epoch_id'] < eps[i]['epoch_id']):
            raise Reject("claim: epochs not strictly ascending")
    epmap = {e['epoch_id']: e for e in eps}
    referenced = {c['epoch_id']} | {b.lite['epoch_id'] for b in blocks}
    if set(epmap) != referenced:
        raise Reject("claim: epoch table does not hold exactly the referenced epochs")
    for e in eps:
        check_sorted_accounts(e['validators'])
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
            check_sorted_accounts(st)
            check_sorted_accounts(rw)
    # witness epoch / header
    if W['epoch_id'] != c['epoch_id']:
        raise Reject("witness epoch_id != claim epoch_id")
    if W['inner'].raw != c['chunk_inner']:
        raise Reject("witness chunk header inner != claim chunk_inner")

    # ---------------- claim-level D0 conditions ----------------
    if c['pv'] != 86:
        raise OOD("c.pv86")
    if len(eps) != 1 or any(b.lite['epoch_id'] != c['epoch_id'] for b in blocks) or any(esa):
        raise OOD("c.single_epoch")
    L = decode_layout(epmap[c['epoch_id']]['layout_raw'])
    ns = len(L.shard_ids)
    if not (1 <= ns <= 64):
        raise OOD("c.layout: %d shards" % ns)
    for b in blocks:
        if len(b.slots) != ns:
            raise Reject("claim: slot count != number of shards")
    if any(af['split_gate'] is not None for af in c['apply_facts']):
        raise OOD("c.no_split_gate")
    if c['tx_valid']:
        raise OOD("c.no_tx_flags")
    if n > 32:
        raise OOD("c.segment: n_blocks > 32")

    # ---------------- backward walk (single epoch, no resharding) ----------------
    s0 = H.shard_id
    if s0 not in L.index:
        raise Reject("chunk shard_id not in the epoch's layout")
    idx = L.index[s0]
    if idx >= ns:
        raise Reject("shard index out of range")
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
        raise Reject("no last new chunk found")  # genesis without new chunk: cannot happen
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
    if len(c['tx_valid']) != 0:
        raise Reject("claim: tx_valid length")
    own_slot = B2.slots[idx]
    # A1: chunk gas_limit (a genesis constant) at most mainnet's 1000 Tgas
    if own_slot.inner.gas_limit > D0_MAX_GAS_LIMIT:
        raise OOD("c.gas_limit: chunk gas_limit above 10^15")
    cong_b2 = ctx_congestion(B2)
    if s0 not in cong_b2:
        raise OOD("c.own_congestion_zero: no congestion info for own shard")
    own_info = cong_b2[s0][0]
    if own_info[0] or own_info[1] or own_info[2]:
        raise OOD("c.own_congestion_zero")

    # ---------------- witness-level size bound ----------------
    if sum(len(v) for v in W['main']['base_state']) > D0_MAX_BASE_STATE:
        raise OOD("w.size: main base_state > 3 000 000 bytes")

    # ---------------- source receipt proofs ----------------
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
                # A2 (w.proof_routing): every receipt of a used proof routes to the target shard
                if any(account_to_shard(L, x.recv) != s0 for x in receipts):
                    raise OOD("w.proof_routing: receipt proof holds a receipt routed to another shard")
                expected += 1
                block_proofs.append(receipts)
            # filter_incoming_receipts_for_shard (unconditional; keeps every proof)
            block_proofs = [[x for x in rs if account_to_shard(L, x.recv) == s0] for rs in block_proofs]
            ChaCha20Rng(S.prev_hash).shuffle(block_proofs)
            for receipts in block_proofs:
                R_list.extend(receipts)
        if len(proofs) != expected:
            raise Reject("source_receipt_proofs contains too many proofs")
    if len({x.rid for x in R_list}) != len(R_list):
        raise OOD("e.distinct_ids")
    if sha(u32(len(R_list)) + b''.join(x.raw for x in R_list)) != W['applied_receipts_hash']:
        raise Reject("applied_receipts_hash mismatch")
    if own_slot.inner.tx_root != ZERO32:  # merklize([]) of the witness transactions
        raise Reject("tx_root of last new chunk != merklize(witness transactions)")

    # ---------------- main transition (Runtime::apply, new chunk) ----------------
    gas_limit = own_slot.inner.gas_limit
    gas_price = blocks[b2i + 1].rest['next_gas_price']
    height = B2.height
    trie = PartialTrie(W['main']['base_state'], own_slot.inner.prev_state_root)
    overlay = {}
    d = get_indices(trie, bytes([COL_DELAYED]), "DelayedReceiptIndices")
    if d is not None and d[0] != d[1]:
        raise OOD("e.queues_empty: delayed receipt queue not empty")
    grants = run_scheduler_step(trie, overlay, L, B2)
    # ReceiptSink::new
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

    leaves = []
    outgoing = []
    balance_burnt = 0
    gas_used = 0
    for i, x in enumerate(R_list):
        if gas_used >= gas_limit:  # total.compute >= compute_limit -> delayed
            raise OOD("e.compute: receipt %d would be delayed" % i)
        akey = bytes([COL_ACCOUNT]) + x.recv
        v = overlay.get(akey)
        if v is None:
            v = trie.get(akey)
        if v is None:
            raise OOD("r.success: receiver account missing")
        if len(v) != 72 or int.from_bytes(v[:16], 'little') == U128_MAX:
            raise OOD("r.success: receiver is not AccountV1")
        amount = int.from_bytes(v[:16], 'little')
        locked = int.from_bytes(v[16:32], 'little')
        su = struct.unpack('<Q', v[64:72])[0]
        is_system = x.pred == b'system'
        if is_system and x.signer == x.recv:
            handle = x.pk  # PublicKeyHandle borsh = PublicKey borsh for ED25519/SECP256K1
            ak = trie.get(bytes([COL_ACCESS_KEY]) + x.recv + bytes([COL_ACCESS_KEY]) + handle)
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
                rc = enc_refund_receipt(x.signer, rid, x.pk, refund)
                shard = account_to_shard(L, x.signer)
                size = min(len(rc), MAX_RECEIPT_SIZE)
                atype = account_type(x.signer)
                cg = NEW_ACTION_RECEIPT_EXEC + TRANSFER_EXEC
                if atype in ('eth', 'det'):
                    cg += CREATE_ACCOUNT_EXEC
                elif atype == 'near':
                    cg += CREATE_ACCOUNT_EXEC + ADD_FULL_ACCESS_KEY_EXEC
                admission = min(cg, 1_000_000_000_000_000)
                lim = limits.setdefault(shard, [U64_MAX, 0])
                if lim[0] >= admission and lim[1] >= size:
                    lim[0] = max(lim[0] - cg, 0)
                    lim[1] -= size
                    outgoing.append((shard, x.signer, rc))
                else:
                    raise OOD("e.forwarded: refund receipt would be buffered")
                rids.append(rid)
        gas_used += G
        partial = (u32(len(rids)) + b''.join(rids) + u64(G) + u128(tokens) + bstr(x.recv) +
                   u8(2) + u32(0))
        leaves.append(sha(u32(2) + x.rid + sha(partial)))
    py = get_indices(trie, bytes([COL_PROMISE_YIELD_INDICES]), "PromiseYieldIndices")
    if py is not None and py[0] < py[1]:
        raise OOD("e.queues_empty: promise yield queue not empty")
    state_root = finalize(trie, overlay)
    if state_root != W['main']['post_state_root']:
        raise Reject("main transition post_state_root mismatch")
    outcome_root = merkle_root_of_hashes(leaves)
    allowed = L.shard_ids[((height + idx) & U64_MAX) % ns]  # wrapping_add, checked_rem
    congestion = (own_info[0], own_info[1], own_info[2], allowed)

    # ---------------- implicit transitions ----------------
    imp = list(reversed(implicit_idx))
    if len(imp) != len(W['implicit']):
        raise Reject("implicit transitions count mismatch")
    for bi_, T in zip(imp, W['implicit']):
        M = blocks[bi_]
        t2 = PartialTrie(T['base_state'], state_root)
        ov2 = {}
        dd = get_indices(t2, bytes([COL_DELAYED]), "DelayedReceiptIndices")
        del dd
        run_scheduler_step(t2, ov2, L, M)
        state_root = finalize(t2, ov2)
        if state_root != T['post_state_root']:
            raise Reject("implicit transition post_state_root mismatch")

    # ---------------- comparison with the endorsed header ----------------
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
    if H.tx_root != ZERO32:
        raise Reject("InvalidTxRoot")
    body = u32(0) + u32(len(outgoing)) + b''.join(rc for _s, _r, rc in outgoing)
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
        print("spec_check_v3: INTERNAL ERROR on %s: %r" % (d, e), file=sys.stderr)
        return "reject", "INTERNAL ERROR %s: %s" % (type(e).__name__, e)


# ======================================================================
# self test against oracle/fixtures/v3/vectors
# ======================================================================
def selftest(vdir):
    from v3lib import prim
    ok = True

    def report(name, bad, total):
        nonlocal ok
        ok &= bad == 0
        print("%-12s %d/%d ok" % (name, total - bad, total))

    ch = json.load(open(os.path.join(vdir, "chacha.json")))
    bad = tot = 0
    for s in ch['streams']:
        rng = ChaCha20Rng(bytes.fromhex(s['seed']))
        tot += 1
        bad += [rng.next_u32() for _ in s['u32']] != s['u32']
    for s in ch['shuffles']:
        lst = list(range(s['n']))
        ChaCha20Rng(bytes.fromhex(s['seed'])).shuffle(lst)
        tot += 1
        bad += lst != s['perm']
    lst = list(range(7))
    ChaCha20Rng(sha(bytes([1, 2, 3, 4, 5]))).shuffle(lst)
    tot += 1
    bad += lst != ch['nearcore_test_vector']
    report("chacha", bad, tot)

    cg = json.load(open(os.path.join(vdir, "congestion.json")))
    bad = 0
    for cs in cg['cases']:
        info = (int(cs['delayed_receipts_gas']), int(cs['buffered_receipts_gas']), cs['receipt_bytes'],
                cs['allowed_shard'])
        lvl = prim.congestion_level(info, cs['missed_chunks_count'])
        e = (struct.pack('>d', lvl).hex() != cs['level_bits'] or (lvl == 1.0) != cs['fully_congested']
             or prim.outgoing_gas_limit(info, cs['missed_chunks_count'], cs['allowed_shard'])
             != cs['outgoing_gas_limit_from_allowed']
             or prim.outgoing_gas_limit(info, cs['missed_chunks_count'], (cs['allowed_shard'] + 1) % 65536)
             != cs['outgoing_gas_limit_from_other'])
        bad += e
    report("congestion", bad, len(cg['cases']))

    rs = json.load(open(os.path.join(vdir, "rs.json")))
    bad = 0
    for cs in rs['cases']:
        data = bytes.fromhex(cs['borsh_bytes'])
        parts, n = prim.rs_encode(data, cs['data_parts'], cs['total_parts'])
        root, _ = encoded_merkle_root(data, cs['data_parts'], cs['total_parts'])
        e = (n != cs['encoded_length'] or root.hex() != cs['encoded_merkle_root']
             or [sha(p).hex() for p in parts] != cs['part_sha256'])
        bad += e
    report("rs", bad, len(rs['cases']))

    sc = json.load(open(os.path.join(vdir, "scheduler.json")))
    bad = 0
    for cs in sc['cases']:
        L = decode_layout(bytes.fromhex(cs['shard_layout_borsh']))
        prev = bytes.fromhex(cs['prev_state_borsh']) if cs.get('prev_state_borsh') else None
        cong = {x['shard_id']: ((int(x['delayed_receipts_gas']), int(x['buffered_receipts_gas']),
                                 x['receipt_bytes'], x['allowed_shard']), x['missed_chunks_count'])
                for x in cs['congestion']}
        bw = {}
        for x in cs['bandwidth_requests']:
            r = R(bytes.fromhex(x['requests_borsh']))
            bw[x['shard_id']] = read_bw_requests(r)
            r.end()
        new, _ = sched.run(L, sched.decode_state(prev) if prev else None, cong, bw,
                           bytes.fromhex(cs['prev_block_hash']))
        e = new.hex() != cs['post_state_borsh']
        # trie roots: the vector's state is {0x00 'a' 'b': [1; 72], 0x0f: prev?}
        if not e:
            t = PartialTrie([], ZERO32)
            t.insert(b'\x00ab', b'\x01' * 72)
            if prev is not None:
                t.insert(b'\x0f', prev)
            pre = t.root
            t.insert(b'\x0f', new)
            if pre.hex() != cs['pre_root'] or t.root.hex() != cs['post_root']:
                e = 'root'
        if e:
            bad += 1
            if bad <= 3:
                print("  scheduler mismatch (%s): height %s own %s" % (e, cs['block_height'], cs['own_shard_id']))
    report("scheduler", bad, len(sc['cases']))
    return ok


def main():
    args = sys.argv[1:]
    if args and args[0] == "--selftest":
        vdir = args[1] if len(args) > 1 else os.path.join(
            os.path.dirname(os.path.abspath(__file__)), "..", "fixtures", "v3", "vectors")
        sys.exit(0 if selftest(vdir) else 1)
    for d in args:
        v, reason = check_case(d)
        print(json.dumps(dict(case=d, verdict=v, reason=reason)))
        sys.stdout.flush()


if __name__ == "__main__":
    main()
