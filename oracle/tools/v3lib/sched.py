"""Multi-shard bandwidth scheduler, transcribed from
runtime/runtime/src/bandwidth_scheduler/{mod.rs,scheduler.rs,distribute_remaining.rs}
and core/primitives/src/bandwidth_scheduler.rs (nearcore 2.13.4, PV 86 config)."""
from .prim import (R, DecodeError, ChaCha20Rng, sha, u8, u32, u64, U64_MAX, ZERO32,
                   congestion_level)

MAX_SHARD_BANDWIDTH = 4_500_000
MAX_SINGLE_GRANT = 4_194_304
MAX_ALLOWANCE = 4_500_000
MAX_BASE_BANDWIDTH = 100_000
MAX_RECEIPT_SIZE = 4_194_304
NUM_VALUES = 40


def decode_state(v):
    """strict borsh BandwidthSchedulerState::V1 -> (links, hash)."""
    r = R(v)
    if r.u8() != 0:
        raise DecodeError("BandwidthSchedulerState tag")
    links = r.vec(lambda: (r.u64(), r.u64(), r.u64()))
    h = r.hash()
    r.end()
    return links, h


def encode_state(links, h):
    return u8(0) + u32(len(links)) + b''.join(u64(s) + u64(t) + u64(a) for s, t, a in links) + h


def params(n):
    base = (MAX_SHARD_BANDWIDTH - MAX_SINGLE_GRANT) // max(1, n - 1)
    return min(base, MAX_BASE_BANDWIDTH)


def request_values(base):
    return [base + (MAX_SINGLE_GRANT - base) * (i + 1) // NUM_VALUES for i in range(NUM_VALUES)]


def run(layout, prev_state, congestion, bw_requests, seed):
    """layout: object with .shard_ids (index order) and .index (id -> index).
    prev_state: (links, hash) or None.
    congestion: dict shard_id -> (info(delayed,buffered,bytes,allowed), missed).
    bw_requests: dict shard_id -> list of (to_shard u16, bitmap 5 bytes).
    Returns (new_state_bytes, granted: dict (sender_id, receiver_id) -> bandwidth)."""
    ids = layout.shard_ids
    n = len(ids)
    idx = layout.index
    links_prev, h_prev = prev_state if prev_state is not None else ([], ZERO32)
    base = params(n)

    allowance = [None] * (n * n)
    for s, t, a in links_prev:
        if s in idx and t in idx:
            allowance[idx[s] * n + idx[t]] = a

    status = [None] * n
    for sid in sorted(congestion):
        if sid in idx:
            info, missed = congestion[sid]
            lvl = congestion_level(info, missed)
            status[idx[sid]] = (missed > 0, idx.get(info[3]), lvl == 1.0)

    def calc_allowed(s, r):
        rs = status[r]
        if rs is None:
            return False
        if rs[0]:
            return False
        ss = status[s]
        if ss is not None and ss[0]:
            return False
        if rs[2]:
            return s == rs[1]
        return True

    allowed = [calc_allowed(s, r) for s in range(n) for r in range(n)]

    values = request_values(base)
    requests = []
    for sender in sorted(bw_requests):
        for to_shard, bitmap in bw_requests[sender]:
            if sender not in idx or to_shard not in idx:
                continue
            link = idx[sender] * n + idx[to_shard]
            incs = []
            cur = base
            for bit in range(NUM_VALUES):
                if not (bitmap[bit // 8] >> (bit % 8)) & 1:
                    continue
                v = values[bit]
                if v <= cur:
                    continue
                incs.append(v - cur)
                cur = v
            if incs:
                requests.append([link, incs])

    send_budget = [MAX_SHARD_BANDWIDTH] * n
    recv_budget = [MAX_SHARD_BANDWIDTH] * n
    granted = [None] * (n * n)

    def get_allow(l):
        a = allowance[l]
        return 0 if a is None else a

    fair = MAX_SHARD_BANDWIDTH // n
    for l in range(n * n):
        a = min(get_allow(l) + fair, U64_MAX)
        if a > MAX_ALLOWANCE:
            a = MAX_ALLOWANCE
        allowance[l] = a

    def grant_more(l, bw):
        cur = granted[l] or 0
        nv = cur + bw
        granted[l] = nv if nv <= U64_MAX else U64_MAX

    def try_grant(l, bw):
        if not allowed[l]:
            return False
        s, r = divmod(l, n)
        if send_budget[s] < bw or recv_budget[r] < bw:
            return False
        send_budget[s] -= bw
        recv_budget[r] -= bw
        allowance[l] = max(get_allow(l) - bw, 0)
        grant_more(l, bw)
        return True

    for l in range(n * n):
        try_grant(l, base)

    rng = ChaCha20Rng(seed)
    buckets = {}
    for req in requests:
        buckets.setdefault(get_allow(req[0]), []).append(req)
    while buckets:
        k = max(buckets)
        reqs = buckets.pop(k)
        rng.shuffle(reqs)
        for req in reqs:
            if not req[1]:
                continue
            inc = req[1].pop(0)
            if try_grant(req[0], inc):
                if req[1]:
                    buckets.setdefault(get_allow(req[0]), []).append(req)

    # distribute_remaining_bandwidth
    s_left = list(send_budget)
    r_left = list(recv_budget)
    s_links = [0] * n
    r_links = [0] * n
    for s in range(n):
        for r in range(n):
            if allowed[s * n + r]:
                s_links[s] += 1
                r_links[r] += 1

    def avg(left, links, i):
        return 0 if links[i] == 0 else left[i] // links[i]
    senders = sorted(range(n), key=lambda i: avg(s_left, s_links, i))
    receivers = sorted(range(n), key=lambda i: avg(r_left, r_links, i))
    remaining = {}
    for s in senders:
        for r in receivers:
            if not allowed[s * n + r]:
                continue
            if s_links[s] == 0 or r_links[r] == 0:
                break
            g = min(s_left[s] // s_links[s], r_left[r] // r_links[r])
            remaining[s * n + r] = g
            s_left[s] -= g
            s_links[s] -= 1
            r_left[r] -= g
            r_links[r] -= 1
    for l in range(n * n):
        if l in remaining:
            grant_more(l, remaining[l])

    grants = {}
    for l in range(n * n):
        if granted[l] is not None:
            s, r = divmod(l, n)
            grants[(ids[s], ids[r])] = granted[l]

    new_links = []
    for l in range(n * n):
        if allowance[l] is not None:
            s, r = divmod(l, n)
            new_links.append((ids[s], ids[r], allowance[l]))
    all_ids = u32(n) + b''.join(u64(x) for x in ids)
    new_hash = sha(h_prev + sha(all_ids))
    return encode_state(new_links, new_hash), grants
