#!/usr/bin/env python3
"""Build historical replay fixtures from AUTHENTIC NEAR mainnet data.

Data sources (all public, no credentials):
  * JSON-RPC (default https://archival-rpc.mainnet.fastnear.com): blocks, chunks,
    receipts, transaction status, protocol config, account views, peers.
  * NEAR P2P state sync (via `near-arena-historical`, this crate): the epoch's
    state-sync header and state parts -- raw trie nodes of the shard trie at
    the sync point, served by ordinary mainnet nodes to any peer.

Nothing here fabricates state: every trie node comes from a mainnet peer and is
hash-checked against an on-chain state root by nearcore itself; receipts and
block/chunk fields come from RPC and are cross-checked (see `anchors` in each
case's provenance.json). See docs/HISTORICAL_REPLAY.md.

Usage:
  harvest.py sync-point [--epoch-start H]
      Print the current (or given) epoch's state-sync point and the chunks whose
      pre-state is the state-sync root (the only roots whose trie nodes are
      publicly retrievable).
  harvest.py candidates [--from H --to H]
      List receipts that may be in the v1 domain (single Transfer, named
      receiver, predecessor == signer, SuccessValue) executed in the current
      epoch's sync-prev chunks (exact candidates), or in blocks [from, to)
      (rebased candidates). Uses neardata.xyz block JSON. `build` re-verifies
      every property from RPC.
  harvest.py build --shard S --receipt ID [--receipt ID ...] --name NAME
                   [--out oracle/fixtures/historical]
      Fetch the parts needed for the receivers (plus whatever Runtime::apply
      reads), run the oracle on them, check every anchor and write
      cases/NAME/{request,witness,expected_claim,apply_witness}.bin,
      diagnostics.json, provenance.json.
      The batch receipts must have been executed in the same chunk; the batch
      context (height, gas price, gas limit) is that chunk's. If that chunk's
      prev_state_root is the sync root the case is `historical-exact-*`,
      otherwise `historical-rebased-prestate` (pre-state is the earlier sync
      root of the same shard and epoch).

Environment: NEAR_RPC (endpoint), PARTS_DIR (part cache, default ./parts).
"""
import argparse
import base64
import datetime
import hashlib
import json
import os
import re
import subprocess
import sys
import time
import urllib.error
import urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))
ORACLE_DIR = os.path.dirname(HERE)
REPO = os.path.dirname(ORACLE_DIR)
FETCH = os.path.join(HERE, "target/debug/near-arena-historical")
RPC = os.environ.get("NEAR_RPC", "https://archival-rpc.mainnet.fastnear.com")
PEER_RPC = "https://rpc.mainnet.near.org"
PARTS_DIR = os.environ.get("PARTS_DIR", os.path.join(os.getcwd(), "parts"))
G = 108_059_500_000 + 115_123_062_500
B58 = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
LOG = []


def now():
    return datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def b58(s):
    n = 0
    for c in s:
        n = n * 58 + B58.index(c)
    return n.to_bytes(32, "big")


def b58enc(b):
    n = int.from_bytes(b, "big")
    s = ""
    while n:
        n, r = divmod(n, 58)
        s = B58[r] + s
    return "1" * (len(b) - len(b.lstrip(b"\0"))) + s


def sha(b):
    return hashlib.sha256(b).digest()


# ---------------------------------------------------------------- RPC
def rpc(method, params, ep=None):
    ep = ep or RPC
    body = json.dumps({"jsonrpc": "2.0", "id": 1, "method": method, "params": params}).encode()
    for i in range(30):
        time.sleep(0.25)  # stay well under public rate limits
        try:
            req = urllib.request.Request(ep, body, {"Content-Type": "application/json"})
            r = json.load(urllib.request.urlopen(req, timeout=60))
        except urllib.error.HTTPError as e:
            try:
                r = json.load(e)
            except Exception:
                time.sleep(3 + 2 * i)
                continue
        except Exception:
            time.sleep(3 + 2 * i)
            continue
        if "error" in r:
            err = r["error"]
            if err.get("code") == -429 or "Rate limit" in json.dumps(err):
                print(f"  rate limited by {ep}; backing off", file=sys.stderr)
                time.sleep(10 + 5 * i)
                continue
            return {"__error__": err}
        LOG.append({"t": now(), "endpoint": ep, "method": method, "params": params})
        return r["result"]
    raise RuntimeError(f"rpc {method} {params} failed")


def blk_at(h):
    b = rpc("block", {"block_id": h})
    if "__error__" in b:
        e = b["__error__"]
        name = (e.get("cause") or {}).get("name") or e.get("name")
        if name == "UNKNOWN_BLOCK":
            return None
        raise RuntimeError(f"block {h}: {e}")
    return b


def next_blk(h):
    h += 1
    while True:
        b = blk_at(h)
        if b:
            return b
        h += 1


def sync_point(epoch_start):
    """nearcore chain/chain/src/state_sync/utils.rs: sync_prev = first block of the
    epoch (not counting the epoch's first block) after which every shard has >= 2
    new chunks; sync = the next block. State parts are for
    sync_prev.chunks[s].prev_state_root (state_sync/adapter.rs)."""
    b = blk_at(epoch_start)
    ep = b["header"]["epoch_id"]
    counts = [0] * len(b["header"]["chunk_mask"])
    prev = b
    while True:
        nb = next_blk(prev["header"]["height"])
        assert nb["header"]["prev_hash"] == prev["header"]["hash"]
        assert nb["header"]["epoch_id"] == ep
        counts = [c + int(m) for c, m in zip(counts, nb["header"]["chunk_mask"])]
        if all(c >= 2 for c in counts):
            sp = nb
            break
        prev = nb
    s = next_blk(sp["header"]["height"])
    assert s["header"]["prev_hash"] == sp["header"]["hash"]
    return {
        "epoch_id": ep,
        "epoch_start_height": epoch_start,
        "sync_prev_height": sp["header"]["height"],
        "sync_prev_hash": sp["header"]["hash"],
        "sync_hash": s["header"]["hash"],
        "sync_height": s["header"]["height"],
        "chunks": {
            c["shard_id"]: {
                "chunk_hash": c["chunk_hash"],
                "height_included": c["height_included"],
                "new_chunk": c["height_included"] == sp["header"]["height"],
                "prev_state_root": c["prev_state_root"],
            }
            for c in sp["chunks"]
        },
    }


# ---------------------------------------------------------------- P2P parts
class Parts:
    def __init__(self, sync_hash, shard, head_height):
        self.sync, self.shard, self.head = sync_hash, shard, head_height
        os.makedirs(PARTS_DIR, exist_ok=True)
        self.peers = []
        self.all_peers = [
            p["id"] + "@" + p["addr"] for p in rpc("network_info", [], PEER_RPC)["active_peers"] if p.get("addr")
        ]
        self.meta = {}

    def _run(self, args):
        env = dict(os.environ, NEAR_HEAD_HEIGHT=str(self.head))
        r = subprocess.run([FETCH] + args, capture_output=True, text=True, timeout=300, env=env)
        return r.stdout.strip().splitlines()[-1] if r.stdout.strip() else "", r.stderr.strip()[-300:]

    def _try_peers(self, args, ok_marker):
        for p in self.peers + [x for x in self.all_peers if x not in self.peers]:
            out, err = self._run([args[0], p] + args[1:])
            if ok_marker in out:
                if p not in self.peers:
                    self.peers.insert(0, p)
                return p, json.loads(out)
        raise RuntimeError(f"no peer answered {args}")

    def header(self):
        f = os.path.join(PARTS_DIR, f"{self.sync}_s{self.shard}_header.bin")
        peer, h = self._try_peers(["header", self.sync, str(self.shard), f], "num_state_parts")
        h.update(peer=peer, retrieved_at=now(), sha256=sha(open(f, "rb").read()).hex())
        self.num_parts = h["num_state_parts"]
        self.root = h["state_root_node_hash"]
        return h

    def fetch(self, pid):
        name = f"{self.sync}_s{self.shard}_p{pid}.bin"
        f = os.path.join(PARTS_DIR, name)
        flog = os.path.join(PARTS_DIR, "fetch_log.jsonl")
        if not os.path.exists(f):
            peer, _ = self._try_peers(["part", self.sync, str(self.shard), str(pid), f], '"part_id"')
            with open(flog, "a") as fl:
                fl.write(json.dumps({"file": name, "peer": peer, "retrieved_at": now(),
                                     "sha256": sha(open(f, "rb").read()).hex()}) + "\n")
        b = open(f, "rb").read()
        m = self.meta.setdefault(pid, {})
        if "retrieved_at" not in m:
            m.update(peer="unknown", retrieved_at="unknown")
            if os.path.exists(flog):
                for line in open(flog):
                    e = json.loads(line)
                    if e["file"] == name:
                        m.update(peer=e["peer"], retrieved_at=e["retrieved_at"])
        m.update(part_id=pid, bytes=len(b), sha256=sha(b).hex())
        return f

    def rng(self, pid):
        out = subprocess.run([FETCH, "range", self.root, self.fetch(pid)], capture_output=True, text=True).stdout
        d = json.loads(out)
        return d["first_key_nibbles"], d["last_key_nibbles"]

    def locate(self, key_nibbles):
        lo, hi = 0, self.num_parts - 1
        while lo <= hi:
            m = (lo + hi) // 2
            a, b = self.rng(m)
            if a is None or key_nibbles < a:
                hi = m - 1
            elif key_nibbles > b:
                lo = m + 1
            else:
                return m
        # key absent: the part whose range would contain it is lo (or lo-1)
        return max(0, min(lo, self.num_parts - 1))

    def whereis(self, node_hash, files):
        r = subprocess.run([FETCH, "whereis", self.root, node_hash] + files, capture_output=True, text=True)
        if r.returncode != 0:
            return None
        d = json.loads(r.stdout)
        return d.get("path_nibbles", d.get("value_of_key_nibbles"))


# ---------------------------------------------------------------- outcome hashing
def borsh_str(s):
    b = s.encode()
    return len(b).to_bytes(4, "little") + b


def partial_status(st):
    (k, v), = st.items()
    if k == "SuccessValue":
        b = base64.b64decode(v)
        return b"\x02" + len(b).to_bytes(4, "little") + b
    if k == "SuccessReceiptId":
        return b"\x03" + b58(v)
    if k == "Failure":
        return b"\x01"
    return b"\x00"


def outcome_leaf(o):
    """merklize leaf of ExecutionOutcomeWithId::to_hashes (transaction.rs, merkle.rs)."""
    out = o["outcome"]
    p = len(out["receipt_ids"]).to_bytes(4, "little") + b"".join(b58(x) for x in out["receipt_ids"])
    p += int(out["gas_burnt"]).to_bytes(8, "little") + int(out["tokens_burnt"]).to_bytes(16, "little")
    p += borsh_str(out["executor_id"]) + partial_status(out["status"])
    hs = [b58(o["id"]), sha(p)] + [sha(l.encode()) for l in out["logs"]]
    return sha(len(hs).to_bytes(4, "little") + b"".join(hs))


def root_from_path(leaf, path):
    h = leaf
    for it in path:
        x = b58(it["hash"])
        h = sha(x + h) if it["direction"] == "Left" else sha(h + x)
    return h


# ---------------------------------------------------------------- build
def next_new_chunk(shard, height):
    """First block after `height` carrying a new chunk for `shard`: its chunk header's
    prev_* fields commit to the results of the chunk applied at `height`."""
    h = height
    while True:
        b = next_blk(h)
        h = b["header"]["height"]
        c = [c for c in b["chunks"] if c["shard_id"] == shard][0]
        if c["height_included"] == h:
            return b, c


def check(anchors, name, ok, meaning, **kw):
    anchors[name] = dict(ok=bool(ok), meaning=meaning, **kw)
    print(f"  [{'ok' if ok else 'NO'}] {name}", file=sys.stderr)


def cmd_build(a):
    shard = a.shard
    status = rpc("status", [])
    head = status["sync_info"]["latest_block_height"]
    sp = sync_point(a.epoch_start or status["sync_info"]["epoch_start_height"])
    root = sp["chunks"][shard]["prev_state_root"]
    anchors = {}

    # ---- receipts: authentic + tx-originated (=> ReceiptEnum::Action, receipt.rs Receipt::from_tx)
    receipts, rinfo, exec_blocks = [], [], set()
    for rid in a.receipt:
        r = rpc("EXPERIMENTAL_receipt", {"receipt_id": rid})
        t = rpc("EXPERIMENTAL_receipt_to_tx", {"receipt_id": rid})
        tx = rpc("EXPERIMENTAL_tx_status", {"tx_hash": t["transaction_hash"], "sender_account_id": t["sender_account_id"], "wait_until": "NONE"})
        ro = [o for o in tx["receipts_outcome"] if o["id"] == rid][0]
        tr = tx["transaction"]
        act = r["receipt"]["Action"]
        from_tx = (
            tx["transaction_outcome"]["outcome"]["receipt_ids"] == [rid]
            and tr["signer_id"] == r["predecessor_id"] == act["signer_id"]
            and tr["receiver_id"] == r["receiver_id"]
            and tr["actions"] == act["actions"]
            and tr["public_key"] == act["signer_public_key"]
            and "refund_to" not in act
        )
        check(anchors, f"receipt_from_transaction:{rid}", from_tx,
              "receipt is the conversion receipt of a Transfer transaction (tx outcome receipt_ids == [id], same signer/receiver/key/actions), hence Receipt::from_tx => ReceiptEnum::Action (in v1 domain); RPC ReceiptView -> Receipt conversion is then exact",
              tx_hash=t["transaction_hash"], tx_signer=tr["signer_id"])
        check(anchors, f"receipt_succeeded_onchain:{rid}", ro["outcome"]["status"] == {"SuccessValue": ""},
              "on-chain execution outcome status SuccessValue('')", status=ro["outcome"]["status"])
        receipts.append(r)
        exec_blocks.add(ro["block_hash"])
        rinfo.append({"receipt_id": rid, "tx_hash": t["transaction_hash"], "tx_signer": t["sender_account_id"],
                      "receiver_id": r["receiver_id"], "deposit": act["actions"][0]["Transfer"]["deposit"],
                      "gas_price": act["gas_price"], "onchain_outcome": ro})
    assert len(exec_blocks) == 1, "batch receipts must be executed in the same block"
    xb = rpc("block", {"block_id": exec_blocks.pop()})
    X = xb["header"]["height"]
    xc = [c for c in xb["chunks"] if c["shard_id"] == shard][0]
    assert xc["height_included"] == X, "execution chunk must be new at the execution block"
    pv = rpc("EXPERIMENTAL_protocol_config", {"block_id": X})
    check(anchors, "protocol_version_86", pv["protocol_version"] == 86 and pv["chain_id"] == "mainnet",
          "EXPERIMENTAL_protocol_config at the execution block: protocol_version 86, chain_id mainnet",
          protocol_version=pv["protocol_version"], chain_id=pv["chain_id"])
    exact = xc["prev_state_root"] == root
    print(f"exec block {X}; sync_prev {sp['sync_prev_height']}; exact={exact}", file=sys.stderr)

    # ---- trie nodes over P2P
    P = Parts(sp["sync_hash"], shard, head)
    hdr = P.header()
    check(anchors, "state_header_root_matches_chain", hdr["state_root_node_hash"] == root == hdr["chunk_prev_state_root"],
          "sha256 of the peer-served state root node == chunk header prev_state_root of sync_prev.chunks[shard] (from RPC) == pre_state_root",
          state_root=root, header_chunk_hash=hdr["chunk_hash"], rpc_chunk_hash=sp["chunks"][shard]["chunk_hash"])
    pids = set()
    for r in receipts:
        pids.add(P.locate("00" + r["receiver_id"].encode().hex()))
    ctx = {"protocol_version": 86, "chain_id": "mainnet", "shard_id": shard, "block_height": X,
           "block_gas_price": xb["header"]["gas_price"], "gas_limit": xc["gas_limit"],
           "pre_state_root": root, "receipts": receipts}
    os.makedirs(PARTS_DIR, exist_ok=True)
    ctxf = os.path.join(PARTS_DIR, f"ctx_{a.name}.json")
    json.dump(ctx, open(ctxf, "w"), indent=1)
    out = os.path.join(a.out, "cases", a.name)
    for _ in range(12):
        files = [P.fetch(p) for p in sorted(pids)]
        r = subprocess.run([FETCH, "build", "--ctx", ctxf, "--parts", ",".join(files), "--out", out],
                           capture_output=True, text=True)
        m = re.search(r"MissingTrieValue \{ context: \w+, hash: (\w+) \}", r.stderr)
        if not m:
            break
        path = P.whereis(m.group(1), files)
        assert path is not None, f"cannot place missing node {m.group(1)}"
        pid = P.locate(path)
        # part boundaries are by memory usage, so a subtree can start in the
        # neighbour of the part our key-range bisection lands on: widen.
        for d in (0, 1, -1, 2, -2, 3, -3):
            if 0 <= pid + d < P.num_parts and pid + d not in pids:
                pid += d
                break
        else:
            sys.exit(f"cannot find the part holding node {m.group(1)} (path {path})")
        print(f"  apply needs node at path {path[:24]}.. -> part {pid}", file=sys.stderr)
        pids.add(pid)
    if r.returncode != 0:
        sys.exit(f"build failed: {r.stderr[-2000:]}")
    claim = json.loads(r.stdout.strip().splitlines()[-1])
    json.dump(ctx, open(os.path.join(out, "context.json"), "w"), indent=1)  # build input (RPC ReceiptViews + block fields)
    diag = json.load(open(os.path.join(out, "diagnostics.json")))

    # ---- anchors against the chain
    check(anchors, "claim_pre_state_root_is_onchain_root", claim["pre_state_root"] == b58(root).hex(),
          "claim.pre_state_root == sync_prev.chunks[shard].prev_state_root (an on-chain chunk-header field)")
    check(anchors, "claim_pre_state_root_is_execution_chunk_prev_state_root", exact,
          "claim.pre_state_root == prev_state_root of the chunk that actually executed the receipts",
          execution_chunk_prev_state_root=xc["prev_state_root"])
    nb, nc = next_new_chunk(shard, X)
    leaves = [outcome_leaf(i["onchain_outcome"]) for i in rinfo]
    for i, lf in zip(rinfo, leaves):
        check(anchors, f"onchain_outcome_proof:{i['receipt_id']}",
              root_from_path(lf, i["onchain_outcome"]["proof"]) == b58(nc["outcome_root"]),
              "on-chain outcome (RPC) + its merkle path hash to the execution chunk's outcome root, committed as prev_outcome_root in the next chunk header",
              leaf=lf.hex())
    if len(leaves) == 1:
        check(anchors, "claim_outcome_root_equals_onchain_outcome_leaf", claim["outcome_root"] == leaves[0].hex(),
              "batch of 1: claim.outcome_root (oracle) == the on-chain outcome leaf of that receipt (state-independent outputs: refund id, gas, tokens, status)")
    pure = (int(nc["gas_used"]) == claim["gas_burnt_total"] and int(nc["balance_burnt"]) == int(claim["tokens_burnt_total"]))
    check(anchors, "execution_chunk_contains_exactly_the_batch", pure,
          "next chunk header prev_gas_used == claim.gas_burnt_total and prev_balance_burnt == claim.tokens_burnt_total (the execution chunk burnt exactly the batch's gas)",
          onchain_prev_gas_used=nc["gas_used"], onchain_prev_balance_burnt=nc["balance_burnt"])
    check(anchors, "claim_outcome_root_equals_onchain_prev_outcome_root", claim["outcome_root"] == b58(nc["outcome_root"]).hex(),
          "claim.outcome_root == next chunk header prev_outcome_root (only possible when the chunk executed exactly the batch)",
          onchain_prev_outcome_root=nc["outcome_root"])
    cls = ("historical-exact-chunk" if pure else "historical-exact-subbatch") if exact else "historical-rebased-prestate"
    nchunk = rpc("chunk", {"chunk_id": nc["chunk_hash"]})
    out_ids = [x["receipt_id"] for x in nchunk["receipts"]]
    refund_ids = [x for i in rinfo for x in i["onchain_outcome"]["outcome"]["receipt_ids"]]
    exp_refunds = [(i["tx_signer"], str((int(i["gas_price"]) - min(int(i["gas_price"]), int(xb["header"]["gas_price"]))) * G)) for i in rinfo
                   if int(i["gas_price"]) > int(xb["header"]["gas_price"])]
    got = [(x["receiver_id"], x["receipt"]["Action"]["actions"][0]["Transfer"]["deposit"]) for x in nchunk["receipts"] if x["receipt_id"] in refund_ids]
    check(anchors, "refunds_match_onchain_outgoing_receipts", got == exp_refunds and claim["refund_count"] == len(exp_refunds),
          "the gas refunds the claim commits to (receiver, amount, count) are the execution chunk's on-chain outgoing receipts with the on-chain refund ids",
          onchain_outgoing_receipt_ids=out_ids, refund_ids=refund_ids)
    rec_ok = True
    rec = []
    pre_vals = {bytes.fromhex(x["key"])[1:].decode(): x["value"] for x in diag["receiver_pre_values"]}
    for i in rinfo:
        acc = i["receiver_id"]
        v = bytes.fromhex(pre_vals[acc])
        amt = int.from_bytes(v[:16], "little")
        before = rpc("query", {"request_type": "view_account", "account_id": acc, "block_id": xb["header"]["prev_hash"]})
        after = rpc("query", {"request_type": "view_account", "account_id": acc, "block_id": X})
        same = int(before["amount"]) == amt and int(before["locked"]) == int.from_bytes(v[16:32], "little") and before["storage_usage"] == int.from_bytes(v[64:72], "little")
        rec_ok &= same
        rec.append({"account": acc, "witness_amount": str(amt), "onchain_amount_before_execution": before["amount"],
                    "onchain_amount_after_execution": after["amount"]})
    check(anchors, "receiver_records_identical_to_execution_prestate", rec_ok,
          "each receiver's Account record under pre_state_root (from the authentic witness) equals view_account at the execution block's prev block, so the slice computes the same per-receipt account write the chain made",
          records=rec)

    not_anchored = ["slice_post_root (projection root, never on chain; spec §5)"]
    if not exact:
        not_anchored.append("pre_state_root is an on-chain root of the same shard but from an EARLIER chunk "
                             f"(height {sp['sync_prev_height']}) than the one that executed the receipts (height {X}); "
                             "the chain applied the receipts to a different state root, so the claim is a replay of authentic "
                             "receipts against an authentic earlier state, not the chain's own transition")
    prov = {
        "schema": "near-arena-historical-provenance-v1",
        "fixture_class": cls,
        "label": "AUTHENTIC mainnet data (trie nodes from mainnet state sync, receipts/blocks from RPC); see anchors and not_anchored",
        "chain_id": "mainnet",
        "statement_id": "near/pv86/receipt-transfer-batch/v0",
        "nearcore": {"tag": "2.13.4", "commit": "44f7ae6cd7ef08bab604e20a473bf77e35d4c993",
                     "rpc_node_version": status["version"]},
        "retrieval": {"time_utc": now(), "rpc_endpoint": RPC, "peer_list_endpoint": PEER_RPC,
                      "p2p_peers_used": P.peers, "tool": "oracle/historical (near-arena-historical, harvest.py)"},
        "pre_state": {"state_root": root, "state_root_hex": b58(root).hex(), "shard_id": shard,
                      "epoch_id": sp["epoch_id"], "epoch_start_height": sp["epoch_start_height"],
                      "sync_hash": sp["sync_hash"], "sync_height": sp["sync_height"],
                      "sync_prev_block_hash": sp["sync_prev_hash"], "sync_prev_block_height": sp["sync_prev_height"],
                      "chunk_hash": sp["chunks"][shard]["chunk_hash"],
                      "meaning": "prev_state_root of sync_prev.chunks[shard]: the shard state after the previous new chunk",
                      "state_header": hdr,
                      "state_parts": [P.meta[p] for p in sorted(pids)],
                      "parts_not_committed": "the raw parts (7-20 MB each) are not committed; apply_witness.bin holds every node Runtime::apply read, each hash-linked to state_root"},
        "execution": {"block_height": X, "block_hash": xb["header"]["hash"], "block_gas_price": xb["header"]["gas_price"],
                      "chunk_hash": xc["chunk_hash"], "chunk_prev_state_root": xc["prev_state_root"], "gas_limit": xc["gas_limit"],
                      "next_chunk": {"block_height": nb["header"]["height"], "block_hash": nb["header"]["hash"],
                                     "chunk_hash": nc["chunk_hash"], "prev_outcome_root": nc["outcome_root"],
                                     "prev_gas_used": nc["gas_used"], "prev_balance_burnt": nc["balance_burnt"],
                                     "prev_state_root": nc["prev_state_root"]}},
        "receipts": [{k: v for k, v in i.items() if k != "onchain_outcome"} | {"onchain_outcome_leaf": l.hex()} for i, l in zip(rinfo, leaves)],
        "claim": claim,
        "anchors": anchors,
        "not_anchored": not_anchored,
        "excluded_by_spec": "block finality, receipt inclusion proofs, signatures: spec/claim-v1.md §6 (external trust)",
    }
    json.dump(prov, open(os.path.join(out, "provenance.json"), "w"), indent=1)
    open(os.path.join(out, "provenance.json"), "a").write("\n")
    bad = [k for k, v in anchors.items() if not v["ok"]]
    print(json.dumps({"case": out, "class": cls, "anchors_failed": bad}))


NEARDATA = "https://mainnet.neardata.xyz/v0/block/"
HEX64 = re.compile(r"^[0-9a-f]{64}$")


def neardata(h):
    for i in range(20):
        time.sleep(0.25)
        try:
            return json.loads(urllib.request.urlopen(NEARDATA + str(h), timeout=60).read())
        except Exception as e:
            time.sleep(15 if "429" in str(e) else 2 + i)
    raise RuntimeError(f"neardata {h}")


def named(a):
    return not (HEX64.match(a) or re.match(r"^0[xs][0-9a-f]{40}$", a))


def candidates_in_block(h, roots=None):
    d = neardata(h)
    out = []
    if not d:
        return out
    for s in d["shards"]:
        c = s["chunk"]
        if not c or c["header"]["height_included"] != h:
            continue
        outs = s["receipt_execution_outcomes"]
        for o in outs:
            r = o["receipt"]
            a = r["receipt"].get("Action")
            if not a or r["predecessor_id"] == "system" or a["signer_id"] != r["predecessor_id"]:
                continue
            if len(a["actions"]) != 1 or not isinstance(a["actions"][0], dict) or "Transfer" not in a["actions"][0]:
                continue
            if a["input_data_ids"] or a["output_data_receivers"] or not named(r["receiver_id"]):
                continue
            if o["execution_outcome"]["outcome"]["status"] != {"SuccessValue": ""}:
                continue
            out.append({"height": h, "shard": s["shard_id"], "receipt_id": r["receipt_id"],
                        "receiver": r["receiver_id"], "chunk_receipts": len(outs), "chunk_txs": len(c["transactions"]),
                        "pure_chunk": len(outs) == 1 and not c["transactions"],
                        "exact": roots is not None and c["header"]["prev_state_root"] == roots.get(s["shard_id"])})
    return out


def cmd_candidates(a):
    st = rpc("status", [])
    sp = sync_point(a.epoch_start or st["sync_info"]["epoch_start_height"])
    roots = {k: v["prev_state_root"] for k, v in sp["chunks"].items()}
    hs = range(a.frm, a.to) if a.frm else [sp["sync_prev_height"]]
    print(json.dumps({"sync_hash": sp["sync_hash"], "sync_prev_height": sp["sync_prev_height"]}))
    for h in hs:
        for c in candidates_in_block(h, roots):
            print(json.dumps(c))


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("sync-point")
    s.add_argument("--epoch-start", type=int)
    c = sub.add_parser("candidates")
    c.add_argument("--epoch-start", type=int)
    c.add_argument("--from", dest="frm", type=int)
    c.add_argument("--to", type=int)
    b = sub.add_parser("build")
    b.add_argument("--shard", type=int, required=True)
    b.add_argument("--receipt", action="append", required=True)
    b.add_argument("--name", required=True)
    b.add_argument("--epoch-start", type=int)
    b.add_argument("--out", default=os.path.join(ORACLE_DIR, "fixtures/historical"))
    a = ap.parse_args()
    if a.cmd == "sync-point":
        st = rpc("status", [])
        print(json.dumps(sync_point(a.epoch_start or st["sync_info"]["epoch_start_height"]), indent=1))
    elif a.cmd == "candidates":
        cmd_candidates(a)
    else:
        cmd_build(a)


if __name__ == "__main__":
    main()
