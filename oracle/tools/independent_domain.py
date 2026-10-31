#!/usr/bin/env python3
"""Independent assertion of checker domain exclusions the corpus oracle does not label.

The corpus oracles (`d3_violations` in each case's meta.json) predate several restrictions of the
signed tier and some successor exclusions: the D1/D2 corpora's `ood` families carry their
violations under `d1_violations` / `d2_violations` and an empty `d3_violations`, and the
pipeline-race fixtures label their global-contract shape `w.shape` only. A checker exclusion on
such a case cannot be licensed by the oracle's labels. This module licenses it instead by
decoding `claim.bin` / `witness.bin` in Python and computing the predicate the exclusion's reason
names. Nothing here reads the Lean checker or its output: the decoders are the independent Python
reference's (`spec_check_v3.py`, `v3lib/near2.py`, `v3lib/prim.py`, written from the nearcore
sources), and the predicates are written from the claim / witness formats (`spec/claim-v3.md`,
`spec/near-chunk-validation-d2.md` and `-d3.md`).

An exclusion is licensed only when (a) its reason text is one this module knows, (b) the tier under
test still excludes that shape (`TIER_EXCLUSIONS`), and (c) the decoded predicate holds. An unknown
reason, an undecodable case or a false predicate is *not* licensed; the harness then keeps the row
a failure.

    independent_domain.py CASE_DIR REASON [--tier signed]   print the decision as JSON
"""
import contextlib
import hashlib
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import spec_check_v3 as s3  # noqa: E402
from v3lib.prim import R, ZERO32, PartialTrie  # noqa: E402
from v3lib import near2 as N  # noqa: E402

FORMAT_WITNESS = b"near-arena-witness-v3"
MAX_STATE_WITNESS_IN_DOMAIN = 8 * 1024 * 1024      # the 8 MiB state-witness bound (`w.size`)
MAX_SEGMENT_BLOCKS = 32                             # `c.segment`

# Reason texts (the checker's `out of domain (CODE): DETAIL` line) and the predicate each needs.
# Matching is on the whole text, so a reason with a different detail (e.g. the resharding walk's
# `out of domain (c.not_genesis): resharding walk reaches the genesis block`) is unknown and not
# licensed.
R_NOT_GENESIS = "out of domain (c.not_genesis)"
R_SEGMENT = "out of domain (c.segment)"
R_WSIZE_8MIB = "out of domain (w.size): witness larger than 8 MiB"
R_NON_ED25519_TX = "out of domain (w.shape): non-ED25519 transaction key"
R_MLDSA_KEY = "out of domain (w.shape): ML-DSA-65 public key"
R_GCD = "out of domain (w.shape): GlobalContractDistribution receipt"
R_CACHE_SERVED = ("out of domain (e.wasm-α): pre-state contract served only by the in-chunk "
                  "compiled-contract cache")
R_PREP_RACE = ("out of domain (e.code_prep_race): contract preparation pipelined before the "
               "in-chunk deploy that serves its code")

PREDICATES = {
    R_NOT_GENESIS: "b2_is_genesis",
    R_SEGMENT: "segment_longer_than_32",
    R_WSIZE_8MIB: "state_witness_larger_than_8MiB",
    R_NON_ED25519_TX: "transaction_key_not_ed25519",
    R_MLDSA_KEY: "mldsa65_public_key_in_tx_or_receipt",
    R_GCD: "global_contract_distribution_receipt",
    R_CACHE_SERVED: "prestate_code_absent_but_deployed_in_chunk",
    R_PREP_RACE: "call_served_by_earlier_in_chunk_deploy",
}

# Which reasons each tier still reports as exclusions, so a licence is never granted for a shape the
# tier under test decides. `signed` is `D3.checkD3` (`spec/lean/v3/NearSpecV3/D3/Signed.lean`): the
# one-layout core plus the recorder hand-over; it keeps `c.not_genesis` (`checkD2CoreWith` still
# checks `!B2.isGenesis`), `c.segment` and the 8 MiB bound (the hand-over driver's lift flags are
# false), the `w.shape` ML-DSA / global-contract shapes (no global actions, `D2/Types.lean`), the
# non-ED25519 transaction key (`D2/TxD2.lean`) and the cold-cache code rule (`D3/FunctionCall.lean`).
# The successor tiers (`tools/d3/replay_successor.py`) are licensed here only for the preparation
# race, the named exclusion every whole-state tier shares (`Successor/CodeResolution.lean`); every
# other successor exclusion stays licensed by the oracle's own labels.
TIER_EXCLUSIONS = {
    "signed": frozenset({R_NOT_GENESIS, R_SEGMENT, R_WSIZE_8MIB, R_NON_ED25519_TX, R_MLDSA_KEY,
                         R_GCD, R_CACHE_SERVED}),
    "successor": frozenset({R_PREP_RACE}),
}


def match_reason(reason):
    """The known reason text `reason` is exactly, or None (no prefix or substring matching)."""
    return reason if reason in PREDICATES else None


@contextlib.contextmanager
def lenient():
    """Let near2 walk ML-DSA keys and global-contract shapes instead of raising on them; the
    predicates below inspect the decoded tags themselves."""
    old = N.LENIENT
    N.LENIENT = True
    try:
        yield
    finally:
        N.LENIENT = old


def sha(b):
    return hashlib.sha256(b).digest()


class Case:
    """The decoded parts of a case that the predicates read. Decoding is lazy and each part keeps
    its own error, so a predicate that does not need the witness still works on an odd witness."""

    def __init__(self, claim_bytes, witness_bytes):
        self.claim_bytes = claim_bytes
        self.witness_bytes = witness_bytes
        self._claim = self._file = self._sw = self._walk = None

    @classmethod
    def load(cls, case_dir):
        with open(os.path.join(case_dir, "claim.bin"), "rb") as f:
            c = f.read()
        with open(os.path.join(case_dir, "witness.bin"), "rb") as f:
            w = f.read()
        return cls(c, w)

    def claim(self):
        if self._claim is None:
            self._claim = s3.decode_claim(self.claim_bytes)
        return self._claim

    def witness_file(self):
        """(state_witness_bytes, codes) of the clear `near-arena-witness-v3` format."""
        if self._file is None:
            r = R(self.witness_bytes)
            if r.bytes() != FORMAT_WITNESS:
                raise ValueError("witness format id is not near-arena-witness-v3")
            sw = r.bytes()
            codes = r.vec(r.bytes)
            r.end()
            self._file = (sw, codes)
        return self._file

    def state_witness(self):
        """Structural decode of ChunkStateWitness (the D2 reference's layout, no domain checks)."""
        if self._sw is None:
            sw, _ = self.witness_file()
            with lenient():
                r = R(sw)
                if r.u8() != 1:
                    raise ValueError("ChunkStateWitness tag")
                w = dict(epoch_id=r.hash())
                if r.u8() != 2:
                    raise ValueError("ShardChunkHeader version is not V3")
                w['inner'] = s3.read_inner(r)
                w['height_included'] = r.u64()
                s3.read_signature(r)
                w['main'] = s3.read_transition(r)
                incoming = []
                for _ in range(r.u32()):
                    r.hash()
                    incoming += r.vec(lambda: N.read_receipt(r))
                    r.u64(), r.u64()
                    r.vec(lambda: (r.hash(), r.u8()))
                w['incoming'] = incoming
                w['applied_receipts_hash'] = r.hash()
                w['txs'] = r.vec(lambda: N.read_tx(r))
                w['implicit'] = r.vec(lambda: s3.read_transition(r))
                w['new_txs'] = r.vec(lambda: N.read_tx(r))
                r.end()
            self._sw = w
        return self._sw

    def walk(self):
        """(blocks, idx, b2i): the backward walk to the last new chunk of the claimed shard."""
        if self._walk is None:
            c = self.claim()
            H = s3.decode_inner_bytes(c['chunk_inner'])
            ep = {e['epoch_id']: e for e in c['epochs']}[c['epoch_id']]
            L = s3.decode_layout(ep['layout_raw'])
            idx = L.index[H.shard_id]
            b2i = None
            for i, b in enumerate(c['blocks']):
                height = s3.decode_inner_lite(b.lite_raw)['height']
                if b.slots_raw[idx][1] == height:
                    b2i = i
                    break
            if b2i is None:
                raise ValueError("segment has no new chunk for the claimed shard")
            self._walk = (c['blocks'], idx, b2i)
        return self._walk

    # ---- derived views ------------------------------------------------------------------------
    def messages(self):
        """Every decoded transaction and receipt with where it came from, in chunk order:
        the chunk's transactions, then the incoming receipts, then the new transactions."""
        w = self.state_witness()
        out = [("tx", i, t) for i, t in enumerate(w['txs'])]
        out += [("incoming", i, x) for i, x in enumerate(w['incoming'])]
        out += [("new_tx", i, t) for i, t in enumerate(w['new_txs'])]
        return out

    def stored_receipts(self):
        """Receipts stored in the recorded pre-state (delayed / buffered / postponed queues). A
        value that does not decode as a stored receipt is skipped."""
        out = []
        with lenient():
            for v in self.state_witness()['main']['base_state']:
                try:
                    x, _, _ = N.decode_stored_receipt(v)
                except Exception:  # noqa: BLE001 - most trie values are not receipts
                    continue
                out.append(x)
        return out

    def prestate_account(self, account):
        """The pre-state account record of `account` (the main transition's recorded trie at the
        last new chunk's prev_state_root), or None when absent or not recorded."""
        blocks, idx, b2i = self.walk()
        raw, _ = blocks[b2i].slots_raw[idx]
        root = s3.decode_inner_bytes(raw).prev_state_root
        trie = PartialTrie(self.state_witness()['main']['base_state'], root)
        try:
            v = trie.get(bytes([0]) + account)
        except Exception:  # noqa: BLE001 - an unrecorded path is "unknown", not a licence
            return None
        return None if v is None else N.decode_account(v)

    def code_store_hashes(self):
        """Hashes of every code the cold validator can read from the witness: the code blobs and
        the recorded values (`base_state ++ codes`, partial_witness_tracker.rs:693-696)."""
        sw, codes = self.witness_file()
        return {sha(v) for v in self.state_witness()['main']['base_state']} | {sha(c) for c in codes}


def _actions(msg):
    """Top-level and delegated actions of a decoded transaction or action receipt."""
    acts = list(getattr(msg, 'actions', None) or [])
    out = []
    for a in acts:
        out.append(a)
        if a.tag in (N.A_DELEGATE, N.A_DELEGATE_V2):
            out += list(a.f.get('actions') or [])
    return out


def _pks(msg):
    """Every public key a transaction or receipt carries (signer key and action keys)."""
    pks = []
    if getattr(msg, 'pk', None) is not None:
        pks.append(msg.pk)
    for a in getattr(msg, 'actions', None) or []:
        if 'pk' in a.f:
            pks.append(a.f['pk'])
        if a.tag in (N.A_DELEGATE, N.A_DELEGATE_V2):
            for b in a.f.get('actions') or []:
                if 'pk' in b.f:
                    pks.append(b.f['pk'])
    return pks


# ---- predicates: (holds, detail) ----------------------------------------------------------------
def b2_is_genesis(case):
    blocks, _, b2i = case.walk()
    return blocks[b2i].prev_hash == ZERO32, f"blocks[{b2i}] is the last new chunk's block"


def segment_longer_than_32(case):
    n = len(case.claim()['blocks'])
    return n > MAX_SEGMENT_BLOCKS, f"{n} blocks"


def state_witness_larger_than_8MiB(case):
    sw, _ = case.witness_file()
    return len(sw) > MAX_STATE_WITNESS_IN_DOMAIN, f"state witness {len(sw)} B"


def transaction_key_not_ed25519(case):
    w = case.state_witness()
    for where in ("txs", "new_txs"):
        for i, t in enumerate(w[where]):
            if t.pk[0] != 0:
                return True, f"{where}[{i}] signer key tag {t.pk[0]}"
    return False, "every transaction key is ED25519"


def mldsa65_public_key_in_tx_or_receipt(case):
    for kind, i, m in case.messages():
        for pk in _pks(m):
            if pk[0] == 2:
                return True, f"{kind}[{i}] carries an ML-DSA-65 key"
    for i, x in enumerate(case.stored_receipts()):
        for pk in _pks(x):
            if pk[0] == 2:
                return True, f"stored receipt {i} carries an ML-DSA-65 key"
    return False, "no ML-DSA-65 key in a transaction or receipt"


def global_contract_distribution_receipt(case):
    for i, x in enumerate(case.state_witness()['incoming']):
        if x.kind == N.K_GCD:
            return True, f"incoming[{i}] is a GlobalContractDistribution receipt"
    for i, x in enumerate(case.stored_receipts()):
        if x.kind == N.K_GCD:
            return True, f"stored receipt {i} is a GlobalContractDistribution receipt"
    return False, "no GlobalContractDistribution receipt"


def _calls_and_deploys(case):
    """FunctionCall and DeployContract actions this chunk executes, with their position
    (message index, action index) in execution order. A transaction is executed here only as a
    local receipt (signer == receiver, runtime/runtime/src/lib.rs `process_transactions`); an
    incoming receipt is executed here. Delegated inner actions run in a later receipt and new
    transactions are not applied, so neither is counted."""
    calls, deploys = [], []
    for pos, (kind, i, m) in enumerate(case.messages()):
        if kind == "new_tx" or (kind == "tx" and m.signer != m.recv):
            continue
        for k, a in enumerate(getattr(m, 'actions', None) or []):
            if a.tag == N.A_FC:
                calls.append(((pos, k), kind, i, m.recv))
            elif a.tag == N.A_DEPLOY:
                deploys.append(((pos, k), kind, i, m.recv, sha(a.f['code'])))
    return calls, deploys


def prestate_code_absent_but_deployed_in_chunk(case):
    """A FunctionCall's receiver has a pre-state contract whose code no witness blob or recorded
    value holds, while a DeployContract executed earlier in this chunk carries exactly that code
    (the cold-cache rule's in-chunk precompile case, spec/near-chunk-validation-d3.md §2.2)."""
    calls, deploys = _calls_and_deploys(case)
    store = case.code_store_hashes()
    for pos, kind, i, recv in calls:
        acct = case.prestate_account(recv)
        if acct is None or acct.contract[0] != 'local':
            continue
        h = acct.contract[1]
        own = [d for d in deploys if d[0] < pos and d[3] == recv]
        if own and own[-1][4] != h:
            continue            # the receiver now runs other code, served by the deploy tracker
        if h not in store and any(d[0] < pos and d[4] == h for d in deploys):
            return True, f"{kind}[{i}] calls {recv.decode(errors='replace')}: pre-state code absent, deployed in chunk"
    return False, "no pre-state contract call whose code only an in-chunk deploy holds"


def call_served_by_earlier_in_chunk_deploy(case):
    """A FunctionCall needs code with hash h that no witness blob or recorded value holds, and a
    DeployContract with code hash h runs in an earlier transaction or receipt of the same chunk:
    the call's code exists only through that deploy (the deploy tracker for the receiver's own
    deploy, the deploy's synchronous precompile into the compiled-contract cache for any account,
    runtime/runtime/src/actions.rs:297-339). h is the code an earlier in-chunk deploy set on the
    receiver, else the receiver's pre-state contract. This is the structural precondition of
    nearcore's preparation race (runtime/runtime/src/pipelining.rs): it asserts the cause the reason
    names (code served by an in-chunk deploy), not that nearcore's verdict races."""
    calls, deploys = _calls_and_deploys(case)
    store = case.code_store_hashes()
    for pos, kind, i, recv in calls:
        earlier = [d for d in deploys if d[0][0] < pos[0]]     # an earlier transaction or receipt
        own = [d for d in earlier if d[3] == recv]
        if own:
            h = own[-1][4]
        else:
            acct = case.prestate_account(recv)
            if acct is None or acct.contract[0] != 'local':
                continue
            h = acct.contract[1]
        if h in store:
            continue
        for dpos, dkind, di, drecv, dh in earlier:
            if dh == h:
                return True, (f"{kind}[{i}] calls {recv.decode(errors='replace')}, code served only by "
                              f"the deploy in {dkind}[{di}]")
    return False, "no call served only by an earlier in-chunk deploy"


PREDICATE_FNS = {f.__name__: f for f in (
    b2_is_genesis, segment_longer_than_32, state_witness_larger_than_8MiB,
    transaction_key_not_ed25519, mldsa65_public_key_in_tx_or_receipt,
    global_contract_distribution_receipt, prestate_code_absent_but_deployed_in_chunk,
    call_served_by_earlier_in_chunk_deploy)}


def assert_exclusion(case_dir, reason, tier, case=None):
    """Decide whether `reason` is an independently asserted exclusion of `case_dir` on `tier`.

    Returns a dict {licensed, predicate, detail}. Never raises on a case: a decode error is an
    unlicensed exclusion with the error as detail."""
    known = match_reason(reason)
    if known is None:
        return {"licensed": False, "predicate": None, "detail": "reason not known to the classifier"}
    if known not in TIER_EXCLUSIONS.get(tier, frozenset()):
        return {"licensed": False, "predicate": PREDICATES[known],
                "detail": f"tier {tier!r} does not exclude this shape"}
    name = PREDICATES[known]
    try:
        case = case or Case.load(case_dir)
        holds, detail = PREDICATE_FNS[name](case)
    except Exception as e:  # noqa: BLE001 - undecodable means not asserted
        return {"licensed": False, "predicate": name, "detail": f"{type(e).__name__}: {e}"}
    return {"licensed": bool(holds), "predicate": name, "detail": detail}


def classifier(tier):
    """The callable the difftest harness takes: (case_dir, reason) -> decision dict."""
    def f(case_dir, reason):
        return assert_exclusion(case_dir, reason, tier)
    return f


def main():
    args = [a for a in sys.argv[1:]]
    tier = "signed"
    if "--tier" in args:
        k = args.index("--tier")
        tier = args[k + 1]
        del args[k:k + 2]
    if len(args) != 2:
        sys.exit(__doc__)
    print(json.dumps(assert_exclusion(args[0], args[1], tier), sort_keys=True))


if __name__ == "__main__":
    main()
