#!/usr/bin/env python3
"""Independent Python reference checker for near/pv86/chunk-validation/v0, domain D2
(D1 + every non-WASM action, multi-action transactions and receipts, gas keys, meta
transactions, failures with rollback and refunds, data / postponed receipts, the delayed
queue, outgoing buffers with receipt groups and bandwidth requests, yield timeouts, epoch
boundaries with validator account updates).

Written from the nearcore 2.13.4 Rust sources (runtime/runtime/src/{lib.rs, actions.rs,
access_keys.rs, verifier.rs, action_validation.rs, config.rs, congestion_control.rs},
core/store/src/{utils/mod.rs, trie/*}, chain/chain/src/{runtime/mod.rs,
stateless_validation/chunk_validation.rs, validate.rs}), the claim format
(spec/claim-v3.md) and the D2 domain definition. It does NOT use the Lean formalization.
The claim / chain-context decoding, receipt proofs, shuffle, scheduler and Reed-Solomon are
imported from spec_check_v3.py (D0); Ed25519 from v3lib/ed25519.py (D1); the trie operations
(lookups by reference, prefix iteration, batched insert/delete) from v3lib/trie2.py; the
nearcore types from v3lib/near2.py.

Usage:
  spec_check_v3_d2.py CASE_DIR...      one JSON line per case:
                                       {"case", "verdict": accept|reject|out_of_domain, "reason"}
"""
import hashlib
import json
import os
import struct
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import spec_check_v3 as s3  # noqa: E402
from v3lib.prim import (  # noqa: E402
    R, Reject, OOD, DecodeError, sha, u8, u16, u32, u64, u128, bstr, U64_MAX, U128_MAX, ZERO32,
    account_type, merklize, merkle_root_of_hashes, compute_root_from_path, ChaCha20Rng,
    encoded_merkle_root, outgoing_gas_limit, valid_account_id)
from v3lib import ed25519, sched  # noqa: E402
from v3lib.trie2 import Trie2  # noqa: E402
from v3lib import near2 as N  # noqa: E402
from v3lib.near2 import (  # noqa: E402
    A_CREATE, A_DEPLOY, A_FC, A_TRANSFER, A_STAKE, A_ADDKEY, A_DELKEY, A_DELACC, A_DELEGATE,
    A_TO_GK, A_FROM_GK, A_DELEGATE_V2, K_ACTION, K_DATA, K_YIELD, K_RESUME, K_ACTION_V2, K_YIELD_V2)

FORMAT_WITNESS = b"near-arena-witness-v3"
MAX_WITNESS = 64 * 1024 * 1024
D_MAX_WITNESS = 8 * 1024 * 1024
D_MAX_BASE_STATE = 3_000_000

# ---------------------------------------------------------------------------------------------
# PV 86 runtime parameters (`near-arena-oracle-v3-d1 params --d2`, i.e. nearcore's own
# RuntimeConfigStore::new(None).get_config(86)); (gas, compute) per fee component
# ---------------------------------------------------------------------------------------------
FEES = {
    'add_full_access_key': ((101765125000, 101765125000), (101765125000, 101765125000), (101765125000, 101765125000)),
    'add_function_call_key_base': ((102217625000, 102217625000), (102217625000, 102217625000), (102217625000, 102217625000)),
    'add_function_call_key_byte': ((1925331, 1925331), (47683715, 47683715), (1925331, 1925331)),
    'create_account': ((500000000000, 500000000000), (500000000000, 500000000000), (7200000000000, 7200000000000)),
    'delegate': ((200000000000, 200000000000), (200000000000, 200000000000), (200000000000, 200000000000)),
    'delete_account': ((147489000000, 147489000000), (147489000000, 147489000000), (147489000000, 147489000000)),
    'delete_key': ((94946625000, 94946625000), (94946625000, 94946625000), (94946625000, 94946625000)),
    'deploy_contract_base': ((184765750000, 184765750000), (184765750000, 184765750000), (184765750000, 20000000000000)),
    'deploy_contract_byte': ((6812999, 6812999), (47683715, 47683715), (64572944, 250000000)),
    'function_call_base': ((200000000000, 200000000000), (200000000000, 200000000000), (780000000000, 780000000000)),
    'function_call_byte': ((2235934, 2235934), (47683715, 47683715), (2235934, 2235934)),
    'gas_key_byte': ((59357464, 59357464), (59357464, 59357464), (101435400, 101435400)),
    'gas_key_nonce_write_base': ((0, 0), (0, 0), (64196736000, 64196736000)),
    'gas_key_transfer_base': ((115123062500, 115123062500), (115123062500, 115123062500), (235676644250, 235676644250)),
    'new_action_receipt': ((108059500000, 108059500000), (108059500000, 108059500000), (108059500000, 108059500000)),
    'stake': ((141715687500, 141715687500), (141715687500, 141715687500), (102217625000, 102217625000)),
    'transfer': ((115123062500, 115123062500), (115123062500, 115123062500), (115123062500, 115123062500)),
}
SIG_VERIFICATION = {0: (0, 0), 1: (0, 0), 2: (100000000000, 100000000000)}
EXT_REMOVE_BASE_C, EXT_REMOVE_KEY_BYTE_C, EXT_REMOVE_VALUE_BYTE_C = 200000000000, 38220384, 11531556
NUM_BYTES_ACCOUNT = 100
NUM_EXTRA_BYTES_RECORD = 40
STORAGE_AMOUNT_PER_BYTE = 10 ** 19
ZERO_BALANCE_ACCOUNT_STORAGE_LIMIT = 770
MIN_GAS_PURCHASE_PRICE = 10 ** 9
ACCOUNT_CREATION_CHARGE = 7 * 10 ** 21
MIN_TOP_LEVEL_LEN = 65
REGISTRAR = b"registrar"
MAX_ACTIONS_PER_RECEIPT = 100
MAX_TOTAL_PREPAID_GAS = 10 ** 15
MAX_NUMBER_BYTES_METHOD_NAMES = 2000
MAX_LENGTH_METHOD_NAME = 256
MAX_ARGUMENTS_LENGTH = 4194304
MAX_LENGTH_RETURNED_DATA = 4194304
MAX_CONTRACT_SIZE = 4194304
MAX_TRANSACTION_SIZE = 1572864
MAX_RECEIPT_SIZE = 4194304
MAX_INPUT_DATA_DEPENDENCIES = 128
MAX_DEPLOY_ACTIONS_PER_RECEIPT = 10
ACCESS_KEY_MIN_GAS_KEY_BORSH_LEN = 27
GAS_KEY_INFO_BORSH_LEN = 18
GAS_KEY_MAX_BALANCE_TO_BURN = 10 ** 24
GAS_KEY_MAX_NONCES = 1024
MAX_ACCOUNT_DELETION_STORAGE_USAGE = 10_000
PROOF_SOFT_LIMIT = 4_000_000
ALLOWED_SHARD_OUTGOING_GAS = 1_000_000_000_000_000
NONCE_RANGE = 1_000_000
GROUP_SIZE_UPPER_BOUND = 100_000          # ReceiptGroupsConfig::default_config: ByteSize::kb(100)
ETH_WALLET_HASH = {
    'mainnet': bytes.fromhex('1daa835c4637f7ae3d924095ba3f0bf2829bcfa17b1068cd58bd853dcad7ceb5'),
    'testnet': bytes.fromhex('238feac1f86cc9f9f4003e3f6d5aebc04eaea9c394032bd29470e9609b67f6c5'),
    'other': bytes.fromhex('d2884a900d4fa370e48f1e3d4865d4dc0dbd093c89f0e7baef2eddc142c49e8d'),
}

# trie columns (core/primitives/src/trie_key.rs)
C_ACCOUNT, C_CODE, C_ACCESS_KEY, C_RECEIVED_DATA, C_POSTPONED_ID, C_PENDING, C_POSTPONED = 0, 1, 2, 3, 4, 5, 6
C_DELAYED, C_DATA, C_YIELD_INDICES, C_YIELD_TIMEOUT, C_YIELD_RECEIPT = 7, 9, 10, 11, 12
C_BUFFERED_INDICES, C_BUFFERED, C_BW_STATE, C_GROUPS_DATA, C_GROUPS_ITEM = 13, 14, 15, 16, 17
C_YIELD_STATUS, C_DATA_TO_YIELD = 20, 23


def k_account(a): return u8(C_ACCOUNT) + a
def k_code(a): return u8(C_CODE) + a
def k_ak(a, pk): return u8(C_ACCESS_KEY) + a + u8(C_ACCESS_KEY) + pk
def k_gk_nonce(a, pk, i): return u8(C_ACCESS_KEY) + a + u8(C_ACCESS_KEY) + pk + u16(i)
def k_acc_data(col, a, h): return u8(col) + a + b',' + h


# ---------------------------------------------------------------------------------------------
# arithmetic helpers (u64 gas / u128 balance with nearcore's overflow behaviour)
# ---------------------------------------------------------------------------------------------
class Overflow(Exception):
    pass


def cadd64(a, b):
    r = a + b
    if r > U64_MAX:
        raise Overflow()
    return r


def cadd128(a, b):
    r = a + b
    if r > U128_MAX:
        raise Overflow()
    return r


def cmul128(a, b):
    r = a * b
    if r > U128_MAX:
        raise Overflow()
    return r


def padd(p, q):
    return (cadd64(p[0], q[0]), cadd64(p[1], q[1]))


def pmul(p, n):
    return (p[0] * n, p[1] * n)   # checked_mul(...).unwrap(): never overflows for valid sizes


def fee(name, which):
    s, ns, e = FEES[name]
    return {'sir': s, 'not': ns, 'exec': e}[which]


def send(name, sir):
    return fee(name, 'sir' if sir else 'not')


def pk_trie_len(pk):
    return len(pk)   # PublicKeyHandle borsh = PublicKey borsh for ED25519/SECP256K1


def ak_key_len(acc_len, pk_len):
    return 1 + acc_len + 1 + pk_len


def is_implicit(a):
    return account_type(a) != 'named'


# ---------------------------------------------------------------------------------------------
# fees (runtime/runtime/src/config.rs, core/parameters/src/cost.rs)
# ---------------------------------------------------------------------------------------------
def transfer_send_fee(sir, recv):
    t = account_type(recv)
    f = send('transfer', sir)
    if t == 'named':
        return f
    f = padd(f, send('create_account', sir))
    if t == 'near':
        f = padd(f, send('add_full_access_key', sir))
    return f


def transfer_exec_fee(recv):
    t = account_type(recv)
    f = fee('transfer', 'exec')
    if t == 'named':
        return f
    f = padd(f, fee('create_account', 'exec'))
    if t == 'near':
        f = padd(f, fee('add_full_access_key', 'exec'))
    return f


def permission_send_fees(ak, sir):
    if ak.has_fc():
        nb = sum(len(m) + 1 for m in ak.methods)
        f = padd(send('add_function_call_key_base', sir), pmul(send('add_function_call_key_byte', sir), nb))
    else:
        f = send('add_full_access_key', sir)
    if ak.is_gas_key():
        f = padd(f, pmul(send('gas_key_byte', sir), GAS_KEY_INFO_BORSH_LEN))
    return f


def permission_exec_fees(ak, recv, pk):
    if ak.has_fc():
        nb = sum(len(m) + 1 for m in ak.methods)
        f = padd(fee('add_function_call_key_base', 'exec'), pmul(fee('add_function_call_key_byte', 'exec'), nb))
    else:
        f = fee('add_full_access_key', 'exec')
    if not ak.is_gas_key():
        return f
    nn = ak.gk_nonces
    base = pmul(fee('gas_key_nonce_write_base', 'exec'), nn)
    nonce_key_len = ak_key_len(len(recv), pk_trie_len(pk)) + 2
    per = pmul(pmul(fee('gas_key_byte', 'exec'), nonce_key_len + 8), nn)
    return padd(f, padd(base, per))


def total_send_fees(sir, actions, recv):
    r = (0, 0)
    for a in actions:
        t = a.tag
        if t == A_CREATE:
            d = send('create_account', sir)
        elif t == A_DEPLOY:
            d = padd(send('deploy_contract_base', sir), pmul(send('deploy_contract_byte', sir), len(a.f['code'])))
        elif t == A_FC:
            nb = len(a.f['method']) + len(a.f['args'])
            d = padd(send('function_call_base', sir), pmul(send('function_call_byte', sir), nb))
        elif t == A_TRANSFER:
            d = transfer_send_fee(sir, recv)
        elif t in (A_TO_GK, A_FROM_GK):
            d = padd(send('gas_key_transfer_base', sir), pmul(send('gas_key_byte', sir), pk_trie_len(a.f['pk'])))
        elif t == A_STAKE:
            d = send('stake', sir)
        elif t == A_ADDKEY:
            d = permission_send_fees(a.f['ak'], sir)
        elif t == A_DELKEY:
            d = send('delete_key', sir)
        elif t == A_DELACC:
            d = send('delete_account', sir)
        elif t in (A_DELEGATE, A_DELEGATE_V2):
            d = padd(send('delegate', sir), total_send_fees(sir, a.f['actions'], a.f['receiver']))
        else:
            raise OOD("r.exec: action %d" % t)
        r = padd(r, d)
    return r


def total_prepaid_send_fees(actions):
    r = (0, 0)
    for a in actions:
        if a.tag in (A_DELEGATE, A_DELEGATE_V2):
            r = padd(r, total_send_fees(a.f['sender'] == a.f['receiver'], a.f['actions'], a.f['receiver']))
    return r


def exec_fee(a, recv):
    t = a.tag
    if t == A_CREATE:
        return fee('create_account', 'exec')
    if t == A_DEPLOY:
        return padd(fee('deploy_contract_base', 'exec'), pmul(fee('deploy_contract_byte', 'exec'), len(a.f['code'])))
    if t == A_FC:
        nb = len(a.f['method']) + len(a.f['args'])
        return padd(fee('function_call_base', 'exec'), pmul(fee('function_call_byte', 'exec'), nb))
    if t == A_TRANSFER:
        return transfer_exec_fee(recv)
    if t == A_STAKE:
        return fee('stake', 'exec')
    if t == A_ADDKEY:
        return permission_exec_fees(a.f['ak'], recv, a.f['pk'])
    if t == A_DELKEY:
        return fee('delete_key', 'exec')
    if t == A_DELACC:
        return fee('delete_account', 'exec')
    if t in (A_DELEGATE, A_DELEGATE_V2):
        return fee('delegate', 'exec')
    if t in (A_TO_GK, A_FROM_GK):
        return padd(fee('gas_key_transfer_base', 'exec'),
                    pmul(fee('gas_key_byte', 'exec'), ak_key_len(len(recv), pk_trie_len(a.f['pk'])) + ACCESS_KEY_MIN_GAS_KEY_BORSH_LEN))
    raise OOD("r.exec: action %d" % t)


def total_prepaid_exec_fees(actions, recv):
    r = (0, 0)
    for a in actions:
        if a.tag in (A_DELEGATE, A_DELEGATE_V2):
            d = total_prepaid_exec_fees(a.f['actions'], a.f['receiver'])
            d = padd(d, exec_fee(a, a.f['receiver']))
            d = padd(d, fee('new_action_receipt', 'exec'))
        else:
            d = exec_fee(a, recv)
        r = padd(r, d)
    return r


def signature_verification_cost(pk, actions):
    t = SIG_VERIFICATION[pk[0]]
    for a in actions:
        if a.tag in (A_DELEGATE, A_DELEGATE_V2):
            t = padd(t, SIG_VERIFICATION[a.f['pk'][0]])
    return t


def tx_cost(t, gas_price):
    """config.rs calculate_tx_cost; None = IntegerOverflowError (CostOverflow)."""
    try:
        sir = t.recv == t.signer
        burnt = padd(send('new_action_receipt', sir), total_send_fees(sir, t.actions, t.recv))
        burnt = padd(burnt, signature_verification_cost(t.pk, t.actions))
        prepaid_gas = N.total_prepaid_gas(t.actions)
        if prepaid_gas > U64_MAX:
            raise Overflow()
        pse = total_prepaid_send_fees(t.actions)
        pee = total_prepaid_exec_fees(t.actions, t.recv)
        rc = fee('new_action_receipt', 'exec')
        gas_remaining = cadd64(cadd64(cadd64(prepaid_gas, pse[0]), rc[0]), pee[0])
        burnt_amount = cmul128(gas_price, burnt[0])
        rgp = max(gas_price, MIN_GAS_PURCHASE_PRICE)
        rem = cmul128(rgp, gas_remaining)
        gas_cost = cadd128(burnt_amount, rem)
        deposit = N.total_deposit(t.actions)
        if deposit > U128_MAX:
            raise Overflow()
        total = cadd128(gas_cost, deposit)
    except Overflow:
        return None
    return dict(gas_burnt=burnt[0], compute=burnt[1], gas_remaining=gas_remaining, rgp=rgp,
                burnt_amount=burnt_amount, gas_cost=gas_cost, deposit=deposit, total=total)


def receipt_congestion_gas(x):
    """congestion_control.rs compute_receipt_congestion_gas (u64; overflow -> RuntimeError)."""
    if x.kind not in (K_ACTION, K_ACTION_V2):
        return 0
    try:
        g = cadd64(total_prepaid_exec_fees(x.actions, x.recv)[0], fee('new_action_receipt', 'exec')[0])
        g = cadd64(g, total_prepaid_send_fees(x.actions)[0])
        pg = N.total_prepaid_gas(x.actions)
        return cadd64(pg, g)
    except Overflow:
        raise Reject("receipt congestion gas overflow")


# ---------------------------------------------------------------------------------------------
# validation (action_validation.rs, verifier.rs validate_receipt)
# ---------------------------------------------------------------------------------------------
def is_valid_staking_key(pk):
    """near_crypto::key_conversion::is_valid_staking_key: ED25519, decompresses, torsion-free."""
    if pk[0] != 0:
        return False
    pt = ed25519._decompress(pk[1:])
    if pt is None:
        return False
    return ed25519._mul(ed25519.L, pt) == ed25519.IDENT


def validate_actions(actions, recv, new_receipt):
    """None if valid, else a reason string."""
    if len(actions) > MAX_ACTIONS_PER_RECEIPT:
        return "TotalNumberOfActionsExceeded"
    if new_receipt and sum(1 for a in actions if a.tag == A_DEPLOY) > MAX_DEPLOY_ACTIONS_PER_RECEIPT:
        return "TotalNumberOfDeployActionsExceeded"
    found_delegate = False
    for i, a in enumerate(actions):
        if a.tag == A_DELACC:
            if i + 1 < len(actions):
                return "DeleteActionMustBeFinal"
        elif a.tag in (A_DELEGATE, A_DELEGATE_V2):
            if found_delegate:
                return "DelegateActionMustBeOnlyOne"
            found_delegate = True
        e = validate_action(a, recv, new_receipt)
        if e:
            return e
    if N.total_prepaid_gas(actions) > MAX_TOTAL_PREPAID_GAS:
        return "TotalPrepaidGasExceeded"
    return None


def validate_action(a, recv, new_receipt):
    t = a.tag
    if t == A_DEPLOY:
        return "ContractSizeExceeded" if len(a.f['code']) > MAX_CONTRACT_SIZE else None
    if t == A_FC:
        if a.f['gas'] == 0:
            return "FunctionCallZeroAttachedGas"
        if len(a.f['method']) > MAX_LENGTH_METHOD_NAME:
            return "FunctionCallMethodNameLengthExceeded"
        if len(a.f['args']) > MAX_ARGUMENTS_LENGTH:
            return "FunctionCallArgumentsLengthExceeded"
        return None
    if t == A_STAKE:
        return None if is_valid_staking_key(a.f['pk']) else "UnsuitableStakingKey"
    if t == A_ADDKEY:
        ak = a.f['ak']
        if ak.has_fc():
            if not valid_account_id(ak.receiver):
                return "InvalidAccountId"
            total = 0
            for m in ak.methods:
                if len(m) > MAX_LENGTH_METHOD_NAME:
                    return "AddKeyMethodNameLengthExceeded"
                total += len(m) + 1
            if total > MAX_NUMBER_BYTES_METHOD_NAMES:
                return "AddKeyMethodNamesNumberOfBytesExceeded"
        if ak.is_gas_key():
            if ak.perm == 'gfc' and ak.allowance is not None:
                return "GasKeyFunctionCallAllowanceNotAllowed"
            if ak.gk_nonces == 0 or ak.gk_nonces > GAS_KEY_MAX_NONCES:
                return "GasKeyInvalidNumNonces"
            if ak.gk_balance != 0:
                return "AddGasKeyWithNonZeroBalance"
        return None
    if t == A_DELACC:
        return None if valid_account_id(a.f['beneficiary']) else "InvalidAccountId"
    if t in (A_DELEGATE, A_DELEGATE_V2):
        if len(a.f['actions']) > MAX_ACTIONS_PER_RECEIPT:
            return "TotalNumberOfActionsExceeded"
        return validate_actions(a.f['actions'], a.f['receiver'], new_receipt)
    return None


def validate_receipt(x, new_receipt):
    if new_receipt and len(x.raw) > MAX_RECEIPT_SIZE:
        return "ReceiptSizeExceeded"
    if x.is_action():
        if len(x.inputs) > MAX_INPUT_DATA_DEPENDENCIES:
            return "NumberInputDataDependenciesExceeded"
        return validate_actions(x.actions, x.recv, new_receipt)
    if x.data is not None and len(x.data) > MAX_LENGTH_RETURNED_DATA:
        return "ReturnedValueLengthExceeded"
    return None


# ---------------------------------------------------------------------------------------------
# transactions
# ---------------------------------------------------------------------------------------------
FORBIDDEN = (A_FC,)


def check_tx_shape(t):
    if t.pk[0] != 0 or t.sig[0] != 0:
        raise OOD("w.tx_shape: transaction key or signature is not ED25519")

    def walk(actions, top):
        for a in actions:
            if a.tag in FORBIDDEN:
                raise OOD("w.tx_shape: FunctionCall action")
            if a.tag in (A_ADDKEY, A_DELKEY, A_STAKE, A_TO_GK, A_FROM_GK) and a.f['pk'][0] == 2:
                raise OOD("w.tx_shape: ML-DSA key in an action")
            if a.tag in (A_DELEGATE, A_DELEGATE_V2):
                if a.f['pk'][0] != 0 or a.f['sig'][0] != 0:
                    raise OOD("w.tx_shape: delegate key or signature is not ED25519")
                walk(a.f['actions'], False)
    walk(t.actions, True)


def decode_state_witness_d2(b):
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
        receipts = r.vec(lambda: N.read_receipt(r))
        from_shard, to_shard = r.u64(), r.u64()

        def item():
            h = r.hash()
            d = r.u8()
            if d > 1:
                raise DecodeError("Direction")
            return (h, d)
        path = r.vec(item)
        proofs[key] = (receipts, from_shard, to_shard, path)   # duplicate key: last wins
    w['proofs'] = proofs
    w['applied_receipts_hash'] = r.hash()
    w['txs'] = r.vec(lambda: N.read_tx(r))
    w['implicit'] = r.vec(lambda: s3.read_transition(r))
    w['new_txs'] = r.vec(lambda: N.read_tx(r))
    r.end()
    for t in w['txs'] + w['new_txs']:
        check_tx_shape(t)
    return w


# ---------------------------------------------------------------------------------------------
# state: TrieUpdate overlay (core/store/src/trie/update.rs) over the partial trie
# ---------------------------------------------------------------------------------------------
class State:
    def __init__(self, trie):
        self.trie = trie
        self.committed = {}
        self.prospective = {}
        self.data_removals = 0

    def _ov(self, k):
        if k in self.prospective:
            return True, self.prospective[k]
        if k in self.committed:
            return True, self.committed[k]
        return False, None

    def get(self, k):
        hit, v = self._ov(k)
        return v if hit else self.trie.get(k)

    def contains(self, k):
        hit, v = self._ov(k)
        return (v is not None) if hit else (self.trie.get_ref(k) is not None)

    def value_len(self, k):
        hit, v = self._ov(k)
        if hit:
            return None if v is None else len(v)
        ref = self.trie.get_ref(k)
        return None if ref is None else ref[0]

    def set(self, k, v):
        self.prospective[k] = v

    def remove(self, k):
        if k[0] == C_DATA:
            self.data_removals += 1
        self.prospective[k] = None

    def commit(self):
        self.committed.update(self.prospective)
        self.prospective = {}

    def rollback(self):
        self.prospective = {}

    def iter_prefix(self, prefix):
        """TrieUpdateIterator over the trie and the overlay (committed, then prospective)."""
        items = {k: True for k, _ in self.trie.iter_prefix(prefix)}
        ov = dict(self.committed)
        ov.update(self.prospective)
        for k, v in ov.items():
            if k.startswith(prefix):
                items[k] = v is not None
        return sorted(k for k, present in items.items() if present)

    def finalize(self):
        assert not self.prospective
        return self.trie.update(sorted(self.committed.items()))

    # typed accessors
    def get_account(self, a):
        v = self.get(k_account(a))
        return None if v is None else N.decode_account(v)

    def set_account(self, a, acc):
        if acc.v == 1 and acc.amount == U128_MAX:
            raise OOD("a.sentinel: account amount equals the AccountV2 serialization sentinel")
        self.set(k_account(a), acc.encode())

    def get_ak(self, a, pk):
        v = self.get(k_ak(a, pk))
        return None if v is None else N.decode_ak(v)

    def set_ak(self, a, pk, ak):
        self.set(k_ak(a, pk), ak.encode())

    def get_u64(self, k):
        v = self.get(k)
        if v is None:
            return None
        if len(v) != 8:
            raise Reject("StorageInconsistentState: u64 value")
        return struct.unpack('<Q', v)[0]

    def get_indices(self, k):
        v = self.get(k)
        if v is None:
            return [0, 0]
        if len(v) != 16:
            raise Reject("StorageInconsistentState: queue indices")
        return list(struct.unpack('<QQ', v))


def storage_stake_ok(acc, balance):
    """verifier.rs check_storage_stake: True / False (lack) / raises Reject (overflow)."""
    required = STORAGE_AMOUNT_PER_BYTE * acc.su
    if required > U128_MAX:
        raise Reject("storage usage overflows")
    available = balance + acc.locked
    if available > U128_MAX:
        raise Reject("amount + locked overflow")
    if available >= required:
        return True
    return acc.su <= ZERO_BALANCE_ACCOUNT_STORAGE_LIMIT


def create_hash_index(base, height, salt):
    return sha(base + u64(height) + u64(salt))


def partial_outcome(receipt_ids, gas, tokens, executor, status):
    """borsh PartialExecutionOutcome; status: ('fail',) | ('value', bytes) | ('rid', hash)."""
    if status[0] == 'fail':
        st = u8(1)
    elif status[0] == 'value':
        st = u8(2) + bstr(status[1])
    else:
        st = u8(3) + status[1]
    return u32(len(receipt_ids)) + b''.join(receipt_ids) + u64(gas) + u128(tokens) + bstr(executor) + st


def outcome_leaf(oid, partial):
    return sha(u32(2) + oid + sha(partial))


# ---------------------------------------------------------------------------------------------
# the main transition (Runtime::apply for a new chunk), domain D2
# ---------------------------------------------------------------------------------------------
class Apply:
    def __init__(self, st, L, s0, height, gas_price, gas_limit, minimum_stake, chain_id, ctx):
        self.st, self.L, self.s0, self.height = st, L, s0, height
        self.gas_price, self.gas_limit, self.minimum_stake, self.chain_id = gas_price, gas_limit, minimum_stake, chain_id
        self.ctx = ctx
        self.leaves = []
        self.total_gas = 0
        self.total_compute = 0
        self.tx_burnt = 0
        self.other_burnt = 0
        self.outgoing = []            # forwarded receipts in order
        self.proposals = []           # (account, pk, stake)
        self.local = []
        self.instant = []

    # -------- outcomes / totals
    def add_total(self, gas, compute):
        self.total_gas = cadd64(self.total_gas, gas)
        self.total_compute = cadd64(self.total_compute, compute)

    def shard_of(self, a):
        return s3.account_to_shard(self.L, a)

    # -------- receipt sink (congestion_control.rs ReceiptSinkV2)
    def sink_init(self, own_info, cong, grants):
        st = self.st
        self.own = list(own_info[:3])
        self.limits = {}
        for sid, (info, missed) in cong.items():
            g = U64_MAX if sid == self.s0 else outgoing_gas_limit(info, missed, self.s0)
            self.limits[sid] = [g, grants.get((self.s0, sid), 0)]
        v = st.get(u8(C_BUFFERED_INDICES))
        self.buffers = {}
        if v is not None:
            try:
                r = R(v)
                for _ in range(r.u32()):
                    k = r.u64()
                    self.buffers[k] = [r.u64(), r.u64()]
                r.end()
            except DecodeError:
                raise Reject("StorageInconsistentState: BufferedReceiptIndices")
        self.metas = {}
        for k in sorted(self.buffers):
            m = st.get(u8(C_GROUPS_DATA) + u64(k))
            if m is not None:
                self.metas[k] = self.decode_meta(m)

    @staticmethod
    def decode_meta(v):
        try:
            r = R(v)
            if r.u8() != 0:
                raise DecodeError("ReceiptGroupsQueueData tag")
            m = dict(first=r.u64(), next=r.u64(), size=r.u64(), gas=r.u128(), num=r.u64())
            r.end()
            return m
        except DecodeError:
            raise Reject("StorageInconsistentState: receipt groups data")

    def save_meta(self, sid):
        m = self.metas[sid]
        self.st.set(u8(C_GROUPS_DATA) + u64(sid),
                    u8(0) + u64(m['first']) + u64(m['next']) + u64(m['size']) + u128(m['gas']) + u64(m['num']))

    def group_key(self, sid, i):
        return u8(C_GROUPS_ITEM) + u64(sid) + u64(i)

    def get_group(self, sid, i):
        v = self.st.get(self.group_key(sid, i))
        if v is None:
            raise Reject("StorageInconsistentState: receipt group missing")
        try:
            r = R(v)
            if r.u8() != 0:
                raise DecodeError("ReceiptGroup tag")
            g = [r.u64(), r.u128()]
            r.end()
            return g
        except DecodeError:
            raise Reject("StorageInconsistentState: receipt group")

    def set_group(self, sid, i, g):
        self.st.set(self.group_key(sid, i), u8(0) + u64(g[0]) + u128(g[1]))

    def meta_pushed(self, sid, size, gas):
        m = self.metas.setdefault(sid, dict(first=0, next=0, size=0, gas=0, num=0))
        m['size'] += size
        m['gas'] += gas
        m['num'] += 1
        if m['first'] < m['next']:
            # pop_back
            last = self.get_group(sid, m['next'] - 1)
            self.st.remove(self.group_key(sid, m['next'] - 1))
            m['next'] -= 1
            self.save_meta(sid)
            if last[0] + size > GROUP_SIZE_UPPER_BOUND:
                self.set_group(sid, m['next'], last)
                m['next'] += 1
                self.save_meta(sid)
                self.set_group(sid, m['next'], [size, gas])
                m['next'] += 1
                self.save_meta(sid)
            else:
                self.set_group(sid, m['next'], [last[0] + size, last[1] + gas])
                m['next'] += 1
                self.save_meta(sid)
        else:
            self.set_group(sid, m['next'], [size, gas])
            m['next'] += 1
            self.save_meta(sid)

    def meta_popped(self, sid, size, gas):
        m = self.metas[sid]
        if m['size'] < size or m['gas'] < gas or m['num'] < 1:
            raise Reject("receipt groups underflow (panic)")
        m['size'] -= size
        m['gas'] -= gas
        m['num'] -= 1
        if m['first'] >= m['next']:
            raise Reject("no receipt groups to pop from (panic)")
        g = self.get_group(sid, m['first'])
        if g[0] < size or g[1] < gas:
            raise Reject("receipt group underflow (panic)")
        g = [g[0] - size, g[1] - gas]
        if g[0] == 0:
            if g[1] != 0:
                raise Reject("empty receipt group with gas (panic)")
            # pop_front: get again, remove, advance
            self.get_group(sid, m['first'])
            self.st.remove(self.group_key(sid, m['first']))
            m['first'] += 1
            self.save_meta(sid)
        else:
            self.set_group(sid, m['first'], g)
            self.save_meta(sid)

    def write_buffer_indices(self):
        out = u32(len(self.buffers)) + b''.join(u64(k) + u64(f) + u64(n) for k, (f, n) in sorted(self.buffers.items()))
        self.st.set(u8(C_BUFFERED_INDICES), out)

    def try_forward(self, x, gas, size, shard):
        if size > MAX_RECEIPT_SIZE:
            size = MAX_RECEIPT_SIZE
        lim = self.limits.setdefault(shard, [U64_MAX, 0])
        if lim[0] >= min(gas, ALLOWED_SHARD_OUTGOING_GAS) and lim[1] >= size:
            self.outgoing.append(x)
            lim[0] = max(lim[0] - gas, 0)
            lim[1] -= size
            return True
        return False

    def forward_or_buffer(self, x):
        shard = self.shard_of(x.recv)
        size = len(x.raw)
        gas = receipt_congestion_gas(x)
        if self.try_forward(x, gas, size, shard):
            return
        # buffer_receipt: StateStoredReceipt V1 with metadata
        self.own[2] = cadd64(self.own[2], size)
        self.own[1] = cadd128(self.own[1], gas)
        self.meta_pushed(shard, size, gas)
        b = self.buffers.setdefault(shard, [0, 0])
        self.st.set(u8(C_BUFFERED) + u16(shard) + u64(b[1]), N.encode_state_stored(x, gas, size))
        b[1] += 1
        self.write_buffer_indices()

    def forward_from_buffers(self):
        for sid in self.L.shard_ids:
            if sid not in self.buffers:
                continue
            f, n = self.buffers[sid]
            forwarded = []
            for i in range(f, n):
                v = self.st.trie.get(u8(C_BUFFERED) + u16(sid) + u64(i))
                if v is None:
                    raise Reject("StorageInconsistentState: buffered receipt missing")
                x, meta, v1 = N.decode_stored_receipt(v)
                gas, size = meta if meta is not None else (receipt_congestion_gas(x), len(x.raw))
                if not self.try_forward(x, gas, size, self.shard_of(x.recv)):
                    break
                if self.own[2] < size or self.own[1] < gas:
                    raise Reject("congestion info underflow")
                self.own[2] -= size
                self.own[1] -= gas
                forwarded.append((size, gas, v1))
            if forwarded:
                for i in range(f, f + len(forwarded)):
                    self.st.remove(u8(C_BUFFERED) + u16(sid) + u64(i))
                self.buffers[sid][0] = f + len(forwarded)
                self.write_buffer_indices()
            for size, gas, v1 in forwarded:
                if v1:
                    if sid not in self.metas:
                        raise Reject("receipt groups metadata missing (panic)")
                    self.meta_popped(sid, size, gas)

    # -------- delayed queue (DelayedReceiptQueueWrapper)
    def delayed_init(self):
        self.dq = self.st.get_indices(u8(C_DELAYED))
        self.dq_new_gas = self.dq_new_bytes = self.dq_rm_gas = self.dq_rm_bytes = 0

    def delayed_push(self, x):
        gas = receipt_congestion_gas(x)
        size = len(x.raw)
        self.dq_new_gas = cadd64(self.dq_new_gas, gas)
        self.dq_new_bytes = cadd64(self.dq_new_bytes, size)
        self.st.set(u8(C_DELAYED) + u64(self.dq[1]), N.encode_state_stored(x, gas, size))
        self.dq[1] += 1
        self.st.set(u8(C_DELAYED), u64(self.dq[0]) + u64(self.dq[1]))

    def delayed_pop(self):
        while True:
            if self.dq[0] >= self.dq[1]:
                return None
            k = u8(C_DELAYED) + u64(self.dq[0])
            v = self.st.get(k)
            if v is None:
                raise Reject("StorageInconsistentState: delayed receipt missing")
            x, meta, _ = N.decode_stored_receipt(v)
            self.st.remove(k)
            self.dq[0] += 1
            self.st.set(u8(C_DELAYED), u64(self.dq[0]) + u64(self.dq[1]))
            gas, size = meta if meta is not None else (receipt_congestion_gas(x), len(x.raw))
            self.dq_rm_gas = cadd64(self.dq_rm_gas, gas)
            self.dq_rm_bytes = cadd64(self.dq_rm_bytes, size)
            if self.shard_of(x.recv) == self.s0:
                return x

    # -------- transactions (lib.rs process_transactions)
    def process_transactions(self, txs, flags):
        seen = set()
        for t, flag in zip(txs, flags):
            if t.hash in seen:
                continue
            seen.add(t.hash)
            failed = outcome_leaf(t.hash, partial_outcome([], 0, 0, t.signer, ('fail',)))
            if not flag:
                self.leaves.append(failed)
                continue
            if validate_actions(t.actions, t.recv, True) is not None:
                self.leaves.append(failed)
                continue
            if len(t.raw) > MAX_TRANSACTION_SIZE or not ed25519.verify(t.pk[1:], t.sig[1:], t.hash):
                self.leaves.append(failed)
                continue
            cost = tx_cost(t, self.gas_price)
            if cost is None:
                self.leaves.append(failed)
                continue
            acc = self.st.get_account(t.signer)
            if acc is None:
                self.leaves.append(failed)
                continue
            ak = self.st.get_ak(t.signer, t.pk)
            if ak is None:
                self.leaves.append(failed)
                continue
            if t.nonce_index is not None:
                cur = self.st.get_u64(k_gk_nonce(t.signer, t.pk, t.nonce_index))
                if cur is None:
                    self.leaves.append(failed)
                    continue
                verdict = self.verify_gas_key(acc, ak, cur, t, cost)
            else:
                verdict = self.verify_regular(acc, ak, t, cost)
            if verdict[0] == 'fail':
                self.leaves.append(failed)
                continue
            kind, new_amount, ak_update = verdict
            if kind == 'ok':
                rid = create_hash_index(t.hash, self.height, 0)
                x = N.new_action_receipt(t.signer, t.recv, rid, t.signer, t.pk, cost['rgp'], [], [], t.actions)
                if t.recv == t.signer:
                    self.local.append(x)
                else:
                    self.forward_or_buffer(x)
                partial = partial_outcome([rid], cost['gas_burnt'], cost['burnt_amount'], t.signer, ('rid', rid))
                compute = cost['compute']
            else:   # gas key deposit failure: gas burnt, failed outcome
                partial = partial_outcome([], cost['gas_burnt'], cost['burnt_amount'], t.signer, ('fail',))
                compute = cost['gas_burnt']
            if self.tx_burnt + cost['burnt_amount'] > U128_MAX:
                continue   # lib.rs: dropped without outcome or state change
            self.tx_burnt += cost['burnt_amount']
            try:
                self.add_total(cost['gas_burnt'], compute)
            except Overflow:
                raise Reject("chunk gas overflow")
            self.leaves.append(outcome_leaf(t.hash, partial))
            acc = acc.copy()
            acc.amount = new_amount
            ak = ak.copy()
            if ak_update[0] == 'regular':
                ak.nonce = ak_update[1]
                if ak_update[2] is not None:
                    ak.allowance = ak_update[2]
            else:
                ak.gk_balance = ak_update[1]
            self.st.set_account(t.signer, acc)
            if ak_update[0] == 'gas':
                self.st.set(k_gk_nonce(t.signer, t.pk, t.nonce_index), u64(t.nonce))
            self.st.set_ak(t.signer, t.pk, ak)
            self.st.commit()

    def verify_nonce(self, tx_nonce, current, strict):
        if strict:
            if current + 1 > U64_MAX or tx_nonce != current + 1:
                return False
        elif tx_nonce <= current:
            return False
        return tx_nonce < min(self.height * NONCE_RANGE, U64_MAX)

    def verify_regular(self, acc, ak, t, cost):
        if ak.is_gas_key():
            return ('fail',)
        if not self.verify_nonce(t.nonce, ak.nonce, t.strict):
            return ('fail',)
        if acc.amount < cost['total']:
            return ('fail',)
        new_amount = acc.amount - cost['total']
        new_allowance = None
        if ak.perm == 'fc' and ak.allowance is not None:
            if ak.allowance < cost['total']:
                return ('fail',)
            new_allowance = ak.allowance - cost['total']
        if not storage_stake_ok(acc, new_amount):
            return ('fail',)
        if ak.has_fc():
            return ('fail',)   # verify_function_call_permission: never a single FunctionCall in D2
        return ('ok', new_amount, ('regular', t.nonce, new_allowance))

    def verify_gas_key(self, acc, ak, cur, t, cost):
        if not ak.is_gas_key():
            return ('fail',)
        if t.nonce_index >= ak.gk_nonces:
            return ('fail',)
        if not self.verify_nonce(t.nonce, cur, t.strict):
            return ('fail',)
        if ak.gk_balance < cost['gas_cost']:
            return ('fail',)
        new_gk = ak.gk_balance - cost['gas_cost']
        if ak.gk_balance < cost['burnt_amount']:
            return ('fail',)
        gk_on_fail = ak.gk_balance - cost['burnt_amount']
        if ak.has_fc():
            return ('fail',)
        if acc.amount < cost['deposit']:
            return ('deposit_failed', acc.amount, ('gas', gk_on_fail))
        new_amount = acc.amount - cost['deposit']
        if not storage_stake_ok(acc, new_amount):
            return ('deposit_failed', acc.amount, ('gas', gk_on_fail))
        return ('ok', new_amount, ('gas', new_gk))

    # -------- receipts (lib.rs process_receipts)
    def process_receipts(self):
        limit = self.gas_limit
        for x in self.local:
            if self.total_compute >= limit:
                self.delayed_push(x)
            else:
                self.process_with_instants(x)
        while self.total_compute < limit:
            x = self.delayed_pop()
            if x is None:
                break
            e = validate_receipt(x, False)
            if e:
                raise Reject("StorageInconsistentState: invalid delayed receipt (%s)" % e)
            self.process_with_instants(x)
        for x in self.incoming:
            e = validate_receipt(x, False)
            if e:
                raise Reject("ReceiptValidationError: %s" % e)
            if self.total_compute >= limit:
                self.delayed_push(x)
            else:
                self.process_with_instants(x)
        self.yield_indices = self.resolve_yield_timeouts(limit)

    def process_with_instants(self, x):
        self.process_receipt_metrics(x)
        while self.instant:
            y = self.instant.pop(0)
            self.process_receipt_metrics(y)

    def process_receipt_metrics(self, x):
        out = self.process_receipt(x)
        if out is not None:
            leaf, gas, compute = out
            try:
                self.add_total(gas, compute)
            except Overflow:
                raise Reject("chunk gas overflow")
            self.leaves.append(leaf)

    def process_receipt(self, x):
        st = self.st
        acc_id = x.recv
        if x.kind == K_DATA:
            st.set(k_acc_data(C_RECEIVED_DATA, acc_id, x.data_id), self.enc_received(x.data))
            rid = st.get(k_acc_data(C_POSTPONED_ID, acc_id, x.data_id))
            if rid is not None:
                if len(rid) != 32:
                    raise Reject("StorageInconsistentState: postponed receipt id")
                st.remove(k_acc_data(C_POSTPONED_ID, acc_id, x.data_id))
                pk = k_acc_data(C_PENDING, acc_id, rid)
                pv = st.get(pk)
                if pv is None:
                    raise Reject("StorageInconsistentState: pending data count missing")
                if len(pv) != 4:
                    raise Reject("StorageInconsistentState: pending data count")
                cnt = struct.unpack('<I', pv)[0]
                if cnt == 1:
                    st.remove(pk)
                    rk = k_acc_data(C_POSTPONED, acc_id, rid)
                    rv = st.get(rk)
                    if rv is None:
                        raise Reject("StorageInconsistentState: postponed receipt missing")
                    try:
                        ready = N.decode_receipt(rv)
                    except DecodeError:
                        raise Reject("StorageInconsistentState: postponed receipt")
                    st.remove(rk)
                    return self.apply_action_receipt(ready)
                if cnt == 0:
                    raise Reject("StorageInconsistentState: pending data count is 0")
                st.set(pk, u32(cnt - 1))
            st.commit()
            return None
        if x.kind in (K_ACTION, K_ACTION_V2):
            pending = 0
            for d in x.inputs:
                if not st.contains(k_acc_data(C_RECEIVED_DATA, acc_id, d)):
                    pending += 1
                    st.set(k_acc_data(C_POSTPONED_ID, acc_id, d), x.rid)
            if pending == 0:
                return self.apply_action_receipt(x)
            st.set(k_acc_data(C_PENDING, acc_id, x.rid), u32(pending))
            st.set(k_acc_data(C_POSTPONED, acc_id, x.rid), x.raw)
            st.commit()
            return None
        if x.kind in (K_YIELD, K_YIELD_V2):
            if not x.inputs:
                raise Reject("PromiseYield receipt without input data")
            st.set(k_acc_data(C_YIELD_RECEIPT, acc_id, x.inputs[0]), x.raw)
            st.commit()
            return None
        # PromiseResume
        if x.data is None:
            s = st.get(k_acc_data(C_YIELD_STATUS, acc_id, x.data_id))
            if s is not None:
                if s not in (b'\x00', b'\x01'):
                    raise Reject("StorageInconsistentState: PromiseYieldStatus")
                if s == b'\x01':
                    return None
        yv = st.get(k_acc_data(C_YIELD_RECEIPT, acc_id, x.data_id))
        if yv is None:
            return None
        raise OOD("r.exec: a PromiseYield receipt is resumed (its callback executes WASM)")

    @staticmethod
    def enc_received(data):
        return (u8(1) + bstr(data)) if data is not None else u8(0)

    # -------- apply_action_receipt (lib.rs:776-1160)
    def apply_action_receipt(self, x):
        st = self.st
        acc_id = x.recv
        for a in x.actions:
            if a.tag == A_FC:
                raise OOD("r.exec: an executed receipt has a FunctionCall action")
        if x.pk[0] == 2:
            raise OOD("r.key_type: executed receipt with an ML-DSA signer key")
        for a in x.actions:
            if a.tag in (A_ADDKEY, A_DELKEY, A_STAKE, A_TO_GK, A_FROM_GK) and a.f['pk'][0] == 2:
                raise OOD("r.key_type: ML-DSA key in an executed action")
        for d in x.inputs:
            k = k_acc_data(C_RECEIVED_DATA, acc_id, d)
            v = st.get(k)
            if v is None:
                raise Reject("StorageInconsistentState: received data should be in the state")
            st.remove(k)
        st.commit()
        account = st.get_account(acc_id)
        did_not_exist = account is None
        ctx = dict(account=account, actor=x.pred)
        nar = fee('new_action_receipt', 'exec')
        res = dict(gas_burnt=nar[0], gas_used=nar[0], compute=nar[1], ok=True, err=None, new=[],
                   proposals=[], tokens_burnt=0)
        is_refund = x.pred == b'system'
        for i, a in enumerate(x.actions):
            ar = self.apply_action(a, x, ctx, is_refund, len(x.actions) == 1)
            if ar['ok']:
                for y in ar['new']:
                    if validate_receipt(y, True) is not None:
                        ar['ok'] = False
                        ar['err'] = 'NewReceiptValidationError'
                        break
            try:
                res['gas_burnt'] = cadd64(res['gas_burnt'], ar['gas_burnt'])
                res['gas_used'] = cadd64(res['gas_used'], ar['gas_used'])
                res['compute'] = cadd64(res['compute'], ar['compute'])
                if ar['ok']:
                    res['new'] += ar['new']
                    res['proposals'] += ar['proposals']
                    res['tokens_burnt'] = cadd128(res['tokens_burnt'], ar['tokens_burnt'])
                else:
                    res['ok'] = False
                    res['err'] = ar['err']
                    res['new'] = []
                    res['proposals'] = []
                    res['tokens_burnt'] = 0
            except Overflow:
                raise Reject("integer overflow merging action results")
            if not res['ok']:
                break
        account = ctx['account']
        if res['ok'] and account is not None:
            if storage_stake_ok(account, account.amount):
                st.set_account(acc_id, account)
            else:
                res['ok'] = False
                res['err'] = 'LackBalanceForState'
                res['new'] = []
                res['proposals'] = []
                res['tokens_burnt'] = 0
        purchase = x.gas_price
        burn = min(purchase, self.gas_price)
        deficit = 0
        penalty = 0
        create_charge = 0
        try:
            if is_refund:
                if not res['ok']:
                    self.other_burnt = cadd128(self.other_burnt, N.total_deposit(x.actions))
            else:
                created = did_not_exist and account is not None and res['ok']
                deficit, penalty, create_charge = self.refunds(x, res, burn, purchase, created)
            self.proposals += res['proposals']
            if res['ok']:
                st.commit()
            else:
                st.rollback()
            gas_burnt = 0 if is_refund else res['gas_burnt']
            tx_burnt_amount = cmul128(burn, gas_burnt) - deficit
            tx_burnt_amount = cadd128(tx_burnt_amount, penalty)
            tx_burnt_amount = cadd128(tx_burnt_amount, create_charge)
            tx_burnt_amount = cadd128(tx_burnt_amount, res['tokens_burnt'])
            self.tx_burnt = cadd128(self.tx_burnt, tx_burnt_amount)
        except Overflow:
            raise Reject("integer overflow in receipt balance accounting")
        if x.outputs:
            data = b'' if res['ok'] else None
            for data_id, recv in x.outputs:
                res['new'].append(N.new_data_receipt(acc_id, recv, ZERO32, data_id, data))
        receipt_ids = []
        for i, y in enumerate(res['new']):
            rid = create_hash_index(x.rid, self.height, i)
            y = N.with_rid(y, rid)
            is_action = y.is_action()
            if self.is_instant(y):
                self.instant.append(y)
            else:
                self.forward_or_buffer(y)
            if is_action:
                receipt_ids.append(rid)
        status = ('value', b'') if res['ok'] else ('fail',)
        partial = partial_outcome(receipt_ids, res['gas_burnt'], tx_burnt_amount, acc_id, status)
        return outcome_leaf(x.rid, partial), res['gas_burnt'], res['compute']

    @staticmethod
    def is_instant(y):
        if y.kind in (K_YIELD, K_YIELD_V2):
            return True
        if y.kind in (K_ACTION, K_ACTION_V2):
            return len(y.actions) == 1 and y.actions[0].tag == A_DELACC and not y.inputs
        return False

    def refunds(self, x, res, burn, purchase, created):
        total_dep = N.total_deposit(x.actions)
        prepaid_gas = cadd64(N.total_prepaid_gas(x.actions), total_prepaid_send_fees(x.actions)[0])
        prepaid_exec = cadd64(total_prepaid_exec_fees(x.actions, x.recv)[0], fee('new_action_receipt', 'exec')[0])
        deposit_refund = total_dep if not res['ok'] else 0
        used = res['gas_burnt'] if not res['ok'] else res['gas_used']
        gross = cadd64(prepaid_gas, prepaid_exec) - used
        if gross < 0:
            raise Reject("gas refund underflow (panic)")
        penalty_gas = min(max(gross * 0 // 1, 0), gross)       # gas_refund_penalty 0/1, min 0
        penalty = cmul128(burn, penalty_gas)
        unused = cmul128(purchase, gross)
        unused = unused - penalty if unused > penalty else 0
        deficit = 0
        surplus = 0
        if burn > purchase:
            deficit = cmul128(burn - purchase, res['gas_burnt'])
        else:
            surplus = cmul128(purchase - burn, res['gas_burnt'])
        burned_refund = surplus
        create_charge = 0
        if created:
            burned_cost = cmul128(burn, fee('create_account', 'exec')[0])
            to_charge = ACCOUNT_CREATION_CHARGE - burned_cost if ACCOUNT_CREATION_CHARGE > burned_cost else 0
            create_charge = min(to_charge, burned_refund)
            burned_refund -= create_charge
        gas_refund = cadd128(unused, burned_refund)
        refund_receiver = x.refund_to if x.refund_to is not None else x.pred
        if deposit_refund > 0:
            res['new'].append(self.balance_refund(refund_receiver, deposit_refund))
        if gas_refund > 0:
            res['new'].append(N.new_action_receipt(b'system', x.signer, ZERO32, x.signer, x.pk, 0, [], [],
                                                   [self.transfer_action(gas_refund)]))
        return deficit, penalty, create_charge

    @staticmethod
    def transfer_action(amount):
        return N.Action(A_TRANSFER, u8(A_TRANSFER) + u128(amount), dict(deposit=amount))

    def balance_refund(self, recv, amount):
        return N.new_action_receipt(b'system', recv, ZERO32, b'system', u8(0) + ZERO32, 0, [], [],
                                    [self.transfer_action(amount)])

    # -------- apply_action (lib.rs:523-773)
    def apply_action(self, a, x, ctx, is_refund, only_action):
        acc_id = x.recv
        ef = exec_fee(a, acc_id)
        res = dict(gas_burnt=ef[0], gas_used=ef[0], compute=ef[1], ok=True, err=None, new=[], proposals=[],
                   tokens_burnt=0)

        def fail(e):
            res['ok'] = False
            res['err'] = e
            return res
        account = ctx['account']
        eligible = only_action and not is_refund
        t = a.tag
        # check_account_existence
        if t == A_CREATE:
            if account is not None:
                return fail('AccountAlreadyExists')
            if is_implicit(acc_id):
                return fail('OnlyImplicitAccountCreationAllowed')
        elif t == A_TRANSFER:
            if account is None and not (eligible and is_implicit(acc_id)):
                return fail('AccountDoesNotExist')
        elif account is None:
            return fail('AccountDoesNotExist')
        # check_actor_permissions
        if t in (A_DEPLOY, A_STAKE, A_ADDKEY, A_DELKEY, A_FROM_GK):
            if ctx['actor'] != acc_id:
                return fail('ActorNoPermission')
        elif t == A_DELACC:
            if ctx['actor'] != acc_id:
                return fail('ActorNoPermission')
            if account.locked != 0:
                return fail('DeleteAccountStaking')
        st = self.st
        if t == A_CREATE:
            if b'.' not in acc_id and acc_id != b'system':
                if len(acc_id) < MIN_TOP_LEVEL_LEN and x.pred != REGISTRAR:
                    return fail('CreateAccountOnlyByRegistrar')
            elif not is_sub_account_of(acc_id, x.pred):
                return fail('CreateAccountNotAllowed')
            ctx['actor'] = acc_id
            ctx['account'] = N.new_account(0, 0, ('none',), NUM_BYTES_ACCOUNT)
        elif t == A_DEPLOY:
            acc = account.copy()
            acc.su = max(acc.su - self.contract_storage(acc_id, acc), 0)
            code = a.f['code']
            acc.su += len(code)
            if acc.su > U64_MAX:
                raise Reject("storage usage overflow")
            acc.set_contract(('local', sha(code)))
            st.set(k_code(acc_id), code)
            ctx['account'] = acc
        elif t == A_TRANSFER:
            self.transfer(a.f['deposit'], x, ctx, is_refund)
        elif t == A_STAKE:
            acc = account.copy()
            stake = a.f['stake']
            increment = stake - acc.locked if stake > acc.locked else 0
            if acc.amount >= increment:
                if acc.locked == 0 and stake == 0:
                    return fail('TriesToUnstake')
                if stake > 0 and stake < self.minimum_stake:
                    return fail('InsufficientStake')
                res['proposals'].append((acc_id, a.f['pk'], stake))
                if stake > acc.locked:
                    acc.amount -= increment
                    acc.locked = stake
                ctx['account'] = acc
            else:
                return fail('TriesToStake')
        elif t == A_ADDKEY:
            pk, ak = a.f['pk'], a.f['ak']
            if st.get(k_ak(acc_id, pk)) is not None:
                return fail('AddKeyAlreadyExists')
            acc = account.copy()
            ak = ak.copy()
            init_nonce = (self.height - 1) * NONCE_RANGE
            if ak.is_gas_key():
                ak.nonce = 0
                st.set_ak(acc_id, pk, ak)
                for i in range(ak.gk_nonces):
                    st.set(k_gk_nonce(acc_id, pk, i), u64(init_nonce))
                cost = ak.gk_nonces * (pk_trie_len(pk) + 2 + 8 + NUM_EXTRA_BYTES_RECORD) + \
                    pk_trie_len(pk) + len(ak.encode()) + NUM_EXTRA_BYTES_RECORD
            else:
                ak.nonce = init_nonce
                st.set_ak(acc_id, pk, ak)
                cost = pk_trie_len(pk) + len(ak.encode()) + NUM_EXTRA_BYTES_RECORD
            acc.su += cost
            if acc.su > U64_MAX:
                raise Reject("storage usage overflow")
            ctx['account'] = acc
        elif t == A_DELKEY:
            pk = a.f['pk']
            ak = st.get_ak(acc_id, pk)
            if ak is None:
                return fail('DeleteKeyDoesNotExist')
            acc = account.copy()
            if ak.is_gas_key():
                if ak.gk_balance > GAS_KEY_MAX_BALANCE_TO_BURN:
                    return fail('GasKeyBalanceTooHigh')
                res['tokens_burnt'] = ak.gk_balance
                n = ak.gk_nonces
                for i in range(n):
                    st.remove(k_gk_nonce(acc_id, pk, i))
                nkl = ak_key_len(len(acc_id), pk_trie_len(pk)) + 2
                res['compute'] = cadd64(res['compute'], storage_removes_compute(n, nkl * n, 8 * n))
                st.remove(k_ak(acc_id, pk))
                cost = n * (pk_trie_len(pk) + 2 + 8 + NUM_EXTRA_BYTES_RECORD) + pk_trie_len(pk) + \
                    len(ak.encode()) + NUM_EXTRA_BYTES_RECORD
            else:
                cost = pk_trie_len(pk) + len(ak.encode()) + NUM_EXTRA_BYTES_RECORD
                st.remove(k_ak(acc_id, pk))
            acc.su = max(acc.su - cost, 0)
            ctx['account'] = acc
        elif t == A_DELACC:
            usage = max(account.su - self.contract_storage(acc_id, account), 0)
            if usage > MAX_ACCOUNT_DELETION_STORAGE_USAGE:
                return fail('DeleteAccountWithLargeState')
            burn_gk = self.gas_key_balance_sum(acc_id)
            if burn_gk > GAS_KEY_MAX_BALANCE_TO_BURN:
                return fail('GasKeyBalanceTooHigh')
            if account.amount > 0:
                res['new'].append(self.balance_refund(a.f['beneficiary'], account.amount))
            n_nonces, nonce_key_bytes = self.remove_account(acc_id)
            res['tokens_burnt'] = burn_gk
            if n_nonces > 0:
                res['compute'] = cadd64(res['compute'], storage_removes_compute(n_nonces, nonce_key_bytes, 8 * n_nonces))
            ctx['actor'] = x.pred
            ctx['account'] = None
        elif t in (A_DELEGATE, A_DELEGATE_V2):
            return self.delegate(a, x, res)
        elif t == A_TO_GK:
            ak = st.get_ak(acc_id, a.f['pk'])
            if ak is None or not ak.is_gas_key():
                return fail('GasKeyDoesNotExist')
            ak = ak.copy()
            ak.gk_balance += a.f['amount']
            if ak.gk_balance > U128_MAX:
                raise Reject("gas key balance overflow")
            st.set_ak(acc_id, a.f['pk'], ak)
        elif t == A_FROM_GK:
            ak = st.get_ak(acc_id, a.f['pk'])
            if ak is None or not ak.is_gas_key():
                return fail('GasKeyDoesNotExist')
            if ak.gk_balance < a.f['amount']:
                return fail('InsufficientGasKeyBalance')
            ak = ak.copy()
            ak.gk_balance -= a.f['amount']
            st.set_ak(acc_id, a.f['pk'], ak)
            acc = account.copy()
            acc.amount += a.f['amount']
            if acc.amount > U128_MAX:
                raise Reject("account balance overflow")
            ctx['account'] = acc
        else:
            raise OOD("r.exec: action %d executed" % t)
        return res

    def contract_storage(self, acc_id, acc):
        c = acc.contract
        if c[0] == 'none':
            return 0
        if c[0] == 'local':
            n = self.st.value_len(k_code(acc_id))
            return n if n is not None else 0
        return acc.identifier_storage_usage()

    def transfer(self, deposit, x, ctx, is_refund):
        st = self.st
        acc_id = x.recv
        account = ctx['account']
        if account is not None:
            is_gas_refund = is_refund and x.signer == acc_id
            if is_gas_refund:
                ak = st.get_ak(acc_id, x.pk)
                if ak is not None and ak.is_gas_key():
                    ak = ak.copy()
                    ak.gk_balance += deposit
                    if ak.gk_balance > U128_MAX:
                        raise Reject("gas key balance overflow")
                    st.set_ak(acc_id, x.pk, ak)
                    return
            acc = account.copy()
            acc.amount += deposit
            if acc.amount > U128_MAX:
                raise Reject("account balance overflow")
            ctx['account'] = acc
            if is_gas_refund:
                ak = st.get_ak(acc_id, x.pk)
                if ak is not None and ak.perm == 'fc' and ak.allowance is not None:
                    new = min(ak.allowance + deposit, U128_MAX)
                    if new > ak.allowance:
                        ak = ak.copy()
                        ak.allowance = new
                        st.set_ak(acc_id, x.pk, ak)
            return
        ctx['actor'] = acc_id
        t = account_type(acc_id)
        if t == 'near':
            ak = N.AK((self.height - 1) * NONCE_RANGE, 'full')
            pk = u8(0) + bytes.fromhex(acc_id.decode())
            su = NUM_BYTES_ACCOUNT + pk_trie_len(pk) + len(ak.encode()) + NUM_EXTRA_BYTES_RECORD
            ctx['account'] = N.new_account(deposit, 0, ('none',), su)
            st.set_ak(acc_id, pk, ak)
        elif t == 'eth':
            cid = self.chain_id
            h = ETH_WALLET_HASH['mainnet' if cid in (b'mainnet', b'mocknet') else
                                'testnet' if cid == b'testnet' else 'other']
            ctx['account'] = N.new_account(deposit, 0, ('global', h), NUM_BYTES_ACCOUNT + 32)
        else:
            ctx['account'] = N.new_account(deposit, 0, ('none',), NUM_BYTES_ACCOUNT)

    def access_key_entries(self, acc_id):
        """(raw key, key handle, nonce index or None) of the account's access-key prefix."""
        prefix = u8(C_ACCESS_KEY) + acc_id + u8(C_ACCESS_KEY)
        out = []
        for k in self.st.iter_prefix(prefix):
            rest = k[len(prefix):]
            if not rest or rest[0] not in N.PK_LEN:
                raise Reject("StorageInconsistentState: access key key")
            hl = 1 + N.PK_LEN[rest[0]]
            if len(rest) == hl:
                out.append((k, rest[:hl], None))
            elif len(rest) == hl + 2:
                out.append((k, rest[:hl], struct.unpack('<H', rest[hl:])[0]))
            else:
                raise Reject("StorageInconsistentState: access key key")
        return out

    def gas_key_balance_sum(self, acc_id):
        total = 0
        for k, handle, idx in self.access_key_entries(acc_id):
            if idx is not None:
                continue
            ak = self.st.get_ak(acc_id, handle)
            if ak is not None and ak.is_gas_key():
                total += ak.gk_balance
                if total > U128_MAX:
                    raise Reject("gas key balance overflow")
        return total

    def remove_account(self, acc_id):
        st = self.st
        st.remove(k_account(acc_id))
        st.remove(k_code(acc_id))
        n, kb = 0, 0
        for k, handle, idx in self.access_key_entries(acc_id):
            if idx is not None:
                n += 1
                kb += len(k)
            st.remove(k)
        prefix = u8(C_DATA) + acc_id + b','
        for k in self.st.iter_prefix(prefix):
            st.remove(k)
        return n, kb

    def delegate(self, a, x, res):
        st = self.st

        def fail(e):
            res['ok'] = False
            res['err'] = e
            return res
        f = a.f
        if not ed25519.verify(f['pk'][1:], f['sig'][1:], N.nep461_hash(a)):
            return fail('DelegateActionInvalidSignature')
        if self.height > f['max_block_height']:
            return fail('DelegateActionExpired')
        if f['sender'] != x.recv:
            return fail('DelegateActionSenderDoesNotMatchTxReceiver')
        sender, pk = f['sender'], f['pk']
        ak = st.get_ak(sender, pk)
        if ak is None:
            return fail('DelegateActionAccessKeyError')
        if f['nonce_index'] is None:
            if ak.is_gas_key():
                return fail('DelegateActionRequiresNonGasKey')
            current = ak.nonce
        else:
            if not ak.is_gas_key():
                return fail('DelegateActionRequiresGasKey')
            if f['nonce_index'] >= ak.gk_nonces:
                return fail('DelegateActionInvalidNonceIndex')
            current = st.get_u64(k_gk_nonce(sender, pk, f['nonce_index']))
            if current is None:
                raise Reject("StorageInconsistentState: gas key nonce row missing")
        if f['nonce'] <= current:
            return fail('DelegateActionInvalidNonce')
        upper = self.height * NONCE_RANGE
        if upper > U64_MAX:
            raise Reject("nonce upper bound overflow (panic)")
        if f['nonce'] >= upper:
            return fail('DelegateActionNonceTooLarge')
        if ak.has_fc():
            return fail('DelegateActionAccessKeyError')   # RequiresFullAccess: no FunctionCall in D2
        if f['nonce_index'] is None:
            ak = ak.copy()
            ak.nonce = f['nonce']
            st.set_ak(sender, pk, ak)
        else:
            st.set(k_gk_nonce(sender, pk, f['nonce_index']), u64(f['nonce']))
        y = N.new_action_receipt(sender, f['receiver'], ZERO32, x.signer, x.pk, x.gas_price, [], [], f['actions'])
        pse = total_prepaid_send_fees(x.actions)
        req = padd(total_prepaid_exec_fees(f['actions'], f['receiver']), (N.total_prepaid_gas(f['actions']), 0))
        req = padd(req, fee('new_action_receipt', 'exec'))
        res['gas_used'] = cadd64(cadd64(res['gas_used'], req[0]), pse[0])
        res['gas_burnt'] = cadd64(res['gas_burnt'], pse[0])
        res['compute'] = cadd64(res['compute'], pse[1])
        res['new'].append(y)
        return res

    # -------- yield timeouts (lib.rs:2986-3093)
    def resolve_yield_timeouts(self, limit):
        st = self.st
        idx = st.get_indices(u8(C_YIELD_INDICES))
        initial = list(idx)
        new_index = 0
        while idx[0] < idx[1]:
            if self.total_compute >= limit:
                break
            k = u8(C_YIELD_TIMEOUT) + u64(idx[0])
            v = st.get(k)
            if v is None:
                raise Reject("StorageInconsistentState: yield timeout entry missing")
            try:
                r = R(v)
                account, data_id, expires_at = r.account(), r.hash(), r.u64()
                r.end()
            except DecodeError:
                raise Reject("StorageInconsistentState: PromiseYieldTimeout")
            if expires_at > self.height:
                break
            if st.contains(k_acc_data(C_YIELD_RECEIPT, account, data_id)):
                rid = create_hash_index(data_id, self.height, new_index)
                new_index += 1
                self.forward_or_buffer(N.new_data_receipt(account, account, rid, data_id, None, kind=K_RESUME))
            st.remove(k)
            idx[0] += 1
        return initial, idx


def storage_removes_compute(count, key_bytes, value_bytes):
    return EXT_REMOVE_BASE_C * count + EXT_REMOVE_KEY_BYTE_C * key_bytes + EXT_REMOVE_VALUE_BYTE_C * value_bytes


def is_sub_account_of(a, parent):
    if not a.endswith(parent):
        return False
    s = a[:len(a) - len(parent)]
    if not s.endswith(b'.'):
        return False
    return b'.' not in s[:-1]


def validator_accounts_update(st, L, s0, vu, last_proposals):
    """lib.rs update_validator_accounts with the claim's facts filtered to the shard."""
    stake_info, rewards, treasury = vu
    on = lambda a: s3.account_to_shard(L, a) == s0  # noqa: E731
    stake_info = [(a, v) for a, v in stake_info if on(a)]
    rewards = {a: v for a, v in rewards if on(a)}
    lp = {}
    for a, _pk, s in last_proposals:
        if on(a):
            lp[a] = s
    for a, max_of_stakes in stake_info:
        acc = st.get_account(a)
        if acc is not None:
            acc = acc.copy()
            if a in rewards:
                acc.locked += rewards[a]
                if acc.locked > U128_MAX:
                    raise Reject("update_validator_accounts overflow")
            if acc.locked < max_of_stakes:
                raise Reject("StorageInconsistentState: staking invariant")
            ret = acc.locked - max(max_of_stakes, lp.get(a, 0))
            if ret < 0:
                raise Reject("update_validator_accounts: return stake underflow")
            acc.locked -= ret
            acc.amount += ret
            if acc.amount > U128_MAX:
                raise Reject("update_validator_accounts overflow")
            st.set_account(a, acc)
        elif max_of_stakes > 0:
            raise Reject("StorageInconsistentState: validator account missing")
    if treasury is not None and on(treasury) and treasury not in dict(stake_info):
        acc = st.get_account(treasury)
        if acc is None:
            raise Reject("StorageInconsistentState: protocol treasury missing")
        if treasury not in rewards:
            raise Reject("StorageInconsistentState: treasury reward missing")
        acc = acc.copy()
        acc.amount += rewards[treasury]
        if acc.amount > U128_MAX:
            raise Reject("update_validator_accounts overflow")
        st.set_account(treasury, acc)
    st.commit()


def scheduler_step(st, L, blk):
    v = st.get(u8(C_BW_STATE))
    prev = None
    if v is not None:
        try:
            prev = sched.decode_state(v)
        except DecodeError:
            raise OOD("e.scheduler_state: 0x0f does not decode as BandwidthSchedulerState::V1")
    new_state, grants = sched.run(L, prev, s3.ctx_congestion(blk), s3.ctx_bw_requests(blk), blk.prev_hash)
    st.set(u8(C_BW_STATE), new_state)
    return grants


def make_bw_request(to_shard, sizes, base):
    values = sched.request_values(base)
    bitmap = 0
    total = 0
    cur = 0
    for s in sizes:
        total += s
        if total <= base:
            continue
        while cur < len(values) and values[cur] < total:
            cur += 1
        if cur == len(values):
            break
        bitmap |= 1 << cur
    if bitmap == 0:
        return None
    return (to_shard, bitmap.to_bytes(5, 'little'))


# ---------------------------------------------------------------------------------------------
# the D2 relation
# ---------------------------------------------------------------------------------------------
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
    if len(sw) > D_MAX_WITNESS:
        raise OOD("w.size: state witness larger than 8 MiB")
    W = decode_state_witness_d2(sw)

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
            st_, rw, _tr = af['validator_update']
            s3.check_sorted_accounts(st_)
            s3.check_sorted_accounts(rw)
    if W['epoch_id'] != c['epoch_id']:
        raise Reject("witness epoch_id != claim epoch_id")
    if W['inner'].raw != c['chunk_inner']:
        raise Reject("witness chunk header inner != claim chunk_inner")

    # ---- claim-level D2 conditions
    if c['pv'] != 86 or any(e['pv'] != 86 for e in eps):
        raise OOD("c.pv86")
    layout_raw = epmap[c['epoch_id']]['layout_raw']
    if any(e['layout_raw'] != layout_raw for e in eps):
        raise OOD("c.same_layout: the claim's epochs have different shard layouts")
    L = s3.decode_layout(layout_raw)
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
    for t in W['new_txs']:
        if len(t.raw) > MAX_TRANSACTION_SIZE:
            raise Reject("new transaction exceeds max_transaction_size")

    # ---- backward walk
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
    b2_genesis = B2.prev_hash == ZERO32
    if len(c['apply_facts']) != (0 if b2_genesis else 1) + len(implicit_idx):
        raise Reject("claim: apply_facts count")
    applied = ([] if b2_genesis else [b2i]) + list(reversed(implicit_idx))
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
        raise OOD("c.own_congestion: no congestion info for own shard (bootstrap)")
    own_info = cong_b2[s0][0]
    base_bytes = sum(len(v) for v in W['main']['base_state'])
    if base_bytes > D_MAX_BASE_STATE:
        raise OOD("w.size: main base_state > 3 000 000 bytes")

    # ---- source receipt proofs
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

    # ---- main transition
    height = B2.height
    gas_price = blocks[b2i + 1].rest['next_gas_price']
    trie = Trie2(W['main']['base_state'], own_slot.inner.prev_state_root)
    st = State(trie)
    facts = c['apply_facts'][0]
    if facts['validator_update'] is not None:
        validator_accounts_update(st, L, s0, facts['validator_update'], own_slot.inner.prev_validator_proposals)
    A = Apply(st, L, s0, height, gas_price, own_slot.inner.gas_limit, facts['minimum_stake'], c['chain_id'], None)
    A.delayed_init()
    grants = scheduler_step(st, L, B2)
    A.sink_init(own_info, cong_b2, grants)
    A.forward_from_buffers()
    A.process_transactions(txs, c['tx_valid'])
    ids = [x.rid for x in A.local] + [x.rid for x in R_list]
    if len(set(ids)) != len(ids):
        raise OOD("e.distinct_ids")
    A.incoming = R_list
    A.process_receipts()
    if base_bytes + 2000 * st.data_removals > PROOF_SOFT_LIMIT:
        raise OOD("e.proof_limit")
    # validate_apply_state_update
    yinit, yidx = A.yield_indices
    if yidx != yinit:
        st.set(u8(C_YIELD_INDICES), u64(yidx[0]) + u64(yidx[1]))
    own = A.own
    try:
        own[0] = cadd128(own[0], A.dq_new_gas)
        if own[0] < A.dq_rm_gas:
            raise Reject("delayed gas underflow")
        own[0] -= A.dq_rm_gas
        own[2] = cadd64(own[2], A.dq_new_bytes)
        if own[2] < A.dq_rm_bytes:
            raise Reject("receipt bytes underflow")
        own[2] -= A.dq_rm_bytes
    except Overflow:
        raise Reject("congestion info overflow")
    allowed = L.shard_ids[((height + idx) & U64_MAX) % ns]
    congestion = (own[0], own[1], own[2], allowed)
    base_bw = sched.params(ns)
    bw = []
    for sid in L.shard_ids:
        b = A.buffers.get(sid)
        blen = (b[1] - b[0]) if b else 0
        if blen == 0:
            continue
        m = A.metas.get(sid)
        if m is not None and m['num'] == blen:
            sizes = [min(A.get_group(sid, gi)[0], MAX_RECEIPT_SIZE) for gi in range(m['first'], m['next'])]
        else:
            sizes = [MAX_RECEIPT_SIZE]
        req = make_bw_request(sid, sizes, base_bw)
        if req is not None:
            bw.append(req)
    st.commit()
    state_root = st.finalize()
    if state_root != W['main']['post_state_root']:
        raise Reject("main transition post_state_root mismatch")
    outcome_root = merkle_root_of_hashes(A.leaves)
    uniq = []
    seen_acc = set()
    for p in reversed(A.proposals):
        if p[0] not in seen_acc:
            seen_acc.add(p[0])
            uniq.append(p)
    try:
        balance_burnt = cadd128(A.tx_burnt, A.other_burnt)
    except Overflow:
        raise Reject("burnt balance overflow")
    gas_used = A.total_gas

    # ---- implicit transitions (missing chunks): validator update, delayed indices read, scheduler
    imp = list(reversed(implicit_idx))
    if len(imp) != len(W['implicit']):
        raise Reject("implicit transitions count mismatch")
    for k, (bi_, T) in enumerate(zip(imp, W['implicit'])):
        M = blocks[bi_]
        t2 = Trie2(T['base_state'], state_root)
        st2 = State(t2)
        af = c['apply_facts'][1 + k]
        if af['validator_update'] is not None:
            validator_accounts_update(st2, L, s0, af['validator_update'], uniq)
        st2.get_indices(u8(C_DELAYED))
        scheduler_step(st2, L, M)
        st2.commit()
        state_root = st2.finalize()
        if state_root != T['post_state_root']:
            raise Reject("implicit transition post_state_root mismatch")

    # ---- comparison with the endorsed header
    if H.prev_state_root != state_root:
        raise Reject("InvalidStateRoot")
    if H.prev_outcome_root != outcome_root:
        raise Reject("InvalidOutcomesProof")
    if list(H.prev_validator_proposals) != uniq:
        raise Reject("InvalidValidatorProposals")
    if H.gas_limit != own_slot.inner.gas_limit:
        raise Reject("InvalidGasLimit")
    if H.prev_gas_used != gas_used:
        raise Reject("InvalidGasUsed")
    if H.prev_balance_burnt != balance_burnt:
        raise Reject("InvalidBalanceBurnt")
    by_shard = {sid: [] for sid in L.shard_ids}
    for x in A.outgoing:
        by_shard[s3.account_to_shard(L, x.recv)].append(x.raw)
    rh = [sha(sha(u64(sid) + u32(len(by_shard[sid])) + b''.join(by_shard[sid]))) for sid in L.shard_ids]
    if H.prev_outgoing_receipts_root != merkle_root_of_hashes(rh):
        raise Reject("InvalidReceiptsProof")
    if H.congestion_info != congestion:
        raise Reject("InvalidCongestionInfo")
    if H.bandwidth_requests != bw:
        raise Reject("InvalidBandwidthRequests")
    if H.proposed_split is not None:
        raise Reject("InvalidChunkHeaderShardSplit")
    if H.tx_root != merklize([t.raw for t in W['new_txs']]):
        raise Reject("InvalidTxRoot")
    body = (u32(len(W['new_txs'])) + b''.join(t.raw for t in W['new_txs']) +
            u32(len(A.outgoing)) + b''.join(x.raw for x in A.outgoing))
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
        import traceback
        print("spec_check_v3_d2: INTERNAL ERROR on %s: %r\n%s" % (d, e, traceback.format_exc()), file=sys.stderr)
        return "reject", "INTERNAL ERROR %s: %s" % (type(e).__name__, e)


def main():
    for d in sys.argv[1:]:
        v, reason = check_case(d)
        print(json.dumps(dict(case=d, verdict=v, reason=reason)))
        sys.stdout.flush()


if __name__ == "__main__":
    main()
