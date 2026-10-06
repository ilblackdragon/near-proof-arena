"""nearcore 2.13.4 borsh types read and written by the domain-D2 checker: actions (every
variant), access keys, accounts (V1 and the V2 sentinel encoding), transactions, receipts
(Action / Data / PromiseYield / PromiseResume / ActionV2 / PromiseYieldV2), state-stored
receipts, queue indices, receipt groups, yield timeouts. Written from
core/primitives/src/{action/mod.rs, action/delegate.rs, receipt.rs, transaction.rs},
core/primitives-core/src/account.rs and core/store/src/trie/{receipts_column_helper.rs,
outgoing_metadata.rs}. Nothing here is derived from the Lean formalization."""
import hashlib

from .prim import R, Reject, OOD, DecodeError, u8, u16, u32, u64, u128, bstr, U128_MAX, ZERO32

PK_LEN = {0: 32, 1: 64, 2: 1952}
SIG_LEN = {0: 64, 1: 65, 2: 3309}

A_CREATE, A_DEPLOY, A_FC, A_TRANSFER, A_STAKE, A_ADDKEY, A_DELKEY, A_DELACC, A_DELEGATE, \
    A_DEPLOY_GLOBAL, A_USE_GLOBAL, A_DSI, A_TO_GK, A_FROM_GK, A_DELEGATE_V2 = range(15)
ACTION_NAMES = ["CreateAccount", "DeployContract", "FunctionCall", "Transfer", "Stake", "AddKey",
                "DeleteKey", "DeleteAccount", "Delegate", "DeployGlobalContract", "UseGlobalContract",
                "DeterministicStateInit", "TransferToGasKey", "WithdrawFromGasKey", "DelegateV2"]


def read_pk(r):
    t = r.u8()
    if t not in PK_LEN:
        raise DecodeError("PublicKey tag")
    b = u8(t) + r.take(PK_LEN[t])
    if t == 2:
        raise OOD("w.shape: ML-DSA-65 public key in a transaction or receipt")
    return b


def read_sig(r):
    t = r.u8()
    if t not in SIG_LEN:
        raise DecodeError("Signature tag")
    s = r.take(SIG_LEN[t])
    if t == 2:
        raise OOD("w.shape: ML-DSA-65 signature")
    if t == 0 and s[63] & 0xE0:
        raise DecodeError("ed25519 signature high bits")
    return u8(t) + s


def read_string(r):
    s = r.bytes()
    try:
        s.decode('utf-8', 'strict')
    except UnicodeDecodeError:
        raise DecodeError("invalid UTF-8")
    return s


# ---------------------------------------------------------------- access keys
class AK:
    """AccessKey: nonce, perm in {'fc','full','gfc','gfull'}, allowance (None|int),
    receiver (bytes), methods (list of bytes), gk_balance, gk_nonces."""
    __slots__ = ('nonce', 'perm', 'allowance', 'receiver', 'methods', 'gk_balance', 'gk_nonces')

    def __init__(self, nonce, perm, allowance=None, receiver=b'', methods=(), gk_balance=0, gk_nonces=0):
        self.nonce, self.perm, self.allowance, self.receiver = nonce, perm, allowance, receiver
        self.methods, self.gk_balance, self.gk_nonces = list(methods), gk_balance, gk_nonces

    def copy(self):
        return AK(self.nonce, self.perm, self.allowance, self.receiver, self.methods, self.gk_balance, self.gk_nonces)

    def is_gas_key(self):
        return self.perm in ('gfc', 'gfull')

    def has_fc(self):
        return self.perm in ('fc', 'gfc')

    def encode(self):
        out = u64(self.nonce)

        def fcp():
            return ((u8(1) + u128(self.allowance)) if self.allowance is not None else u8(0)) + \
                bstr(self.receiver) + u32(len(self.methods)) + b''.join(bstr(m) for m in self.methods)
        if self.perm == 'fc':
            return out + u8(0) + fcp()
        if self.perm == 'full':
            return out + u8(1)
        if self.perm == 'gfc':
            return out + u8(2) + u128(self.gk_balance) + u16(self.gk_nonces) + fcp()
        return out + u8(3) + u128(self.gk_balance) + u16(self.gk_nonces)


def read_ak(r):
    nonce = r.u64()
    tag = r.u8()

    def fcp():
        al = r.u128() if r.option(lambda: True) else None
        recv = read_string(r)
        methods = r.vec(lambda: read_string(r))
        return al, recv, methods
    if tag == 0:
        al, recv, ms = fcp()
        return AK(nonce, 'fc', al, recv, ms)
    if tag == 1:
        return AK(nonce, 'full')
    if tag == 2:
        bal, nn = r.u128(), r.u16()
        al, recv, ms = fcp()
        return AK(nonce, 'gfc', al, recv, ms, bal, nn)
    if tag == 3:
        bal, nn = r.u128(), r.u16()
        return AK(nonce, 'gfull', gk_balance=bal, gk_nonces=nn)
    raise DecodeError("AccessKeyPermission tag")


def decode_ak(v):
    try:
        r = R(v)
        a = read_ak(r)
        r.end()
        return a
    except DecodeError:
        raise Reject("StorageInconsistentState: access key does not decode")


# ---------------------------------------------------------------- accounts
class Account:
    """v: 1|2; contract: ('none',) | ('local', hash) | ('global', hash) | ('global_by', account)."""
    __slots__ = ('v', 'amount', 'locked', 'su', 'contract')

    def __init__(self, v, amount, locked, su, contract):
        self.v, self.amount, self.locked, self.su, self.contract = v, amount, locked, su, contract

    def copy(self):
        return Account(self.v, self.amount, self.locked, self.su, self.contract)

    def encode(self):
        if self.v == 1:
            ch = self.contract[1] if self.contract[0] == 'local' else ZERO32
            return u128(self.amount) + u128(self.locked) + ch + u64(self.su)
        c = self.contract
        cb = {'none': lambda: u8(0), 'local': lambda: u8(1) + c[1], 'global': lambda: u8(2) + c[1],
              'global_by': lambda: u8(3) + bstr(c[1])}[c[0]]()
        return u128(U128_MAX) + u8(0) + u128(self.amount) + u128(self.locked) + u64(self.su) + cb

    def set_contract(self, contract):
        # Account::set_contract (account.rs): a V1 account stays V1 for None/Local
        if self.v == 1 and contract[0] not in ('none', 'local'):
            self.v = 2
        self.contract = contract

    def identifier_storage_usage(self):
        c = self.contract
        return 32 if c[0] == 'global' else (len(c[1]) if c[0] == 'global_by' else 0)


def new_account(amount, locked, contract, su):
    """Account::new: V1 for None/Local, V2 otherwise."""
    return Account(1 if contract[0] in ('none', 'local') else 2, amount, locked, su, contract)


def decode_account(v):
    try:
        r = R(v)
        a = r.u128()
        if a == U128_MAX:
            if r.u8() != 0:
                raise DecodeError("BorshVersionedAccount tag")
            amount, locked, su = r.u128(), r.u128(), r.u64()
            t = r.u8()
            if t == 0:
                c = ('none',)
            elif t == 1:
                c = ('local', r.hash())
            elif t == 2:
                c = ('global', r.hash())
            elif t == 3:
                c = ('global_by', r.account())
            else:
                raise DecodeError("AccountContract tag")
            r.end()
            return Account(2, amount, locked, su, c)
        locked, ch, su = r.u128(), r.hash(), r.u64()
        r.end()
        return Account(1, a, locked, su, ('none',) if ch == ZERO32 else ('local', ch))
    except DecodeError:
        raise Reject("StorageInconsistentState: account does not decode")


# ---------------------------------------------------------------- actions
class Action:
    __slots__ = ('tag', 'raw', 'f')

    def __init__(self, tag, raw, f):
        self.tag, self.raw, self.f = tag, raw, f


def read_tx_nonce(r):
    t = r.u8()
    if t == 0:
        return r.u64(), None
    if t == 1:
        return r.u64(), r.u16()
    raise DecodeError("TransactionNonce tag")


def read_action(r, nested=False):
    start = r.i
    t = r.u8()
    f = {}
    if t == A_CREATE:
        pass
    elif t == A_DEPLOY:
        f['code'] = r.bytes()
    elif t == A_FC:
        f['method'] = read_string(r)
        f['args'] = r.bytes()
        f['gas'] = r.u64()
        f['deposit'] = r.u128()
    elif t == A_TRANSFER:
        f['deposit'] = r.u128()
    elif t == A_STAKE:
        f['stake'] = r.u128()
        f['pk'] = read_pk(r)
    elif t == A_ADDKEY:
        f['pk'] = read_pk(r)
        s = r.i
        f['ak'] = read_ak(r)
        f['ak_raw'] = r.b[s:r.i]
    elif t == A_DELKEY:
        f['pk'] = read_pk(r)
    elif t == A_DELACC:
        f['beneficiary'] = r.account()
    elif t in (A_DELEGATE, A_DELEGATE_V2):
        if nested:
            raise DecodeError("nested delegate action")
        ps = r.i
        if t == A_DELEGATE_V2:
            if r.u8() != 0:
                raise DecodeError("VersionedDelegateActionPayload tag")
        f['sender'] = r.account()
        f['receiver'] = r.account()
        f['actions'] = r.vec(lambda: read_action(r, nested=True))
        if t == A_DELEGATE:
            f['nonce'], f['nonce_index'] = r.u64(), None
        else:
            f['nonce'], f['nonce_index'] = read_tx_nonce(r)
        f['max_block_height'] = r.u64()
        f['pk'] = read_pk(r)
        f['payload'] = r.b[ps:r.i]
        f['sig'] = read_sig(r)
    elif t == A_DEPLOY_GLOBAL:
        f['code'] = r.bytes()
        m = r.u8()
        if m > 1:
            raise DecodeError("GlobalContractDeployMode tag")
        raise OOD("w.shape: DeployGlobalContract action")
    elif t == A_USE_GLOBAL:
        raise OOD("w.shape: UseGlobalContract action")
    elif t == A_DSI:
        raise OOD("w.shape: DeterministicStateInit action")
    elif t in (A_TO_GK, A_FROM_GK):
        f['pk'] = read_pk(r)
        f['amount'] = r.u128()
    else:
        raise DecodeError("Action tag %d" % t)
    return Action(t, r.b[start:r.i], f)


def read_actions(r):
    return r.vec(lambda: read_action(r))


def deposit_of(a):
    """Action::get_deposit_balance."""
    if a.tag in (A_TRANSFER, A_FC):
        return a.f['deposit']
    if a.tag == A_TO_GK:
        return a.f['amount']
    return 0


def total_deposit(actions):
    """config.rs total_deposit (delegate: the inner actions' deposits)."""
    t = 0
    for a in actions:
        if a.tag in (A_DELEGATE, A_DELEGATE_V2):
            t += total_deposit(a.f['actions'])
        else:
            t += deposit_of(a)
    return t


def total_prepaid_gas(actions):
    t = 0
    for a in actions:
        if a.tag in (A_DELEGATE, A_DELEGATE_V2):
            t += total_prepaid_gas(a.f['actions'])
        elif a.tag == A_FC:
            t += a.f['gas']
    return t


def nep461_hash(a):
    """SignableMessage(discriminant 2^30 + NEP, payload) — signable_message.rs."""
    nep = 366 if a.tag == A_DELEGATE else 611
    return hashlib.sha256(u32((1 << 30) + nep) + a.f['payload']).digest()


# ---------------------------------------------------------------- transactions
class Tx:
    pass


def read_tx(r):
    start = r.i
    if r.i + 2 > len(r.b):
        raise DecodeError("transaction version bytes")
    b1, b2 = r.b[r.i], r.b[r.i + 1]
    if b2 == 0:
        v1 = False
    elif b1 == 1:
        v1 = True
        r.i += 1
    else:
        raise DecodeError("invalid transaction version tag %d" % b1)
    t = Tx()
    t.v1 = v1
    t.signer = r.account()
    t.pk = read_pk(r)
    if v1:
        t.nonce, t.nonce_index = read_tx_nonce(r)
    else:
        t.nonce, t.nonce_index = r.u64(), None
    t.recv = r.account()
    t.block_hash = r.hash()
    t.actions = read_actions(r)
    t.strict = False
    if v1:
        m = r.u8()
        if m not in (0, 1):
            raise DecodeError("NonceMode tag")
        t.strict = m == 1
    t.body = r.b[start:r.i]
    t.sig = read_sig(r)
    t.raw = r.b[start:r.i]
    t.hash = hashlib.sha256(t.body).digest()
    return t


# ---------------------------------------------------------------- receipts
K_ACTION, K_DATA, K_YIELD, K_RESUME, K_GCD, K_ACTION_V2, K_YIELD_V2 = range(7)


class Receipt:
    """kind: 0..6 (ReceiptEnum). Action kinds: signer, pk, gas_price, outputs [(data_id, recv)],
    inputs [data_id], actions [Action], refund_to (V2). Data kinds: data_id, data (None|bytes)."""
    __slots__ = ('pred', 'recv', 'rid', 'kind', 'signer', 'pk', 'gas_price', 'outputs', 'inputs',
                 'actions', 'refund_to', 'data_id', 'data', 'raw')

    def is_action(self):
        return self.kind in (K_ACTION, K_YIELD, K_ACTION_V2, K_YIELD_V2)

    def encode(self):
        out = bstr(self.pred) + bstr(self.recv) + self.rid + u8(self.kind)
        if self.is_action():
            out += bstr(self.signer)
            if self.kind in (K_ACTION_V2, K_YIELD_V2):
                out += (u8(1) + bstr(self.refund_to)) if self.refund_to is not None else u8(0)
            out += self.pk + u128(self.gas_price)
            out += u32(len(self.outputs)) + b''.join(d + bstr(rc) for d, rc in self.outputs)
            out += u32(len(self.inputs)) + b''.join(self.inputs)
            out += u32(len(self.actions)) + b''.join(a.raw for a in self.actions)
        else:
            out += self.data_id + ((u8(1) + bstr(self.data)) if self.data is not None else u8(0))
        return out


def read_receipt(r):
    start = r.i
    x = Receipt()
    x.pred = r.account()
    x.recv = r.account()
    x.rid = r.hash()
    x.kind = r.u8()
    x.refund_to = None
    if x.kind in (K_ACTION, K_YIELD, K_ACTION_V2, K_YIELD_V2):
        x.signer = r.account()
        if x.kind in (K_ACTION_V2, K_YIELD_V2):
            x.refund_to = r.option(r.account)
        x.pk = read_pk(r)
        x.gas_price = r.u128()
        x.outputs = r.vec(lambda: (r.hash(), r.account()))
        x.inputs = r.vec(r.hash)
        x.actions = read_actions(r)
    elif x.kind in (K_DATA, K_RESUME):
        x.data_id = r.hash()
        x.data = r.option(r.bytes)
    elif x.kind == K_GCD:
        raise OOD("w.shape: GlobalContractDistribution receipt")
    else:
        raise DecodeError("ReceiptEnum tag")
    x.raw = r.b[start:r.i]
    return x


def decode_receipt(v):
    r = R(v)
    x = read_receipt(r)
    r.end()
    return x


def new_action_receipt(pred, recv, rid, signer, pk, gas_price, outputs, inputs, actions, kind=K_ACTION, refund_to=None):
    x = Receipt()
    x.pred, x.recv, x.rid, x.kind = pred, recv, rid, kind
    x.signer, x.pk, x.gas_price, x.outputs, x.inputs, x.actions = signer, pk, gas_price, outputs, inputs, actions
    x.refund_to = refund_to
    x.raw = x.encode()
    return x


def new_data_receipt(pred, recv, rid, data_id, data, kind=K_DATA):
    x = Receipt()
    x.pred, x.recv, x.rid, x.kind, x.data_id, x.data, x.refund_to = pred, recv, rid, kind, data_id, data, None
    x.raw = x.encode()
    return x


def with_rid(x, rid):
    y = Receipt()
    for s in Receipt.__slots__:
        setattr(y, s, getattr(x, s, None))
    y.rid = rid
    y.raw = y.encode()
    return y


def decode_stored_receipt(v):
    """ReceiptOrStateStoredReceipt: (receipt, metadata (gas, size) or None, v1?)."""
    try:
        if len(v) >= 2 and v[0] == 0xFF and v[1] == 0xFF:
            r = R(v, 2)
            ver = r.u8()
            if ver not in (0, 1):
                raise DecodeError("StateStoredReceipt version")
            x = read_receipt(r)
            gas, size = r.u64(), r.u64()
            r.end()
            return x, (gas, size), ver == 1
        return decode_receipt(v), None, False
    except DecodeError:
        raise Reject("StorageInconsistentState: stored receipt does not decode")


def encode_state_stored(x, gas, size):
    return b'\xff\xff' + u8(1) + x.raw + u64(gas) + u64(size)
