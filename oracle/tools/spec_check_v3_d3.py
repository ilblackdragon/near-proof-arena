#!/usr/bin/env python3
"""Independent Python reference checker for near/pv86/chunk-validation/v0, domain D3-alpha
(D2 + WASM FunctionCall actions on accounts without a contract or with a local contract).

`Rel_D3a` is the D2 relation (spec_check_v3_d2.py) with:
  * `w.no_code` lifted: the contract-code blobs appended to witness.bin (spec/claim-v3.md section 3,
    oracle/v3/src/enc.rs) join the main transition's recorded values, and every trie read uses the
    merged list `base_state ++ codes` (chunk_validation.rs / partial_witness_tracker.rs:693-696);
  * FunctionCall executed as nearcore 2.13.4 does it (spec/near-chunk-validation-d3.md sections 1-7):
    code lookup with cold-cache semantics (section 2.2: deploy tracker, then the merged values,
    otherwise MissingTrieValue = reject), the VMContext (section 3), VMOutcome -> ActionResult
    (section 4), the ReceiptManager receipts with real data ids, gas weights and yields (section 5),
    merge / receiver reward / output data / status / logs (section 6) and the outcome bytes (section 7);
  * the D3-alpha domain conditions (section 10, 10.0): floats, curve host functions, the state-init,
    global-contract and gas-key host functions, global-contract accounts out of domain;
    `e.code_cache`: an executed pre-state contract whose code blob is absent from the witness while
    the same code was deployed earlier in the chunk (committed or rolled back) is out of domain;
    `e.g_alpha`: chunk sum of gas_burnt_for_function_call > 2^22 * 822,756 is out of domain;
    D2's conditions otherwise (w.size sums the merged list).

WASM execution, host functions and the trie-node cost model are the clean-room implementation
oracle/wasm-d3/cleanroom/ (nearwasm.py, nearstore.py, nearcrypto.py), driven here with nearcore's
real `External` (runtime/runtime/src/{ext.rs, receipt_manager.rs, function_call.rs}) instead of the
harness's MockedExternal. Nothing here is derived from the Lean formalization.

Usage:
  spec_check_v3_d3.py CASE_DIR...      one JSON line per case:
                                       {"case", "verdict": accept|reject|out_of_domain, "reason"}
  spec_check_v3_d3.py --list FILE      case directories from FILE (one per line), same output
"""
import json
import os
import struct
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "wasm-d3", "cleanroom"))

import spec_check_v3 as s3  # noqa: E402
import spec_check_v3_d2 as D2  # noqa: E402
from spec_check_v3_d2 import (  # noqa: E402
    Overflow, cadd64, cadd128, cmul128, fee, k_acc_data, k_account, validate_receipt, storage_stake_ok,
    create_hash_index, partial_outcome, C_RECEIVED_DATA, C_YIELD_INDICES, C_YIELD_TIMEOUT, C_YIELD_RECEIPT,
    C_YIELD_STATUS, C_YIELD_TO_DATA, C_DATA_TO_YIELD, C_DATA, C_DELAYED)
from v3lib.prim import (  # noqa: E402
    R, Reject, OOD, DecodeError, sha, u8, u32, u64, u128, bstr, U64_MAX, U128_MAX, ZERO32,
    merklize, merkle_root_of_hashes, compute_root_from_path, ChaCha20Rng, encoded_merkle_root,
    is_eth_implicit, nibbles)
from v3lib import sched  # noqa: E402
from v3lib.trie2 import Trie2  # noqa: E402
from v3lib import near2 as N  # noqa: E402
from v3lib.near2 import (  # noqa: E402
    A_CREATE, A_DEPLOY, A_FC, A_TRANSFER, A_STAKE, A_ADDKEY, A_DELKEY, A_DELACC, K_RESUME,
    K_ACTION_V2, K_YIELD_V2)

import nearwasm as W  # noqa: E402
import nearstore as NS  # noqa: E402

G_ALPHA = (1 << 22) * 822_756               # D3.gAlpha (section 10.0 decision 3)
# Resource bound of this checker only: the chunk's function-call gas at which execution stops
# (out of domain: far above G_alpha, so it never decides an in-domain case).
HARD_CAP = int(os.environ.get("D3_PY_HARD_CAP", str(2 * 10 ** 15)))
BURNT_GAS_REWARD = (3, 10)                  # parameters.yaml burnt_gas_reward
YIELD_TIMEOUT_LENGTH = 200                  # parameters.yaml yield_timeout_length_in_blocks


class CapExceeded(Exception):
    """The chunk's function-call gas passed G_alpha during a call (e.g_alpha)."""


# =============================================================================================
# The VM gas counter with a cap on burnt gas (so that a call that would push the chunk's
# function-call gas over G_alpha stops early).  Semantics are those of nearwasm.GasCounter; the
# cap only lowers the wasm-side copy of the remaining gas, and every sync recovers `burnt` from
# the value of that copy at the previous sync.
# =============================================================================================
class CappedGas(W.GasCounter):
    __slots__ = ("cap", "gsync", "bsync")

    def __init__(self, prepaid, cap):
        super().__init__(prepaid)
        self.cap = cap
        self.gsync = None
        self.bsync = 0

    def remaining(self):
        g = self.prepaid - self.burnt - self.promises
        c = self.cap - self.burnt
        if c < g:
            g = max(c, 0)
        self.gsync, self.bsync = g, self.burnt
        return g

    def burnt_at(self, g):
        return self.bsync + (self.gsync - g)


def _fail_gas(inst, a):
    gc = inst.gc
    gc.burnt = gc.burnt_at(inst.g)
    if a <= gc.prepaid - gc.promises - gc.burnt and gc.burnt + a <= gc.limit:
        raise CapExceeded()
    try:
        gc.burn(a)
    except W.HostErr as e:
        e.synced = True
        inst.g = gc.remaining()
        raise
    raise W.Unmodeled("charge point unexpectedly succeeded")


def _host_call(inst, f, args):
    gc = inst.gc
    gc.burnt = gc.burnt_at(inst.g)
    try:
        res = W.host_dispatch(inst, f.imp_name, args)
    except Exception as e:
        e.synced = True
        inst.g = gc.remaining()
        raise
    if gc.burnt > gc.cap:
        raise CapExceeded()
    inst.g = gc.remaining()
    return res


W.fail_gas = _fail_gas
W.host_call = _host_call


# =============================================================================================
# The real External (ext.rs) and ReceiptManager (receipt_manager.rs) behind the clean-room host
# functions.  nearwasm's host functions call `create_receipt`, `append_action` and `new_data_id`
# through module globals; these are replaced here.  The functions whose External behaviour
# differs from MockedExternal (yields, refund_to, the 1-yocto subsidy accounting, context
# getters, current_contract_code, validator stake) are re-implemented with the clean-room's
# charge order (README H12-H14, D11) and nearcore's External effects.
# =============================================================================================
class MAct:
    """A VM-created action: tag + fields; FunctionCall gas may still change (gas weights)."""
    __slots__ = ("tag", "f")

    def __init__(self, tag, f):
        self.tag, self.f = tag, f

    def to_action(self):
        t, f = self.tag, self.f
        if t == A_CREATE:
            raw = u8(A_CREATE)
        elif t == A_DEPLOY:
            raw = u8(A_DEPLOY) + bstr(f['code'])
        elif t == A_FC:
            raw = u8(A_FC) + bstr(f['method']) + bstr(f['args']) + u64(f['gas']) + u128(f['deposit'])
        elif t == A_TRANSFER:
            raw = u8(A_TRANSFER) + u128(f['deposit'])
        elif t == A_STAKE:
            raw = u8(A_STAKE) + u128(f['stake']) + f['pk']
        elif t == A_ADDKEY:
            f['ak_raw'] = f['ak'].encode()
            raw = u8(A_ADDKEY) + f['pk'] + f['ak_raw']
        elif t == A_DELKEY:
            raw = u8(A_DELKEY) + f['pk']
        elif t == A_DELACC:
            raw = u8(A_DELACC) + bstr(f['beneficiary'])
        else:
            raise AssertionError(t)
        return N.Action(t, raw, dict(f))


def _vm_pk(hexs):
    pk = bytes.fromhex(hexs)
    if pk[0] == 2:
        raise W.OutOfDomain("w.shape: ML-DSA-65 key in a VM-created action")
    return pk


def _utf8_or_invalid(b):
    try:
        b.decode("utf-8")
    except UnicodeDecodeError:
        raise W.HostErr("InvalidMethodName")
    return b


def ext_new_data_id(inst):
    """ext.rs generate_data_id: create_receipt_id_from_action_hash(action_hash, height, data_count)."""
    e = inst.ext
    d = create_hash_index(e.ah, e.height, inst.data_counter)
    inst.data_counter += 1
    return d


def ext_create_receipt(inst, deps, acc):
    """ext.rs create_action_receipt + receipt_manager.rs create_action_receipt."""
    data_ids = [ext_new_data_id(inst) for _ in deps]
    for d, dep in zip(data_ids, deps):
        inst.mgr[dep]['outputs'].append((d, acc))
    r = len(inst.mgr)
    inst.mgr.append(dict(recv=acc, refund_to=None, outputs=[], inputs=data_ids, actions=[], yield_=False))
    inst.rcpt_recv[r] = acc
    return r


def ext_append_action(inst, r, kind, text):
    """receipt_manager.rs append_action_*: the clean-room host functions pass their action as the
    harness's `fmt_action` text, parsed back here."""
    body = text.split(":", 1)[1] if ":" in text else ""
    p = body.split(":") if body else []
    if kind == "FC":
        method = _utf8_or_invalid(bytes.fromhex(p[0]))
        a = MAct(A_FC, dict(method=method, args=bytes.fromhex(p[1]), deposit=int(p[2]), gas=int(p[3])))
        weight = int(p[4])
    elif kind == "CA":
        a = MAct(A_CREATE, {})
    elif kind == "DC":
        if text == "OTHER":
            raise W.OutOfDomain("global-contract host function")
        a = MAct(A_DEPLOY, dict(code=bytes.fromhex(p[0])))
    elif kind == "TR":
        a = MAct(A_TRANSFER, dict(deposit=int(p[0])))
    elif kind == "ST":
        a = MAct(A_STAKE, dict(stake=int(p[0]), pk=_vm_pk(p[1])))
    elif kind == "AF":
        a = MAct(A_ADDKEY, dict(pk=_vm_pk(p[0]), ak=N.AK(int(p[1]), 'full')))
    elif kind == "AC":
        pk = _vm_pk(p[0])
        names = [bytes.fromhex(x) for x in p[4].split("/")] if p[4] else []
        for nm in names:
            _utf8_or_invalid(nm)
        allowance = None if p[2] == "-" else int(p[2])
        a = MAct(A_ADDKEY, dict(pk=pk, ak=N.AK(int(p[1]), 'fc', allowance, p[3].encode(), names)))
    elif kind == "DK":
        a = MAct(A_DELKEY, dict(pk=_vm_pk(p[0])))
    elif kind == "DA":
        a = MAct(A_DELACC, dict(beneficiary=p[0].encode()))
    else:
        raise W.OutOfDomain("state-init / global-contract / gas-key host function")
    acts = inst.mgr[r]['actions']
    acts.append(a)
    ai = len(acts) - 1
    if kind == "FC" and weight > 0:
        inst.weights.append((r, ai, weight))
    return ai


W.new_data_id = ext_new_data_id
W.create_receipt = ext_create_receipt
W.append_action = ext_append_action


def _ood_host(name):
    def h(inst, *a):
        raise W.OutOfDomain(f"host function {name} (state-init / global-contract / gas-key family)")
    return h


def _subsidy_or_deduct(inst, amount):
    """one_yocto_on_promise (85.yaml): exactly 1 yocto on a zero balance is subsidized."""
    if amount == 1 and inst.balance == 0:
        inst.subsidized += 1
    else:
        W.deduct_balance(inst, amount)


def h_function_call(inst, idx, mlen, mptr, alen, aptr, amt_ptr, gas, weight):
    W.pay(inst, "base")
    amount = W.read_u128(inst, amt_ptr)
    method = W.gmr(inst, mptr, mlen)
    if not method:
        raise W.HostErr("EmptyMethodName")
    args = W.gmr(inst, aptr, alen)
    r, sir = W.single_receipt(inst, idx)
    W.act(inst, "function_call", sir)
    W.act(inst, "function_call_byte", sir, len(method) + len(args))
    W.prepay(inst, gas)
    _subsidy_or_deduct(inst, amount)
    ext_append_action(inst, r, "FC", f"FC@{r}:{method.hex()}:{args.hex()}:{amount}:{gas}:{weight}")


def h_promise_create(inst, alen, aptr, mlen, mptr, glen, gptr, amt, gas):
    idx = W.batch_create(inst, alen, aptr)
    h_function_call(inst, idx, mlen, mptr, glen, gptr, amt, gas, 0)
    return idx


def h_promise_then(inst, pidx, alen, aptr, mlen, mptr, glen, gptr, amt, gas):
    idx = W.batch_then(inst, pidx, alen, aptr)
    h_function_call(inst, idx, mlen, mptr, glen, gptr, amt, gas, 0)
    return idx


def h_set_refund_to(inst, idx, n, ptr):
    W.pay(inst, "base")
    acc = W.read_account_id(inst, n, ptr)
    p = W.get_promise(inst, idx)
    if p[0] != "R":
        raise W.HostErr("CannotSetRefundToOnJointPromise")
    inst.mgr[p[1]]['refund_to'] = acc


def _yield_receipt(inst, data_id):
    r = len(inst.mgr)
    inst.mgr.append(dict(recv=W.CURRENT_ACCOUNT, refund_to=None, outputs=[], inputs=[data_id], actions=[],
                         yield_=True))
    inst.rcpt_recv[r] = W.CURRENT_ACCOUNT
    return r


def h_yield_create(inst, mlen, mptr, alen, aptr, gas, weight, reg):
    """logic.rs promise_yield_create; ext.rs create_promise_yield_receipt."""
    W.pay(inst, "base")
    W.pay(inst, "yield_create_base")
    method = W.gmr(inst, mptr, mlen)
    if not method:
        raise W.HostErr("EmptyMethodName")
    args = W.gmr(inst, aptr, alen)
    W.pay(inst, "yield_create_byte", len(method) + len(args))
    W.prepay(inst, gas)
    W.pay_new_receipt(inst, True, [True])
    acc = W.CURRENT_ACCOUNT
    data_id = ext_new_data_id(inst)
    r = _yield_receipt(inst, data_id)
    inst.ext.st.set(k_acc_data(C_YIELD_STATUS, acc, data_id), b"\x00")
    pidx = W.push_promise(inst, ("R", r))
    W.act(inst, "function_call", True)
    W.act(inst, "function_call_byte", True, len(method) + len(args))
    ext_append_action(inst, r, "FC", f"FC@{r}:{method.hex()}:{args.hex()}:0:{gas}:{weight}")
    W.reg_set(inst, reg, data_id)
    return pidx


def h_yield_create_with_id(inst, mlen, mptr, alen, aptr, amt_ptr, gas, weight, ylen, yptr):
    """logic.rs promise_yield_create_with_id; ext.rs create_promise_yield_receipt_with_id."""
    W.pay(inst, "base")
    W.pay(inst, "yield_create_with_id_base")
    amount = W.read_u128(inst, amt_ptr)
    method = W.gmr(inst, mptr, mlen)
    if not method:
        raise W.HostErr("EmptyMethodName")
    args = W.gmr(inst, aptr, alen)
    yid = W.gmr(inst, yptr, ylen)
    if len(yid) != 32:
        raise W.HostErr("YieldIdMalformed")
    W.pay(inst, "yield_create_byte", len(method) + len(args))
    st = inst.ext.st
    acc = W.CURRENT_ACCOUNT
    if st.contains(k_acc_data(C_YIELD_TO_DATA, acc, yid)):
        return W.U64
    data_id = ext_new_data_id(inst)
    st.set(k_acc_data(C_YIELD_TO_DATA, acc, yid), data_id)
    st.set(k_acc_data(C_DATA_TO_YIELD, acc, data_id), yid)
    r = _yield_receipt(inst, data_id)
    st.set(k_acc_data(C_YIELD_STATUS, acc, data_id), b"\x00")
    W.prepay(inst, gas)
    W.pay_new_receipt(inst, True, [True])
    pidx = W.push_promise(inst, ("R", r))
    W.act(inst, "function_call", True)
    W.act(inst, "function_call_byte", True, len(method) + len(args))
    _subsidy_or_deduct(inst, amount)
    ext_append_action(inst, r, "FC", f"FC@{r}:{method.hex()}:{args.hex()}:{amount}:{gas}:{weight}")
    return pidx


def _submit_resume(inst, data_id, payload):
    """ext.rs submit_promise_resume_data."""
    st = inst.ext.st
    acc = W.CURRENT_ACCOUNT
    if st.contains(k_acc_data(C_YIELD_RECEIPT, acc, data_id)) or \
            st.contains(k_acc_data(C_YIELD_STATUS, acc, data_id)):
        inst.data_receipts.append((data_id, payload))
        st.set(k_acc_data(C_YIELD_STATUS, acc, data_id), b"\x01")
        return 1
    return 0


def _yield_resume(inst, with_id, ilen, iptr, plen, pptr):
    W.pay(inst, "base")
    W.pay(inst, "yield_resume_base")
    W.pay(inst, "yield_resume_byte", plen)
    ident = W.gmr(inst, iptr, ilen)
    payload = W.gmr(inst, pptr, plen)
    if len(payload) > W.MAX_YIELD_PAYLOAD:
        raise W.HostErr(f"YieldPayloadLength {{ length: {len(payload)}, limit: {W.MAX_YIELD_PAYLOAD} }}")
    if len(ident) != 32:
        raise W.HostErr("YieldIdMalformed" if with_id else "DataIdMalformed")
    if with_id:
        v = inst.ext.st.get(k_acc_data(C_YIELD_TO_DATA, W.CURRENT_ACCOUNT, ident))
        if v is None:
            return 0
        if len(v) != 32:
            raise Reject("StorageInconsistentState: YieldIdToDataId value")
        ident = v
    return _submit_resume(inst, ident, payload)


def h_current_contract_code(inst, rid):
    W.pay(inst, "base")
    c = inst.ext.contract
    if c[0] == 'none':
        return 0
    if c[0] == 'local':
        W.reg_set(inst, rid, c[1])
        return 1
    raise W.OutOfDomain("w.shape: global contract")


def h_validator_stake(inst, n, ptr, out):
    W.pay(inst, "base")
    acc = W.read_account_id(inst, n, ptr)
    W.pay(inst, "validator_stake_base")
    W.mem_write(inst, out, inst.ext.validators.get(acc, 0).to_bytes(16, "little"))


def h_validator_total(inst, out):
    W.pay(inst, "base")
    W.pay(inst, "validator_total_stake_base")
    total = 0
    for v in inst.ext.validators.values():
        total += v
        if total > U128_MAX:
            raise Reject("validator_total_stake overflow (unwrap panic)")
    W.mem_write(inst, out, total.to_bytes(16, "little"))


HANDLERS = dict(W.HANDLERS)
HANDLERS.update({
    "current_account_id": W._reg_const(lambda i: W.CURRENT_ACCOUNT),
    "chain_id": W._reg_const(lambda i: i.ext.chain_id),
    "signer_account_id": W._reg_const(lambda i: i.ext.signer),
    "signer_account_pk": W._reg_const(lambda i: i.ext.signer_pk),
    "predecessor_account_id": W._reg_const(lambda i: i.ext.pred),
    "refund_to_account_id": W._reg_const(lambda i: i.ext.refund_to),
    "random_seed": W._reg_const(lambda i: i.ext.random_seed),
    "block_index": W._ret_const(lambda i: i.ext.height),
    "block_timestamp": W._ret_const(lambda i: i.ext.timestamp),
    "epoch_height": W._ret_const(lambda i: i.ext.epoch_height),
    "account_locked_balance": W._mem_u128(lambda i: i.ext.locked),
    "current_contract_code": h_current_contract_code,
    "validator_stake": h_validator_stake,
    "validator_total_stake": h_validator_total,
    "promise_create": h_promise_create,
    "promise_then": h_promise_then,
    "promise_set_refund_to": h_set_refund_to,
    "promise_batch_action_function_call": lambda inst, idx, ml, mp, al, ap, amt, gas:
        h_function_call(inst, idx, ml, mp, al, ap, amt, gas, 0),
    "promise_batch_action_function_call_weight": h_function_call,
    "promise_yield_create": h_yield_create,
    "promise_yield_create_with_id": h_yield_create_with_id,
    "promise_yield_resume": lambda inst, *a: _yield_resume(inst, False, *a),
    "promise_yield_resume_with_yield_id": lambda inst, *a: _yield_resume(inst, True, *a),
})
for _n in ("promise_batch_action_deploy_global_contract", "promise_batch_action_deploy_global_contract_by_account_id",
           "promise_batch_action_use_global_contract", "promise_batch_action_use_global_contract_by_account_id",
           "promise_batch_action_state_init", "promise_batch_action_state_init_by_account_id",
           "set_state_init_data_entry", "promise_batch_action_transfer_to_gas_key",
           "promise_batch_action_add_gas_key_with_full_access",
           "promise_batch_action_add_gas_key_with_function_call"):
    HANDLERS[_n] = _ood_host(_n)
W.HANDLERS.clear()
W.HANDLERS.update(HANDLERS)


# =============================================================================================
# Contract storage over the D2 TrieUpdate overlay with the chunk-scoped trie-node accounting of
# docs/research/d3-trie-accounting.md section 4 (the clean-room nearstore.TrieStore model, with the
# chunk's overlay = the D2 State's committed + prospective changes).
# =============================================================================================
class D3Store:
    def __init__(self, A, account):
        self.A = A
        self.st = A.st
        self.prefix = u8(C_DATA) + account + b","

    def _lookup(self, fk):
        """Path hashes (root first) and the value ref of fk in the pre-state trie."""
        trie = self.st.trie
        visited = []
        if trie.root == ZERO32:
            return visited, None
        nib = nibbles(fk)
        h = trie.root
        while True:
            n = trie.node(h)
            visited.append(h)
            if n.kind == 'leaf':
                return visited, (n.vref if n.key == nib else None)
            if n.kind == 'ext':
                if nib[:len(n.key)] != n.key:
                    return visited, None
                nib = nib[len(n.key):]
                h = n.child
                continue
            if not nib:
                return visited, n.vref
            if nib[0] not in n.children:
                return visited, None
            h = n.children[nib[0]]
            nib = nib[1:]

    def _touch(self, h):
        A = self.A
        if h in A.ttn_cache:
            A.ttn_mem += 1
        else:
            A.ttn_db += 1
            A.ttn_cache.add(h)

    def _commit_nodes(self, inst, db0, mem0):
        W.pay(inst, "touching_trie_node", self.A.ttn_db - db0)
        W.pay(inst, "read_cached_trie_node", self.A.ttn_mem - mem0)

    def _evict(self, inst, fk, B):
        hit, ov = self.st._ov(fk)
        if hit:
            if ov is None:
                return None
            W.pay(inst, B, len(ov))
            return ov
        A = self.A
        db0, mem0 = A.ttn_db, A.ttn_mem
        visited, vr = self._lookup(fk)
        for h in visited:
            self._touch(h)
        old = None
        if vr is not None:
            W.pay(inst, B, vr[0])
            self._touch(vr[1])
            old = self.st.trie.value(vr[1])
        self._commit_nodes(inst, db0, mem0)
        return old

    def write(self, inst, k, v):
        fk = self.prefix + k
        old = self._evict(inst, fk, "storage_write_evicted_byte")
        self.st.set(fk, v)
        return old

    def remove(self, inst, k):
        fk = self.prefix + k
        old = self._evict(inst, fk, "storage_remove_ret_value_byte")
        self.st.remove(fk)
        return old

    def read(self, inst, k):
        fk = self.prefix + k
        hit, ov = self.st._ov(fk)
        if hit:
            if ov is None:
                return None
            NS._value_charges(inst, ov)
            return ov
        _, vr = self._lookup(fk)
        if vr is None:
            return None
        NS._value_charges(inst, NS._Len(vr[0]))
        self._touch(vr[1])
        return self.st.trie.value(vr[1])

    def has(self, inst, k):
        fk = self.prefix + k
        hit, ov = self.st._ov(fk)
        if hit:
            return ov is not None
        _, vr = self._lookup(fk)
        return vr is not None

    def items(self):
        return ()




# =============================================================================================
# Running one FunctionCall (function_call.rs execute_function_call, with the clean-room VM)
# =============================================================================================
PREPARED = {}      # code hash -> ('ok', module) | ('err', kind, text)


def prepared(h, code):
    p = PREPARED.get(h)
    if p is not None:
        return p
    try:
        m = W.prepare(code)
        defined = [f for f in m.funcs if not f.imported]
        big = any(len(f.params) + len(f.locals) > W.ENGINE_LOCALS for f in defined)
        if big:
            p = ('nop', "CompilationError(WasmtimeCompileError)")
        else:
            for f in defined:
                W.compile_func(m, f)
            p = ('ok', m)
    except W.PrepError as e:
        p = ('nop', f"CompilationError(PrepareError({e.args[0]}))")
    except W.OutOfDomain as e:
        p = ('ood', f"e.float: {e.args[0]}")
    except W.Unmodeled as e:
        p = ('ood', f"e.unmodeled: {e.args[0]}")
    PREPARED[h] = p
    return p


class ExtEnv:
    pass


class VMCtx:
    """The parts of VMContext nearwasm reads through `inst.ctx`."""

    def __init__(self, receivers, inp, results, deposit, balance):
        self.receivers, self.input, self.results, self.deposit, self.balance = receivers, inp, results, deposit, balance


def run_vm(prep, code, method, prepaid, cap, ctx, ext, store, storage_usage):
    """-> dict(aborted, burnt, used, compute, logs, ret, balance, storage_usage, subsidized, mgr, weights,
    data_receipts).  Raises OOD / Reject / CapExceeded."""
    nop = dict(burnt=0, used=0, compute=0, logs=[], ret=None, mgr=[], weights=[], data_receipts=[], subsidized=0)
    if prep[0] == 'ood':
        raise OOD(prep[1])
    if prep[0] == 'nop':
        return dict(nop, aborted=prep[1])
    m = prep[1]
    gc = CappedGas(prepaid, cap)
    inst = W.Instance()
    inst.gc = gc
    inst.ctx = ctx
    inst.ext = ext
    inst.prof = {}
    inst.act_gas = 0
    inst.send_compute = 0
    inst.regs = {}
    inst.reg_usage = 0
    inst.logs = []
    inst.total_log = 0
    inst.alog = []
    inst.rcpt_recv = {}
    inst.actions = {}
    inst.store = store
    inst.storage_usage = storage_usage
    inst.data_counter = 0
    inst.ret = None
    inst.promises = []
    inst.balance = ctx.balance + ctx.deposit
    inst.mgr = []
    inst.weights = []
    inst.data_receipts = []
    inst.subsidized = 0

    def out(aborted):
        return dict(aborted=aborted, burnt=gc.burnt, used=gc.burnt + gc.promises, compute=W.compute_usage(inst),
                    logs=list(inst.logs), ret=inst.ret, balance=inst.balance, storage_usage=inst.storage_usage,
                    subsidized=inst.subsidized, mgr=inst.mgr, weights=inst.weights,
                    data_receipts=inst.data_receipts)

    # loading fee (ext costs contract_loading_bytes / contract_loading_base, clean-room T1)
    try:
        b0 = gc.burnt
        try:
            gc.pay_per(W.LOAD_BYTES, len(code))
        finally:
            inst.prof["contract_loading_bytes"] = gc.burnt - b0
        b0 = gc.burnt
        try:
            gc.pay_base(W.LOAD_BASE)
        finally:
            inst.prof["contract_loading_base"] = gc.burnt - b0
    except W.HostErr:
        return out("HostError(GasExceeded)")
    for nm, t in m.imports:
        if nm not in W.HOST or W.HOST[nm] != m.types[t]:
            return out("LinkError")
    ex = m.exports.get(method)
    if ex is None or ex[0] != 0:
        return dict(nop, aborted="MethodResolveError(MethodNotFound)")
    mainf = m.funcs[ex[1]]
    if (mainf.params, mainf.results) != ((), ()):
        return dict(nop, aborted="MethodResolveError(MethodInvalidSignature)")
    inst.m = m
    inst.g = gc.remaining()
    inst.stack = W.STACK_BUDGET
    inst.mem = W.mmap.mmap(-1, W.MEM_MAX_PAGES * W.PAGE)
    inst.memlen = W.MEM_INIT_PAGES * W.PAGE
    inst.globals = [g[2] for g in m.globals]
    inst.tables = [[None] * mn for mn, mx in m.tables]
    inst.table_max = [min(W.TABLE_CAP, mx if mx is not None else W.TABLE_CAP) for mn, mx in m.tables]
    inst.elems = [list(items) if mode == "passive" or mode == "active" else [] for mode, t, off, items in m.elems]
    inst.datas = [d for mode, off, d in m.datas]
    try:
        for k, (mode, t, off, items) in enumerate(m.elems):
            if mode == "active":
                tab = inst.tables[t]
                if off + len(items) > len(tab):
                    raise W.Trap("MemoryOutOfBounds")
                tab[off:off + len(items)] = items
                inst.elems[k] = []
            elif mode == "declarative":
                inst.elems[k] = []
        for k, (mode, off, d) in enumerate(m.datas):
            if mode == "active":
                if off + len(d) > inst.memlen:
                    raise W.Trap("MemoryOutOfBounds")
                inst.mem[off:off + len(d)] = d
                inst.datas[k] = b""
    except W.Trap as e:
        return out(f"WasmTrap({e.args[0]})")
    try:
        for entry in ([m.start] if m.start is not None else []) + [ex[1]]:
            try:
                if m.funcs[entry].imported:
                    inst.g = gc.remaining()
                    W.host_call(inst, m.funcs[entry], [])
                else:
                    W.execute(inst, entry)
            except CapExceeded:
                raise
            except BaseException:
                W.sync_exit(inst)
                raise
            W.sync_exit(inst)
    except W.Trap as e:
        return out(f"WasmTrap({e.args[0]})")
    except W.HostErr as e:
        return out(f"HostError({e.args[0]})")
    except W.OutOfDomain as e:
        raise OOD(f"e.wasm-alpha: {e.args[0]}")
    except W.Unmodeled as e:
        raise OOD(f"e.unmodeled: {e.args[0]}")
    except RecursionError:
        raise OOD("e.unmodeled: python recursion")
    except NS.StorageError as e:
        raise Reject(f"StorageError: {e.args[0]}")
    return out(None)


# =============================================================================================
# State with the chunk's contract deploy tracker (core/store/src/contract.rs ContractsTracker)
# =============================================================================================
class DState(D2.State):
    def __init__(self, trie):
        super().__init__(trie)
        self.dep_unc = {}        # code hash -> code (current receipt)
        self.dep_com = {}        # code hash -> code (committed earlier in the chunk)
        self.acct_unc = set()    # accounts whose contract a deploy of the current receipt set
        self.acct_com = set()
        self.attempted = set()   # every code hash deployed in the chunk, committed or rolled back

    def commit(self):
        super().commit()
        self.dep_com.update(self.dep_unc)
        self.dep_unc = {}
        self.acct_com |= self.acct_unc
        self.acct_unc = set()

    def rollback(self):
        super().rollback()
        self.dep_unc = {}
        self.acct_unc = set()


def decode_received(v):
    try:
        r = R(v)
        t = r.u8()
        if t == 0:
            d = None
        elif t == 1:
            d = r.bytes()
        else:
            raise DecodeError("ReceivedData option tag")
        r.end()
        return d
    except DecodeError:
        raise Reject("StorageInconsistentState: ReceivedData does not decode")


def outcome_leaf_logs(oid, partial, logs):
    return sha(u32(2 + len(logs)) + oid + sha(partial) + b"".join(sha(l) for l in logs))


# =============================================================================================
# The main transition with FunctionCall
# =============================================================================================
class ApplyD3(D2.Apply):
    def __init__(self, *a, env=None):
        super().__init__(*a)
        self.env = env
        self.subsidized = 0
        self.fc_sum = 0
        self.ttn_cache = set()
        self.ttn_db = 0
        self.ttn_mem = 0
        self.pre_hash = {}

    def pre_state_hash(self, acc_id):
        """The account's local contract hash in the chunk's pre-state trie (None if absent / no contract).
        Every account the chunk touches was read through the trie once, so this read needs no
        node the validator did not already need."""
        if acc_id not in self.pre_hash:
            v = self.st.trie.get(k_account(acc_id))
            h = None
            if v is not None:
                a = N.decode_account(v)
                if a.contract[0] == 'local':
                    h = a.contract[1]
            self.pre_hash[acc_id] = h
        return self.pre_hash[acc_id]

    def add_fc_gas(self, g):
        self.fc_sum += g

    # -------- apply_action_receipt (lib.rs:776-1156) with the D3 extensions E3, E6-E13
    def apply_action_receipt(self, x):
        st = self.st
        acc_id = x.recv
        results = []
        for d in x.inputs:
            k = k_acc_data(C_RECEIVED_DATA, acc_id, d)
            v = st.get(k)
            if v is None:
                raise Reject("StorageInconsistentState: received data should be in the state")
            data = decode_received(v)
            results.append(("F", None) if data is None else ("S", data))
            st.remove(k)
        st.commit()
        account = st.get_account(acc_id)
        did_not_exist = account is None
        ctx = dict(account=account, actor=x.pred)
        nar = fee('new_action_receipt', 'exec')
        res = dict(gas_burnt=nar[0], gas_used=nar[0], compute=nar[1], ok=True, err=None, new=[],
                   proposals=[], tokens_burnt=0, gas_fc=0, logs=[], ret=('none',), subsidized=0)
        is_refund = x.pred == b'system'
        for i, a in enumerate(x.actions):
            ar = self.apply_action_d3(a, x, i, ctx, is_refund, len(x.actions) == 1, results)
            if ar['ok']:
                for y in ar['new']:
                    if validate_receipt(y, True) is not None:
                        ar['ok'] = False
                        ar['err'] = 'NewReceiptValidationError'
                        break
            if not (ar['gas_fc'] <= ar['gas_burnt'] <= ar['gas_used']):
                raise Reject("ActionResult::merge assertion (panic)")
            try:
                res['gas_burnt'] = cadd64(res['gas_burnt'], ar['gas_burnt'])
                res['gas_fc'] = cadd64(res['gas_fc'], ar['gas_fc'])
                res['gas_used'] = cadd64(res['gas_used'], ar['gas_used'])
                res['compute'] = cadd64(res['compute'], ar['compute'])
                res['logs'] += ar['logs']
                if ar['ok']:
                    ret = ar['ret']
                    if ret[0] == 'receipt':
                        ret = ('receipt', ret[1] + len(res['new']))
                    res['ret'] = ret
                    res['new'] += ar['new']
                    res['proposals'] += ar['proposals']
                    res['tokens_burnt'] = cadd128(res['tokens_burnt'], ar['tokens_burnt'])
                    res['subsidized'] = cadd128(res['subsidized'], ar['subsidized'])
                else:
                    self.set_error(res, ar['err'])
            except Overflow:
                raise Reject("integer overflow merging action results")
            if not res['ok']:
                break
        account = ctx['account']
        if res['ok'] and account is not None:
            if storage_stake_ok(account, account.amount):
                st.set_account(acc_id, account)
            else:
                self.set_error(res, 'LackBalanceForState')
        purchase = x.gas_price
        burn = min(purchase, self.gas_price)
        deficit = penalty = create_charge = 0
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
            tokens_burnt = tx_burnt_amount
            # receiver reward (lib.rs:988-1021)
            rg = res['gas_fc'] * BURNT_GAS_REWARD[0]
            if rg > U64_MAX:
                raise Reject("receiver gas reward overflow (unwrap panic)")
            rg //= BURNT_GAS_REWARD[1]
            reward = cmul128(burn, rg)
            if reward > 0:
                acc2 = st.get_account(acc_id)
                if acc2 is not None:
                    tx_burnt_amount -= reward
                    acc2 = acc2.copy()
                    acc2.amount = cadd128(acc2.amount, reward)
                    st.set_account(acc_id, acc2)
                    st.commit()
            self.tx_burnt = cadd128(self.tx_burnt, tx_burnt_amount)
            self.subsidized = cadd128(self.subsidized, res['subsidized'])
        except Overflow:
            raise Reject("integer overflow in receipt balance accounting")
        if x.outputs:
            ret = res['ret']
            if res['ok'] and ret[0] == 'receipt':
                k = ret[1]
                if k >= len(res['new']):
                    raise Reject("receipt for the given receipt index should exist (panic)")
                y = res['new'][k]
                if not y.is_action():
                    raise Reject("the receipt should be an action receipt (unreachable)")
                y = N.with_rid(y, y.rid)
                y.outputs = list(y.outputs) + list(x.outputs)
                y.raw = y.encode()
                res['new'][k] = y
            else:
                if not res['ok']:
                    data = None
                elif ret[0] == 'value':
                    data = ret[1]
                else:
                    data = b''
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
        if not res['ok']:
            status = ('fail',)
        elif res['ret'][0] == 'receipt':
            status = ('rid', create_hash_index(x.rid, self.height, res['ret'][1]))
        elif res['ret'][0] == 'value':
            status = ('value', res['ret'][1])
        else:
            status = ('value', b'')
        partial = partial_outcome(receipt_ids, res['gas_burnt'], tokens_burnt, acc_id, status)
        return outcome_leaf_logs(x.rid, partial, res['logs']), res['gas_burnt'], res['compute']

    @staticmethod
    def set_error(res, err):
        res['ok'] = False
        res['err'] = err
        res['new'] = []
        res['proposals'] = []
        res['tokens_burnt'] = 0
        res['subsidized'] = 0

    def apply_action_d3(self, a, x, i, ctx, is_refund, only_action, results):
        if a.tag == A_FC:
            ar = self.function_call(a, x, i, ctx, results)
        else:
            ar = self.apply_action(a, x, ctx, is_refund, only_action)
            if a.tag == A_DEPLOY and ar['ok']:
                code = a.f['code']
                h = sha(code)
                self.st.dep_unc[h] = code
                self.st.acct_unc.add(x.recv)
                self.st.attempted.add(h)
        for k, v in (('gas_fc', 0), ('logs', []), ('ret', ('none',)), ('subsidized', 0)):
            ar.setdefault(k, v)
        return ar

    # -------- the FunctionCall arm (lib.rs:631-668, function_call.rs)
    def function_call(self, a, x, i, ctx, results):
        st = self.st
        acc_id = x.recv
        ef = D2.exec_fee(a, acc_id)
        res = dict(gas_burnt=ef[0], gas_used=ef[0], compute=ef[1], ok=True, err=None, new=[], proposals=[],
                   tokens_burnt=0, gas_fc=0, logs=[], ret=('none',), subsidized=0)
        account = ctx['account']
        if account is None:
            res['ok'] = False
            res['err'] = 'AccountDoesNotExist'
            return res
        f = a.f
        c = account.contract
        if c[0] in ('global', 'global_by'):
            raise OOD("w.shape: FunctionCall on an account with a global contract")
        if c[0] == 'local' and is_eth_implicit(acc_id):
            raise OOD("w.shape: FunctionCall on an ETH-implicit account with a local contract")
        if account.amount + f['deposit'] > U128_MAX:
            raise Reject("StorageInconsistentState: balance overflow with the call deposit")
        ah = create_hash_index(x.rid, self.height, U64_MAX - i)
        if c[0] == 'none':
            # ContractCodeNotPresent with account.contract = None: 0-gas CodeDoesNotExist (fc.rs:293-310)
            vm = dict(aborted="CompilationError(CodeDoesNotExist)", burnt=0, used=0, compute=0, logs=[],
                      ret=None, mgr=[], weights=[], data_receipts=[], subsidized=0, early=True)
        else:
            h = c[1]
            if self.pre_state_hash(acc_id) != h:
                # a contract set by a deploy in this chunk: the deploy tracker (contract.rs:42-48);
                # the pipeline drops a preparation whose code hash changed (pipelining.rs get_contract)
                code = st.dep_unc.get(h)
                if code is None:
                    code = st.dep_com.get(h)
                if code is None:
                    code = st.trie.store.get(h)
            else:
                # a pre-state contract: the witness (merged values), cold cache (section 2.2, 10.0)
                code = st.trie.store.get(h)
                if code is None and h in st.attempted:
                    raise OOD("e.code_cache: an executed pre-state contract's code is absent from the witness "
                              "while the same code was deployed earlier in the chunk (compiled-contract cache)")
            if code is None:
                raise Reject("StorageError: MissingTrieValue (contract code %s)" % h.hex())
            prep = prepared(h, code)
            env = self.env
            e = ExtEnv()
            e.st = st
            e.ah = ah
            e.height = self.height
            e.chain_id = self.chain_id
            e.signer = x.signer
            e.signer_pk = x.pk
            e.pred = x.pred
            e.refund_to = x.refund_to if x.refund_to is not None else x.pred
            e.random_seed = sha(ah + env['random_value'])
            e.timestamp = env['timestamp']
            e.epoch_height = env['epoch_height']
            e.locked = account.locked
            e.contract = c
            e.validators = env['validators']
            receivers = [r for _, r in x.outputs] if i + 1 == len(x.actions) else []
            vctx = VMCtx(receivers, f['args'], results, f['deposit'], account.amount)
            W.CURRENT_ACCOUNT = acc_id
            try:
                method = f['method'].decode('utf-8')
            except UnicodeDecodeError:
                raise Reject("method name is not UTF-8")
            try:
                vm = run_vm(prep, code, method, f['gas'], HARD_CAP - self.fc_sum, vctx, e,
                            D3Store(self, acc_id), account.su)
            except CapExceeded:
                raise OOD("e.g_alpha: chunk gas_burnt_for_function_call > %d (checker resource cap)" % HARD_CAP)
            # gas weights (function_call.rs:341-345, receipt_manager.rs distribute_gas)
            unused = f['gas'] - vm['used'] if f['gas'] > vm['used'] else 0
            wsum = sum(w for _, _, w in vm['weights'])
            if wsum and unused:
                dist = 0
                for j, (ri, ai, w) in enumerate(vm['weights']):
                    to = unused * w // wsum
                    act = vm['mgr'][ri]['actions'][ai]
                    act.f['gas'] += to
                    dist += to
                    if j == len(vm['weights']) - 1:
                        act.f['gas'] += unused - dist
                        dist = unused
                    if act.f['gas'] > U64_MAX:
                        raise Reject("IntegerOverflowError distributing gas")
                vm['used'] += dist
                if vm['used'] > U64_MAX:
                    raise Reject("IntegerOverflowError: used gas")
        self.add_fc_gas(vm['burnt'])
        ok = vm['aborted'] is None
        try:
            res['gas_burnt'] = cadd64(res['gas_burnt'], vm['burnt'])
            res['gas_fc'] = cadd64(res['gas_fc'], vm['burnt'])
            res['gas_used'] = cadd64(res['gas_used'], vm['used'])
            res['compute'] = cadd64(res['compute'], vm['compute'])
        except Overflow:
            raise Reject("integer overflow adding the VM outcome")
        res['logs'] = list(vm['logs'])
        if not ok:
            res['ok'] = False
            res['err'] = 'FunctionCallError: ' + vm['aborted']
            return res
        # success (function_call.rs:154-230)
        idx = st.get_indices(u8(C_YIELD_INDICES))
        init = list(idx)
        new = []
        for m in vm['mgr']:
            if m['yield_']:
                if idx[1] + 1 > U64_MAX:
                    raise Reject("yield timeout index overflow (panic)")
                st.set(u8(C_YIELD_TIMEOUT) + u64(idx[1]),
                       bstr(acc_id) + m['inputs'][0] + u64(self.height + YIELD_TIMEOUT_LENGTH))
                idx[1] += 1
            acts = [ma.to_action() for ma in m['actions']]
            new.append(N.new_action_receipt(acc_id, m['recv'], ZERO32, x.signer, x.pk, x.gas_price,
                                            list(m['outputs']), list(m['inputs']), acts,
                                            kind=K_YIELD_V2 if m['yield_'] else K_ACTION_V2,
                                            refund_to=m['refund_to']))
        for d, payload in vm['data_receipts']:
            new.append(N.new_data_receipt(acc_id, acc_id, ZERO32, d, payload, kind=K_RESUME))
        if idx != init:
            st.set(u8(C_YIELD_INDICES), u64(idx[0]) + u64(idx[1]))
        if vm['storage_usage'] < 0 or vm['storage_usage'] > U64_MAX:
            raise Reject("InconsistentStateError: storage usage overflow")
        acc = account.copy()
        acc.amount = vm['balance']
        acc.su = vm['storage_usage']
        ctx['account'] = acc
        res['subsidized'] = vm['subsidized']
        r = vm['ret']
        if r is None:
            res['ret'] = ('none',)
        elif isinstance(r, tuple):
            res['ret'] = ('receipt', r[1])
        else:
            res['ret'] = ('value', bytes(r))
        res['new'] = new
        return res


# =============================================================================================
# The D3-alpha relation
# =============================================================================================
def check_case_inner(claim_b, witness_b):
    c = s3.decode_claim(claim_b)
    wr = R(witness_b)
    if wr.bytes() != D2.FORMAT_WITNESS:
        raise DecodeError("witness format id")
    sw = wr.bytes()
    codes = wr.vec(wr.bytes)
    wr.end()
    if len(sw) > D2.MAX_WITNESS:
        raise Reject("state witness larger than 64 MiB")
    if len(sw) > D2.D_MAX_WITNESS:
        raise OOD("w.size: state witness larger than 8 MiB")
    Wt = D2.decode_state_witness_d2(sw)

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
    if Wt['epoch_id'] != c['epoch_id']:
        raise Reject("witness epoch_id != claim epoch_id")
    if Wt['inner'].raw != c['chunk_inner']:
        raise Reject("witness chunk header inner != claim chunk_inner")

    # ---- claim-level conditions (D2)
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
    for t in Wt['new_txs']:
        if len(t.raw) > D2.MAX_TRANSACTION_SIZE:
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
    txs = Wt['txs']
    if len(c['tx_valid']) != len(txs):
        raise Reject("claim: tx_valid length != number of witness transactions")
    own_slot = B2.slots[idx]
    cong_b2 = s3.ctx_congestion(B2)
    if s0 not in cong_b2:
        raise OOD("c.own_congestion: no congestion info for own shard (bootstrap)")
    own_info = cong_b2[s0][0]
    # D3: the code blobs join the main transition's recorded values (w.no_code lifted); w.size
    # sums the merged list
    merged = list(Wt['main']['base_state']) + list(codes)
    base_bytes = sum(len(v) for v in merged)
    if base_bytes > D2.D_MAX_BASE_STATE:
        raise OOD("w.size: main base_state ++ codes > 3 000 000 bytes")

    # ---- source receipt proofs
    proofs = Wt['proofs']
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
    if sha(u32(len(R_list)) + b''.join(x.raw for x in R_list)) != Wt['applied_receipts_hash']:
        raise Reject("applied_receipts_hash mismatch")
    if own_slot.inner.tx_root != merklize([t.raw for t in txs]):
        raise Reject("tx_root of last new chunk != merklize(witness transactions)")

    # ---- main transition
    height = B2.height
    gas_price = blocks[b2i + 1].rest['next_gas_price']
    trie = Trie2(merged, own_slot.inner.prev_state_root)
    st = DState(trie)
    facts = c['apply_facts'][0]
    if facts['validator_update'] is not None:
        D2.validator_accounts_update(st, L, s0, facts['validator_update'], own_slot.inner.prev_validator_proposals)
    ep2 = epmap[B2.lite['epoch_id']]
    env = dict(timestamp=B2.lite['timestamp'], random_value=B2.rest['random_value'],
               epoch_height=ep2['height'], validators=dict(ep2['validators']))
    A = ApplyD3(st, L, s0, height, gas_price, own_slot.inner.gas_limit, facts['minimum_stake'], c['chain_id'],
                None, env=env)
    A.delayed_init()
    grants = D2.scheduler_step(st, L, B2)
    A.sink_init(own_info, cong_b2, grants)
    A.forward_from_buffers()
    A.process_transactions(txs, c['tx_valid'])
    ids = [x.rid for x in A.local] + [x.rid for x in R_list]
    if len(set(ids)) != len(ids):
        raise OOD("e.distinct_ids")
    A.incoming = R_list
    A.process_receipts()
    if base_bytes + 2000 * st.data_removals > D2.PROOF_SOFT_LIMIT:
        raise OOD("w.size: base_state ++ codes + 2000 x ContractData removals > 4 000 000 (proof limit)")
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
            sizes = [min(A.get_group(sid, gi)[0], D2.MAX_RECEIPT_SIZE) for gi in range(m['first'], m['next'])]
        else:
            sizes = [D2.MAX_RECEIPT_SIZE]
        req = D2.make_bw_request(sid, sizes, base_bw)
        if req is not None:
            bw.append(req)
    st.commit()
    state_root = st.finalize()
    # e.g_alpha (section 10.0 decision 3): decided on the completed main transition, so a storage error
    # anywhere in it (also after the G_alpha point) is a reject
    if A.fc_sum > G_ALPHA:
        raise OOD("e.g_alpha: chunk gas_burnt_for_function_call %d > 2^22 * 822756" % A.fc_sum)
    if state_root != Wt['main']['post_state_root']:
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
    if balance_burnt < A.subsidized:
        raise Reject("balance_burnt - subsidized underflow")
    balance_burnt -= A.subsidized
    gas_used = A.total_gas

    # ---- implicit transitions (missing chunks)
    imp = list(reversed(implicit_idx))
    if len(imp) != len(Wt['implicit']):
        raise Reject("implicit transitions count mismatch")
    for k, (bi_, T) in enumerate(zip(imp, Wt['implicit'])):
        M = blocks[bi_]
        t2 = Trie2(T['base_state'], state_root)
        st2 = D2.State(t2)
        af = c['apply_facts'][1 + k]
        if af['validator_update'] is not None:
            D2.validator_accounts_update(st2, L, s0, af['validator_update'], uniq)
        st2.get_indices(u8(C_DELAYED))
        D2.scheduler_step(st2, L, M)
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
    if H.tx_root != merklize([t.raw for t in Wt['new_txs']]):
        raise Reject("InvalidTxRoot")
    body = (u32(len(Wt['new_txs'])) + b''.join(t.raw for t in Wt['new_txs']) +
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
        print("spec_check_v3_d3: INTERNAL ERROR on %s: %r\n%s" % (d, e, traceback.format_exc()), file=sys.stderr)
        return "reject", "INTERNAL ERROR %s: %s" % (type(e).__name__, e)


def main():
    sys.setrecursionlimit(100000)
    args = sys.argv[1:]
    if args and args[0] == "--list":
        args = [l.strip() for l in open(args[1]) if l.strip()]
    for d in args:
        v, reason = check_case(d)
        print(json.dumps(dict(case=d, verdict=v, reason=reason)))
        sys.stdout.flush()


if __name__ == "__main__":
    main()
