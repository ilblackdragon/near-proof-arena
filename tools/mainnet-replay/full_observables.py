#!/usr/bin/env python3
"""Per-outcome observable comparison (workplan W01): Lean's computed outcomes, outgoing receipts and
storage changes against nearcore's own values.

Expected values are the records `near-arena-oracle-v3-successor` writes with
`NEAR_SUCCESSOR_OBSERVABLES=1` (`nearcore-observables-*.jsonl`, `oracle/v3-successor/src/
observables.rs`): a cold nearcore validator's `apply_new_chunk` on the case's witness. A record is
bound to a case by the sha256 of the case's `claim.bin` and `witness.bin`, never by name.

Each case is blinded exactly as `blind_corpus.py` does (every produced header value and witness
post-state root zeroed), the checker runs with `--blind-full`, and its version-2 detail is compared
field by field. Lean never sees an expected value: the per-outcome values are not in the claim or
witness at all, and the header-level ones are removed.

Independent of both producers, the outcome root is recomputed here from the *emitted* per-outcome
fields of each side (`outcome_leaf`, `merkle_root`) and must equal the header's `prev_outcome_root`:
the emitted list is the list that was hashed.

`--controls N` re-runs the comparison of up to N fully matching cases against expected records with
one field mutated per control (`MUTATIONS`); every control must be reported as a mismatch of the
mutated field (wrong-observable controls).

Version 3 rows (the checker's `observeDetail`, 2026-10-29) add, and this compares when the expected
record carries them:

* `outcome.failureKind`: each failed outcome's kind, canonicalized on both sides by
  `failure_kinds.py` (nearcore's `ExecutionError(<Display>)` resolved back to the VM variant);
* `outcome.computeUsage`: each outcome's compute usage (mainnet records have none);
* `attrib.*`: per processed transaction / receipt, the committed keys whose value it changed and
  their final values. nearcore's side is derived from its per-change causes and values plus the
  pre-state value reference of each key (`observables.rs` `change_detail_json`): a cause naming a
  transaction or receipt id is attributed to the Lean entry listing that id, and a change counts when
  the value after the entry differs from the value before it.
"""
import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
import copy
import gzip
import hashlib
import json
from pathlib import Path
import random
import re
import shutil
import struct
import subprocess
import tempfile
import time

import blind_inputs
import failure_kinds


def sha_bytes(b):
    return hashlib.sha256(b).digest()


def sha_file(path):
    with Path(path).open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


# ---- nearcore outcome hashing (`ExecutionOutcomeWithId::to_hashes`, `merklize`), re-implemented

def u32(n):
    return struct.pack('<I', n)


def status_bytes(st):
    k = st['kind']
    if k == 'value':
        v = bytes.fromhex(st['value'])
        return b'\x02' + u32(len(v)) + v
    if k == 'receipt':
        return b'\x03' + bytes.fromhex(st['receiptId'])
    if k == 'failure':
        return b'\x01'
    if k == 'unknown':
        return b'\x00'
    raise ValueError(f'status kind {k}')


def outcome_leaf(o):
    ids = [bytes.fromhex(x) for x in o['receiptIds']]
    ex = bytes.fromhex(o['executor'])
    partial = (u32(len(ids)) + b''.join(ids) + struct.pack('<Q', int(o['gasBurnt'])) +
               int(o['tokensBurnt']).to_bytes(16, 'little') + u32(len(ex)) + ex + status_bytes(o['status']))
    logs = [bytes.fromhex(x) for x in o['logs']]
    return sha_bytes(u32(2 + len(logs)) + bytes.fromhex(o['id']) + sha_bytes(partial) +
                     b''.join(sha_bytes(l) for l in logs))


def merkle_root(leaves):
    if not leaves:
        return bytes(32)
    level = list(leaves)
    while len(level) > 1:
        nxt = [sha_bytes(level[i] + level[i + 1]) for i in range(0, len(level) - 1, 2)]
        if len(level) % 2:
            nxt.append(level[-1])
        level = nxt
    return level[0]


# ---- normalization of both sides to one comparable form

RECEIPT_KIND = {'Action': 'action', 'ActionV2': 'action', 'PromiseYield': 'promise_yield',
                'PromiseYieldV2': 'promise_yield', 'Data': 'data', 'PromiseResume': 'promise_resume',
                'GlobalContractDistribution': 'global_contract_distribution'}
SYSTEM = b'system'.hex()


def norm_outcome(o, lean=False):
    st = o['status']
    kind = None
    if st['kind'] == 'failure' and st.get('error') is not None:
        kind = (failure_kinds.canonical_lean if lean else failure_kinds.canonical_expected)(st['error'])
    return {'id': o['id'], 'executor': o['executor'], 'status': st['kind'],
            'returnData': st.get('value') if st['kind'] == 'value' else None,
            'statusReceiptId': st.get('receiptId') if st['kind'] == 'receipt' else None,
            'gasBurnt': o['gasBurnt'], 'tokensBurnt': o['tokensBurnt'], 'logs': o['logs'],
            'receiptIds': o['receiptIds'], 'failureKind': kind,
            'computeUsage': o.get('computeUsage')}


def norm_receipt(r):
    kind = RECEIPT_KIND.get(r['kind'], r['kind'])
    return {'id': r['id'], 'predecessor': r['predecessor'], 'receiver': r['receiver'], 'kind': kind,
            'bodyHash': r['hash'], 'refund': r['predecessor'] == SYSTEM}


def norm_changes(cs):
    return {c['key']: (c['valueHash'], c['valueLen']) for c in cs}


# `deploy_global_contract_execution_{base,per_byte}` at PV86 (`core/parameters/res/runtime_configs/
# 84.yaml:39-40`, `parameters.snap:272-273`): compute only, no gas, no outcome.
DISTRIBUTION_COMPUTE_BASE = 20_000_000_000_000
DISTRIBUTION_COMPUTE_PER_BYTE = 250_000_000
GLOBAL_CONTRACT_CODE_PREFIX = '12'    # TrieKey col::GLOBAL_CONTRACT_CODE = 18


def expected_compute(exp):
    """The chunk's total compute as nearcore accumulates it (`processing_state.total.compute`).

    nearcore does not expose the total: outcomes carry `compute_usage`, but a fresh
    `GlobalContractDistribution` receipt adds `deploy_global_contract_execution_base +
    per_byte * code_len` with no outcome (`runtime/src/lib.rs:1506-1516`,
    `global_contracts.rs:223-268`). Each such application commits the code under
    `TrieKey::GlobalContractCode` with cause `ReceiptProcessing`, so the term is recovered from
    nearcore's own state changes."""
    total = sum(int(o['computeUsage']) for o in exp['outcomes'])
    for c in exp['state_changes']:
        if c['key'].startswith(GLOBAL_CONTRACT_CODE_PREFIX) and c['valueLen'] is not None:
            n = sum(1 for x in c.get('causes', []) if x.startswith('ReceiptProcessing'))
            total += n * (DISTRIBUTION_COMPUTE_BASE + DISTRIBUTION_COMPUTE_PER_BYTE * int(c['valueLen']))
    return str(total)


OUTCOME_FIELDS = ('id', 'executor', 'status', 'returnData', 'statusReceiptId', 'gasBurnt',
                  'tokensBurnt', 'logs', 'receiptIds')
# compared only when both sides report them (version-3 Lean rows; records with errors / compute)
OPTIONAL_OUTCOME_FIELDS = ('failureKind', 'computeUsage')


# ---- per-receipt storage attribution (version 3)

_B58 = '123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz'


def b58_to_hex(s):
    n = 0
    for ch in s:
        n = n * 58 + _B58.index(ch)
    b = n.to_bytes(32, 'big')
    return b.hex()


_CAUSE_ID = re.compile(r'^(TransactionProcessing|ActionReceiptProcessingStarted|ActionReceiptGasReward|'
                       r'ReceiptProcessing|PostponedReceipt) \{ (?:tx_hash|receipt_hash): ([1-9A-HJ-NP-Za-km-z]+) \}$')


def cause_id(cause):
    """The transaction / receipt id a `StateChangeCause` names, as hex; None for chunk-level causes."""
    m = _CAUSE_ID.match(cause)
    return b58_to_hex(m.group(2)) if m else None


def has_attribution(exp):
    return bool(exp['state_changes']) and all('changes' in c and 'pre' in c for c in exp['state_changes'])


# Outgoing-buffer keys (`TrieKey` columns BUFFERED_RECEIPT_INDICES 13, BUFFERED_RECEIPT 14,
# BUFFERED_RECEIPT_GROUPS_QUEUE_DATA 16, _ITEM 17). nearcore writes them in the receipt sink *after*
# the receipt's last commit (`lib.rs:963` commits `ReceiptProcessing`, `lib.rs:1109` then forwards or
# buffers its new receipts), so its change log files them under the *next* commit's cause, i.e. the
# next receipt, or `UpdatedDelayedReceipts` (`lib.rs:2781`). That is bookkeeping order, not state: the
# final value of every such key is still compared chunk-wide (`stateChanges`). They are left out of
# the per-receipt attribution on both sides.
QUEUE_KEY_PREFIXES = ('0d', '0e', '10', '11')


def attrib_key(k):
    return not k.startswith(QUEUE_KEY_PREFIXES)


def lean_groups(entries):
    """Merge each entry with its unknown-pre companion (same ids, `preKnown: false`). Returns
    [(ids, known {key: v}, unknown {key: v})]."""
    out = []
    for e in entries:
        cs = {c['key']: (None if c['valueHash'] is None else (c['valueHash'], c['valueLen']))
              for c in e['changes'] if attrib_key(c['key'])}
        if e.get('preKnown', True) or not out or out[-1][0] != e['ids']:
            if e.get('preKnown', True):
                out.append((e['ids'], cs, {}))
            else:
                out.append((e['ids'], {}, cs))
        else:
            out[-1][2].update(cs)
    return out


def group_of(cause, cid, by_first, by_last):
    """The Lean entry a cause belongs to. `PostponedReceipt{h}`: the entry that processed h itself
    (first id). Every other receipt cause: the last entry whose outcome is h (a receipt postponed and
    completed in one chunk has two entries); a transaction or receipt without an outcome entry: its
    first-id entry."""
    if cause.startswith('PostponedReceipt'):
        return by_first.get(cid)
    g = by_last.get(cid)
    return g if g is not None else by_first.get(cid)


def expected_attribution(exp, groups):
    """nearcore's changes per Lean group. `groups` = lean_groups(...). Returns
    (effective {g: {key: v}}, written {g: {key: v}}, ungrouped ids with effective changes,
    pre-state lookup errors). `written` = the value after the group for every key it committed,
    changed or not."""
    by_first, by_last = {}, {}
    for i, (ids, _, _) in enumerate(groups):
        by_first.setdefault(ids[0], i)
        by_last[ids[-1]] = i
    eff, written, unattributed, errors = {}, {}, Counter(), 0
    for c in exp['state_changes']:
        if not attrib_key(c['key']):
            continue
        pre = c['pre']
        if pre is None or 'error' in pre:
            errors += 1
            continue
        running = None if pre.get('absent') else (pre['valueHash'], pre['valueLen'])
        before, after = {}, {}
        for ch in c['changes']:
            cid = cause_id(ch['cause'])
            if cid is None:
                g = ('chunk', None)
            else:
                g = group_of(ch['cause'], cid, by_first, by_last)
                if g is None:
                    g = ('id', cid)
            if g not in before:
                before[g] = running
            running = None if ch['valueHash'] is None else (ch['valueHash'], ch['valueLen'])
            after[g] = running
        for g in before:
            if isinstance(g, int):
                written.setdefault(g, {})[c['key']] = after[g]
            if before[g] != after[g]:
                if isinstance(g, int):
                    eff.setdefault(g, {})[c['key']] = after[g]
                elif g[0] == 'id':
                    unattributed[g[1]] += 1
    return eff, written, unattributed, errors


def compare_attribution(lean_out, exp, counts, bad):
    entries = lean_out.get('receiptStateChanges')
    if entries is None or not has_attribution(exp):
        return
    groups = lean_groups(entries)
    eff, written, unattributed, errors = expected_attribution(exp, groups)
    counts['attrib.preState'] += 1
    if errors:
        bad['attrib.preState'] += 1
    counts['attrib.unattributed'] += 1
    if unattributed:
        bad['attrib.unattributed'] += 1
    for i, (ids, known, unknown) in enumerate(groups):
        want, wrote = eff.get(i, {}), written.get(i, {})
        keys = set(known) | set(unknown) | set(want)
        miss = 0
        for k in keys:
            if k in known:
                ok = want.get(k, 'missing') == known[k]
            elif k in unknown:
                # the checker could not see the pre-state value: nearcore must have committed the
                # key in this entry with the same final value (changed or not)
                ok = wrote.get(k, 'missing') == unknown[k]
            else:
                ok = False
            miss += not ok
        counts['attrib.entry'] += 1
        bad['attrib.entry'] += miss > 0
        counts['attrib.key'] += len(keys)
        bad['attrib.key'] += miss
        counts['attrib.unknownPre'] += len(unknown)


RECEIPT_FIELDS = ('id', 'predecessor', 'receiver', 'kind', 'bodyHash', 'refund')


def compare(lean_out, exp):
    """Per-field (compared, mismatched) counts and the list of mismatching field names."""
    counts = Counter()
    bad = Counter()
    lo = [norm_outcome(o, lean=True) for o in lean_out['outcomes']]
    eo = [norm_outcome(o) for o in exp['outcomes']]
    counts['outcomes.count'] += 1
    if len(lo) != len(eo):
        bad['outcomes.count'] += 1
    for a, b in zip(lo, eo):
        for f in OUTCOME_FIELDS:
            counts[f'outcome.{f}'] += 1
            if a[f] != b[f]:
                bad[f'outcome.{f}'] += 1
        # version 3: the failure kind of a failed outcome; each outcome's compute usage
        if b['status'] == 'failure' and b['failureKind'] is not None and 'computeUsage' in a_raw_keys(lean_out):
            counts['outcome.failureKind'] += 1
            if a['failureKind'] != b['failureKind']:
                bad['outcome.failureKind'] += 1
        if b['computeUsage'] is not None and a['computeUsage'] is not None:
            counts['outcome.computeUsage'] += 1
            if a['computeUsage'] != b['computeUsage']:
                bad['outcome.computeUsage'] += 1
    lr = [norm_receipt(r) for r in lean_out['outgoingReceipts']]
    er = [norm_receipt(r) for r in exp['outgoing_receipts']]
    counts['receipts.count'] += 1
    if len(lr) != len(er):
        bad['receipts.count'] += 1
    for a, b in zip(lr, er):
        for f in RECEIPT_FIELDS:
            counts[f'receipt.{f}'] += 1
            if a[f] != b[f]:
                bad[f'receipt.{f}'] += 1
    counts['refunds.count'] += 1
    if sum(r['refund'] for r in lr) != sum(r['refund'] for r in er):
        bad['refunds.count'] += 1
    if lean_out.get('stateChanges') is not None:
        lc, ec = norm_changes(lean_out['stateChanges']), norm_changes(exp['state_changes'])
        counts['stateChanges.keys'] += 1
        if set(lc) != set(ec):
            bad['stateChanges.keys'] += 1
        for k in set(lc) & set(ec):
            counts['stateChange.value'] += 1
            if lc[k] != ec[k]:
                bad['stateChange.value'] += 1
    if exp.get('compute_usage') is not None and lean_out.get('computeUsage') is not None:
        counts['computeUsage'] += 1
        if lean_out['computeUsage'] != expected_compute(exp):
            bad['computeUsage'] += 1
    for lk, ek in (('outcomeRoot', 'outcome_root'), ('gasUsed', 'gas_used'),
                   ('balanceBurnt', 'balance_burnt')):
        counts[f'chunk.{lk}'] += 1
        if lean_out[lk] != exp[ek]:
            bad[f'chunk.{lk}'] += 1
    compare_attribution(lean_out, exp, counts, bad)
    return counts, bad


def a_raw_keys(lean_out):
    """The keys of a Lean row's first outcome (a version-3 row reports `computeUsage` per outcome)."""
    return lean_out['outcomes'][0].keys() if lean_out['outcomes'] else ()


def recompute_checks(lean_out, exp):
    """The outcome root recomputed from each side's emitted outcome list (independent hashing)."""
    header = exp['header_prev_outcome_root']
    lean_root = merkle_root([outcome_leaf(o) for o in lean_out['outcomes']]).hex()
    exp_root = merkle_root([outcome_leaf(o) for o in exp['outcomes']]).hex()
    leaves_ok = all(outcome_leaf(o).hex() == o['leaf'] for o in lean_out['outcomes'])
    return {'lean_list_hashes_to_header': lean_root == header,
            'lean_list_hashes_to_lean_root': lean_root == lean_out['outcomeRoot'],
            'lean_leaves_recomputed': leaves_ok,
            'nearcore_list_hashes_to_header': exp_root == header,
            'nearcore_store_ids_match': exp.get('store_outcome_ids') == [o['id'] for o in exp['outcomes']]}


# ---- wrong-observable controls: one field of the expected record mutated

def _flip_hex(h):
    if not h:
        return '00'
    return ('0' if h[0] != '0' else '1') + h[1:]


def _bump(s):
    return str(int(s) + 1)


def mutations(exp):
    """(name, mutated-field, mutator) applicable to this record."""
    out = []
    os_ = exp['outcomes']
    if os_:
        out += [('outcome.gasBurnt+1', 'outcome.gasBurnt', lambda e: e['outcomes'][0].__setitem__('gasBurnt', _bump(e['outcomes'][0]['gasBurnt']))),
                ('outcome.tokensBurnt+1', 'outcome.tokensBurnt', lambda e: e['outcomes'][-1].__setitem__('tokensBurnt', _bump(e['outcomes'][-1]['tokensBurnt']))),
                ('outcome.executor', 'outcome.executor', lambda e: e['outcomes'][0].__setitem__('executor', _flip_hex(e['outcomes'][0]['executor']))),
                ('outcome.id', 'outcome.id', lambda e: e['outcomes'][-1].__setitem__('id', _flip_hex(e['outcomes'][-1]['id']))),
                ('outcome.extra_log', 'outcome.logs', lambda e: e['outcomes'][0]['logs'].append('00')),
                ('outcomes.drop_last', 'outcomes.count', lambda e: e['outcomes'].pop())]
        withids = [i for i, o in enumerate(os_) if o['receiptIds']]
        if withids:
            i = withids[0]
            out.append(('outcome.receiptIds', 'outcome.receiptIds', lambda e, i=i: e['outcomes'][i]['receiptIds'].pop()))
        logs = [i for i, o in enumerate(os_) if o['logs']]
        if logs:
            i = logs[0]
            out.append(('outcome.log_byte', 'outcome.logs', lambda e, i=i: e['outcomes'][i]['logs'].__setitem__(0, _flip_hex(e['outcomes'][i]['logs'][0]))))
        vals = [i for i, o in enumerate(os_) if o['status']['kind'] == 'value']
        if vals:
            i = vals[0]
            out.append(('outcome.returnData', 'outcome.returnData', lambda e, i=i: e['outcomes'][i]['status'].__setitem__('value', e['outcomes'][i]['status']['value'] + '00')))
        fails = [i for i, o in enumerate(os_) if o['status']['kind'] == 'failure']
        if fails:
            i = fails[0]
            out.append(('outcome.failure->value', 'outcome.status', lambda e, i=i: e['outcomes'][i].__setitem__('status', {'kind': 'value', 'value': ''})))
        elif vals:
            i = vals[0]
            out.append(('outcome.value->failure', 'outcome.status', lambda e, i=i: e['outcomes'][i].__setitem__('status', {'kind': 'failure'})))
    rs = exp['outgoing_receipts']
    if rs:
        out += [('receipt.bodyHash', 'receipt.bodyHash', lambda e: e['outgoing_receipts'][0].__setitem__('hash', _flip_hex(e['outgoing_receipts'][0]['hash']))),
                ('receipt.receiver', 'receipt.receiver', lambda e: e['outgoing_receipts'][-1].__setitem__('receiver', _flip_hex(e['outgoing_receipts'][-1]['receiver']))),
                ('receipts.drop_last', 'receipts.count', lambda e: e['outgoing_receipts'].pop())]
        refunds = [i for i, r in enumerate(rs) if r['predecessor'] == SYSTEM]
        if refunds:
            i = refunds[0]
            out.append(('refund.unmark', 'receipt.refund', lambda e, i=i: e['outgoing_receipts'][i].__setitem__('predecessor', _flip_hex(SYSTEM))))
    cs = exp['state_changes']
    if cs:
        out += [('stateChange.value', 'stateChange.value', lambda e: e['state_changes'][0].__setitem__('valueHash', _flip_hex(e['state_changes'][0]['valueHash'] or ''))),
                ('stateChanges.drop', 'stateChanges.keys', lambda e: e['state_changes'].pop())]
        dels = [i for i, c in enumerate(cs) if c['valueHash'] is not None]
        if dels:
            i = dels[-1]
            out.append(('stateChange.write->delete', 'stateChange.value', lambda e, i=i: e['state_changes'][i].update(valueHash=None, valueLen=None)))
    if exp.get('compute_usage') is not None:
        if e_has_outcome_compute(exp):
            out.append(('computeUsage+1', 'computeUsage', lambda e: e['outcomes'][0].__setitem__('computeUsage', _bump(e['outcomes'][0]['computeUsage']))))
            out.append(('outcome.computeUsage+1', 'outcome.computeUsage', lambda e: e['outcomes'][-1].__setitem__('computeUsage', _bump(e['outcomes'][-1]['computeUsage']))))
    kinds = [i for i, o in enumerate(os_) if o['status']['kind'] == 'failure' and o['status'].get('error')]
    if kinds:
        i = kinds[0]
        out.append(('outcome.failureKind', 'outcome.failureKind', lambda e, i=i: e['outcomes'][i]['status'].__setitem__(
            'error', _other_kind(e['outcomes'][i]['status']['error']))))
    if has_attribution(exp):
        attributed = [i for i, c in enumerate(cs) if attrib_key(c['key'])
                      and cause_id(c['changes'][-1]['cause'])
                      and c['changes'][-1]['valueHash'] is not None and _last_effective(c)]
        if attributed:
            i = attributed[0]
            out.append(('attrib.value', 'attrib.entry', lambda e, i=i: e['state_changes'][i]['changes'][-1].__setitem__(
                'valueHash', _flip_hex(e['state_changes'][i]['changes'][-1]['valueHash']))))
            out.append(('attrib.cause', 'attrib.entry', lambda e, i=i: _move_cause(e['state_changes'][i])))
    return out


def _last_effective(c):
    """The key's last change sets a value different from the one before it (pre-state or the previous
    change): moving or altering it is observable under the effective-change definition."""
    pre = c.get('pre') or {}
    if 'error' in pre:
        return False
    prev = None if pre.get('absent') else pre.get('valueHash')
    if len(c['changes']) > 1:
        prev = c['changes'][-2]['valueHash']
    return c['changes'][-1]['valueHash'] != prev


def _other_kind(err):
    """A failure whose canonical kind differs from `err`'s."""
    base = failure_kinds.canonical_expected(err)
    for cand in ('InvalidTxError(Expired)', 'InvalidTxError(InvalidNonce { tx_nonce: 1, ak_nonce: 1 })',
                 'ActionError(ActionError { index: Some(0), kind: AccountDoesNotExist { account_id: AccountId("x") } })',
                 'ActionError(ActionError { index: Some(0), kind: AccountAlreadyExists { account_id: AccountId("x") } })'):
        if failure_kinds.canonical_expected(cand) != base:
            return cand
    raise AssertionError(base)


def _move_cause(c):
    """Re-attribute the key's last attributed change to a different (unknown) receipt id."""
    for ch in reversed(c['changes']):
        if cause_id(ch['cause']):
            ch['cause'] = 'ReceiptProcessing { receipt_hash: 11111111111111111111111111111111 }'
            return


def e_has_outcome_compute(exp):
    return bool(exp['outcomes']) and exp['outcomes'][0].get('computeUsage') is not None


def run_controls(lean_out, exp):
    res = []
    for name, field, f in mutations(exp):
        e = copy.deepcopy(exp)
        f(e)
        _, bad = compare(lean_out, e)
        res.append({'control': name, 'field': field, 'detected': bad[field] > 0,
                    'reported': sorted(k for k, v in bad.items() if v)})
    return res


# ---- driver

def load_expected(paths):
    idx = {}
    for p in paths:
        op = gzip.open if str(p).endswith('.gz') else open
        with op(p, 'rt') as f:
            for line in f:
                if line.strip():
                    r = json.loads(line)
                    idx[(r['claim_sha256'], r['witness_sha256'])] = r
    return idx


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--binary', type=Path, required=True)
    p.add_argument('--cases', type=Path, required=True, help='one case directory per line (relative to --root)')
    p.add_argument('--root', type=Path, default=Path('.'))
    p.add_argument('--expected', type=Path, nargs='+', required=True, help='nearcore-observables-*.jsonl[.gz]')
    p.add_argument('--out', type=Path, required=True)
    p.add_argument('--tier', default='allFeatures')
    p.add_argument('--jobs', type=int, default=8)
    p.add_argument('--timeout', type=int, default=600)
    p.add_argument('--controls', type=int, default=200, help='matching cases that also get mutated-expected controls')
    p.add_argument('--seed', type=int, default=1)
    p.add_argument('--label', default='')
    a = p.parse_args()
    a.out.mkdir(parents=True, exist_ok=False)
    binary = (a.out / 'checker').resolve()
    shutil.copy2(a.binary, binary)
    expected = load_expected(a.expected)
    names = [l.strip() for l in a.cases.read_text().splitlines() if l.strip()]
    blind_root = Path(tempfile.mkdtemp(prefix='w01-blind-'))
    rng = random.Random(a.seed)
    # control candidates fixed up front (only their computed/expected pairs are kept in memory)
    candidates = set(rng.sample(names, min(len(names), 3 * a.controls)))

    def lean_row(case):
        proc = subprocess.run([str(binary), '--tier', a.tier, '--blind-full', str(case)], capture_output=True,
                              text=True, timeout=a.timeout)
        lines = proc.stdout.splitlines()
        if len(lines) != 1:
            raise ValueError(f'expected one result line, got {len(lines)} (exit {proc.returncode})')
        row = json.loads(lines[0])
        if row.get('case') != str(case) or row.get('outputsVersion') not in (2, 3):
            raise ValueError('result identity / version mismatch')
        return row

    def run(name):
        case = (a.root / name).resolve()
        key = (sha_file(case / 'claim.bin'), sha_file(case / 'witness.bin'))
        exp = expected.get(key)
        if exp is None:
            return dict(case=name, category='no_expected')
        if exp['status'] != 'ok':
            return dict(case=name, category='nearcore_' + exp['status'].split(':')[0])
        blind = blind_root / name.replace('/', '__')
        try:
            header_exp, _ = blind_inputs.blind_case(case, None, blind)
            row = lean_row(blind)
        except Exception as e:
            return dict(case=name, category='error', error=str(e))
        finally:
            shutil.rmtree(blind, ignore_errors=True)
        if row['verdict'] != 'accept':
            return dict(case=name, category='lean_' + row['verdict'], reason=row.get('reason', ''))
        out = row['outputs']
        counts, bad = compare(out, exp)
        header_diffs = blind_inputs.compare_outputs(header_exp, out)
        rc = recompute_checks(out, exp)
        ok = not any(bad.values()) and not header_diffs and all(rc.values()) and all(row['selfCheck'].values())
        diffs = sorted(k for k, v in bad.items() if v)
        res = dict(case=name, category='match' if ok else 'mismatch', counts=dict(counts), bad=dict(bad),
                   field_diffs=diffs, header_diffs=header_diffs, recompute=rc, selfCheck=row['selfCheck'],
                   n_outcomes=len(out['outcomes']), n_receipts=len(out['outgoingReceipts']),
                   n_changes=len(out['stateChanges'] or []),
                   n_logs=sum(len(o['logs']) for o in out['outcomes']),
                   n_return=sum(1 for o in out['outcomes'] if o['status']['kind'] == 'value' and o['status']['value']),
                   n_failures=sum(1 for o in out['outcomes'] if o['status']['kind'] == 'failure'),
                   n_refunds=sum(1 for r in out['outgoingReceipts'] if r['refund']))
        if not ok:
            res['lean'] = out
            res['expected'] = exp
        elif name in candidates:
            res['_pair'] = (out, exp)
        return res

    rows = []
    started = time.monotonic()
    with ThreadPoolExecutor(max_workers=a.jobs) as pool:
        for r in pool.map(run, names):
            rows.append(r)
            if len(rows) % 500 == 0:
                print(json.dumps({'processed': len(rows), 'total': len(names),
                                  'counts': dict(Counter(x['category'] for x in rows))}), flush=True)
    shutil.rmtree(blind_root, ignore_errors=True)
    matched = [r for r in rows if r['category'] == 'match']
    pool_ = [r for r in matched if '_pair' in r]
    sample = rng.sample(pool_, min(a.controls, len(pool_)))
    controls = []
    for r in sample:
        for c in run_controls(*r['_pair']):
            controls.append(dict(case=r['case'], **c))
    for r in rows:
        r.pop('_pair', None)
    with gzip.open(a.out / 'results.jsonl.gz', 'wt') as f:
        for r in rows:
            f.write(json.dumps(r) + '\n')
    with gzip.open(a.out / 'controls.jsonl.gz', 'wt') as f:
        for c in controls:
            f.write(json.dumps(c) + '\n')
    cats = Counter(r['category'] for r in rows)
    compared = Counter()
    mismatched = Counter()
    for r in rows:
        compared.update(r.get('counts', {}))
        mismatched.update(r.get('bad', {}))
    per_field = {k: {'compared': compared[k], 'matched': compared[k] - mismatched[k], 'mismatched': mismatched[k]}
                 for k in sorted(compared)}
    ctl = Counter((c['control'], c['detected']) for c in controls)
    ctl_summary = {}
    for (name, det), n in sorted(ctl.items()):
        ctl_summary.setdefault(name, {'detected': 0, 'missed': 0})['detected' if det else 'missed'] += n
    exercised = Counter()
    for r in matched:
        for k in ('n_logs', 'n_return', 'n_failures', 'n_refunds', 'n_receipts', 'n_changes'):
            if r.get(k):
                exercised[k] += 1
    graded = cats['match'] + cats['mismatch']
    report = dict(label=a.label, cases=len(names), categories=dict(cats), graded=graded,
                  per_field=per_field, header_diffs=dict(Counter(k for r in rows for k in r.get('header_diffs', []))),
                  recompute_failures=dict(Counter(k for r in rows for k, v in r.get('recompute', {}).items() if not v)),
                  controls=dict(total=len(controls), detected=sum(c['detected'] for c in controls),
                                cases=len(sample), by_control=ctl_summary),
                  matched_cases_exercising=dict(exercised),
                  totals=dict(outcomes=sum(r.get('n_outcomes', 0) for r in matched),
                              receipts=sum(r.get('n_receipts', 0) for r in matched),
                              state_changes=sum(r.get('n_changes', 0) for r in matched)),
                  identities=dict(lean_binary_sha256=sha_file(binary), harness_sha256=sha_file(__file__),
                                  expected=[str(x) for x in a.expected], tier=a.tier,
                                  cases_list_sha256=sha_file(a.cases)),
                  elapsed_seconds=time.monotonic() - started)
    report['pass'] = (graded > 0 and cats['mismatch'] == 0 and cats['error'] == 0 and
                      report['controls']['detected'] == report['controls']['total'])
    (a.out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: report[k] for k in ('label', 'cases', 'categories', 'controls', 'pass')}, indent=1))
    return 0 if report['pass'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
