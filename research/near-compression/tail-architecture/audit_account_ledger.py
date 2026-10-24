#!/usr/bin/env python3
"""Independent ordered balance model; native account-root authentication is trusted."""
import argparse
import hashlib
import json
import struct
from pathlib import Path


def decode_multi(raw):
    assert raw[:8] == b'NPMULF01'
    n = struct.unpack_from('<I', raw, 8)[0]
    pos, parts = 12, []
    for _ in range(n):
        size = struct.unpack_from('<Q', raw, pos)[0]
        pos += 8
        parts.append(raw[pos:pos+size])
        pos += size
    assert pos == len(raw)
    return parts


def check(parts, accounts):
    state, original, expected_final = {}, {}, {}
    for account in accounts:
        receiver = bytes(account['receiver'])
        initial, final = bytes(account['initial']), bytes(account['final'])
        assert receiver and len(receiver) <= 64 and receiver not in state
        assert len(initial) == len(final) == 72
        state[receiver] = initial
        original[receiver] = initial
        expected_final[receiver] = final
    seen, previous = set(), {}
    total, repeats, cross_list = 0, 0, 0
    for li, part in enumerate(parts):
        assert part[:8] == b'NPLST001'
        n = struct.unpack_from('<I', part, 40)[0]
        assert len(part) == 76+504*n
        for ri in range(n):
            words = struct.unpack_from('<63Q', part, 76+504*ri)
            length = words[21]
            raw_receiver = struct.pack('<8Q', *words[22:30])
            assert 1 <= length <= 64 and not any(raw_receiver[length:])
            receiver = raw_receiver[:length]
            assert receiver in state, 'receiver absent from initial table'
            value = state[receiver]
            before = words[0] + (words[1] << 64)
            deposit = words[2] + (words[3] << 64)
            locked = words[4] + (words[5] << 64)
            storage = words[6] + (words[7] << 64)
            assert before == int.from_bytes(value[:16], 'little'), f'ordered balance mismatch list={li} receipt={ri}'
            assert locked == int.from_bytes(value[16:32], 'little'), 'locked changed'
            assert storage == int.from_bytes(value[64:72], 'little'), 'storage changed'
            after = before + deposit
            assert after < (1 << 128)-1
            assert after == words[53] + (words[54] << 64), 'recorded after mismatch'
            state[receiver] = after.to_bytes(16, 'little') + value[16:]
            if receiver in previous:
                repeats += 1
                cross_list += previous[receiver][0] != li
            previous[receiver] = (li, ri)
            seen.add(receiver)
            total += 1
    assert seen == set(state), 'extra account entries'
    assert state == expected_final, 'final account mismatch'
    # Receiver bytes + initial account + final amount; code/locked/storage unchanged.
    table_bytes = 4 + sum(4+len(k)+72+16 for k in state)
    return {'receipts': total, 'accounts': len(state), 'repeated_updates': repeats,
            'cross_list_links': cross_list, 'candidate_public_table_bytes': table_bytes}


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    for name in ['exports', 'lists', 'ledgers', 'claims', 'output']:
        p.add_argument(name, type=Path)
    p.add_argument('--mutant', type=Path)
    a = p.parse_args()
    rows, negatives = [], 0
    for file in sorted(a.ledgers.glob('*.json')):
        case = file.stem
        ledger = json.loads(file.read_text())
        cb = (a.claims/case/'claim.bin').read_bytes()
        assert hashlib.sha256(cb).digest() == bytes(ledger['claim_sha256'])
        v = json.loads((a.exports/case/'rcpt.json').read_text())
        parts = [(a.lists/f'{case}-list{i}.list').read_bytes() for i in range(len(v['lists']))]
        result = check(parts, ledger['accounts'])
        if ledger['accounts']:
            for side in ['initial', 'final']:
                changed = json.loads(json.dumps(ledger['accounts']))
                changed[0][side][0] ^= 1
                try:
                    check(parts, changed)
                except AssertionError:
                    negatives += 1
                else:
                    raise AssertionError('account mutation accepted')
        result.update({'case': case, 'claim_sha256': hashlib.sha256(cb).hexdigest(),
                       'all_main_value_bytes': ledger['all_main_value_bytes'],
                       'all_main_value_count': ledger['all_main_value_count']})
        rows.append(result)
    mutant_result = None
    if a.mutant:
        ledger = json.loads((a.ledgers/'00-h10035-s3.json').read_text())
        try:
            check(decode_multi(a.mutant.read_bytes()), ledger['accounts'])
        except AssertionError as error:
            mutant_result = str(error)
        else:
            raise AssertionError('forged repeated balance accepted by ledger model')
    report = {'status': 'ORDERED_ACCOUNT_MODEL_NOT_CIRCUIT_OR_STATE_AUTH_PROOF',
              'cases': rows, 'negative_checks': negatives, 'mutant_rejection': mutant_result,
              'max_accounts': max(r['accounts'] for r in rows),
              'limits': ['Initial account authentication and final-state commitment are trusted native exports.',
                         'This ordered register model is not yet constrained by the proof.',
                         'All main witness values are a size census, not a minimal account multiproof.']}
    a.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k:report[k] for k in ['status','negative_checks','max_accounts','mutant_rejection']}))
