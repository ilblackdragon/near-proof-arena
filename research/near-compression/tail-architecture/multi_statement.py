#!/usr/bin/env python3
"""Host checks for ordered source sets and their outcome root; proof verification separate.

NPMULT03 leads the public statement with the claim's prev_state_root (4
words), then the bounded account table (16 rows x 18 words). The table is
checked against the receipts: canonical names, initial/final structure,
exactly the distinct receiver set, and the host ledger model threads
balances in order (this duplicates the circuit's constraint independently).
The root words must match the expected claim-derived prev_state_root.
"""
import hashlib
import struct
from audit_source_membership import root_from_digest
from audit_public_merkle import reconstruct

ACCOUNT_SLOTS = 16
ROOT_WORDS = 4
ROW_WORDS = 18
TABLE_WORDS = ACCOUNT_SLOTS*ROW_WORDS


def require(ok, message):
    if not ok:
        raise ValueError(message)


def encode(packet, paths):
    return (b'NPMSET01' + struct.pack('<I', len(packet)) + packet + struct.pack('<I', len(paths)) +
            b''.join(struct.pack('<I', len(p)) + b''.join(bytes([x['direction']]) + bytes(x['sibling']) for x in p) for p in paths))


def parse_table(words):
    """Parse the 16-row account table; return list of (name, balance, locked, storage, final)."""
    rows = []
    for r in range(ACCOUNT_SLOTS):
        row = words[r*ROW_WORDS:(r+1)*ROW_WORDS]
        active, name_len = row[0], row[1]
        name_words = row[2:10]
        balance = row[10], row[11]
        locked = row[12], row[13]
        storage = row[14], row[15]
        final = row[16], row[17]
        if active == 0:
            require(not any(row), 'inactive table row not zero')
            continue
        require(active == 1, 'active flag')
        require(1 <= name_len <= 64, 'name length range')
        raw = b''.join(w.to_bytes(8, 'little') for w in name_words)
        require(not any(raw[name_len:]), 'name padding')
        rows.append((raw[:name_len], balance, locked, storage, final))
    return rows


def check(envelope, caps, mode, expected, outcome_root, ledger_fixture=None):
    """Return packet/public after claim-relative checks, NOT proof acceptance.

    expected comes from trusted claim-only derivation; outcome_root from expected
    claim. Caller must verify returned packet with returned public and fixed caps/
    mode. The account-table/trie-root binding is checked separately
    (audit_account_paths.py); when ledger_fixture is given, the table words must
    equal the native ledger fixture byte-for-byte (active rows, names, initial
    balance/locked/storage and final balances).
    """
    require(16 <= len(envelope) <= 300000 and envelope[:8] == b'NPMSET01', 'envelope')
    size = struct.unpack_from('<I', envelope, 8)[0]
    pos = 12 + size
    require(size >= 24 and pos+4 <= len(envelope), 'packet framing')
    packet = envelope[12:pos]
    count = struct.unpack_from('<I', envelope, pos)[0]
    pos += 4
    require(count == len(caps) == len(expected['sources']), 'complete source count')
    paths = []
    for _ in range(count):
        require(pos+4 <= len(envelope), 'path header')
        depth = struct.unpack_from('<I', envelope, pos)[0]
        pos += 4
        require(pos+33*depth <= len(envelope), 'path length')
        paths.append([{'direction': envelope[pos+33*i], 'sibling': list(envelope[pos+33*i+1:pos+33*i+33])} for i in range(depth)])
        pos += 33*depth
    require(pos == len(envelope), 'trailing data')
    header = 20+4*count
    require(len(packet) >= header+8 and packet[:8] == b'NPMULT03', 'packet version')
    require(struct.unpack_from('<I', packet, 8)[0] == count, 'profile count')
    require(list(struct.unpack_from('<'+str(count)+'I', packet, 12)) == caps, 'profile capacities')
    require(struct.unpack_from('<I', packet, 12+4*count)[0] == mode, 'profile mode')
    require(struct.unpack_from('<I', packet, 16+4*count)[0] == ACCOUNT_SLOTS, 'account table size')
    plen = struct.unpack_from('<Q', packet, header)[0]
    require(plen == 8*(ROOT_WORDS+TABLE_WORDS+sum(9+11*c for c in caps)) and header+8+plen <= len(packet), 'public framing')
    public = packet[header+8:header+8+plen]
    # Account table: canonical names, distinct, structure.
    root_words = struct.unpack_from('<4Q', public, 0)
    require(bytes(expected['pre_state_root']) == b''.join(w.to_bytes(8, 'big') for w in root_words),
            'claim prev_state_root')
    table_words = struct.unpack_from('<%dQ' % TABLE_WORDS, public, 8*ROOT_WORDS)
    rows = parse_table(table_words)
    names = [r[0] for r in rows]
    require(len(set(names)) == len(names), 'duplicate account names')
    if ledger_fixture is not None:
        fixture = ledger_fixture
        require(len(fixture) == 41+ACCOUNT_SLOTS*224 and fixture[:9] == b'NPMLEDG01', 'ledger fixture')
        require(len(rows) > 0, 'active rows')
        frows = []
        for r in range(ACCOUNT_SLOTS):
            frow = fixture[41+r*224:41+(r+1)*224]
            active, name_len = struct.unpack_from('<QQ', frow, 0)
            if active == 0:
                require(not any(frow), 'inactive fixture row')
                continue
            name = frow[16:16+name_len]
            initial = frow[80:152]
            final = frow[152:224]
            frows.append((name, initial, final))
        require(len(frows) == len(rows), 'active row count')
        for (name, initial, final), (tname, tb, tl, ts, tf) in zip(frows, rows):
            require(name == tname, 'account name differs from native ledger')
            require(tb == struct.unpack_from('<2Q', initial, 0), 'initial balance differs')
            require(tl == struct.unpack_from('<2Q', initial, 16), 'locked differs')
            require(ts[0] == struct.unpack_from('<Q', initial, 64)[0] and ts[1] == 0, 'storage differs')
            require(tf == struct.unpack_from('<2Q', final, 0), 'final balance differs')
    off = 8*(ROOT_WORDS+TABLE_WORDS)
    leaves, ids, counts, receivers = [], [], [], []
    for index, cap in enumerate(caps):
        words = struct.unpack_from('<'+str(9+11*cap)+'Q', public, off)
        require(list(words[:4]) == expected['context'], 'claim context')
        n = words[4]
        require(n <= cap, 'receipt count')
        counts.append(n)
        leaf = b''.join(x.to_bytes(8, 'big') for x in words[5:9])
        require(root_from_digest(leaf, paths[index]) == bytes(expected['sources'][index]['root']), 'ordered source membership')
        for i in range(cap):
            row = words[9+11*i:20+11*i]
            if i >= n:
                require(not any(row), 'inactive output')
                continue
            require(row[0] == 1 and row[1] == i, 'ordered active output')
            rid = struct.pack('<4Q', *row[3:7])
            ids.append(rid)
            h = b''.join(x.to_bytes(8, 'big') for x in row[7:11])
            leaves.append(hashlib.sha256(struct.pack('<I', 2)+rid+h).digest())
        off += 8*(9+11*cap)
    require(len(set(ids)) == len(ids), 'duplicate receipt id')
    root = reconstruct(leaves)[1] or bytes(32)
    require(root == outcome_root, 'claim outcome root')
    return packet, public, counts, rows
