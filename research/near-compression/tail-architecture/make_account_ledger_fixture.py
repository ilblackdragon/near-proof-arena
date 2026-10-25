#!/usr/bin/env python3
"""Fixed-format account table fixture (NPMLEDG01) from the native ledger JSON export.

Trusted local input for near-receipt-multi, generated from account-ledger-export
output. Layout: magic(8) || pre_state_root(32) || 16 rows of
active(8) || name_len(8) || name(64) || initial(72) || final(72).
"""
import json
import struct
import sys
from pathlib import Path

SLOTS = 16
ROW = 8+8+64+72+72
MAGIC = b'NPMLEDG01'
HEADER = len(MAGIC)+32


def build(ledger):
    accounts = ledger['accounts']
    assert len(accounts) <= SLOTS
    out = bytearray(MAGIC)
    out += bytes(ledger['pre_state_root'])
    for r in range(SLOTS):
        if r < len(accounts):
            a = accounts[r]
            name = bytes(a['receiver'])
            assert 1 <= len(name) <= 64 and not name[len(name):]
            initial, final = bytes(a['initial']), bytes(a['final'])
            assert len(initial) == 72 and len(final) == 72
            out += struct.pack('<Q', 1)
            out += struct.pack('<Q', len(name))
            out += name.ljust(64, b'\0')
            out += initial
            out += final
        else:
            out += bytes(ROW)
    assert len(out) == HEADER+SLOTS*ROW, len(out)
    return bytes(out)


if __name__ == '__main__':
    source, output = Path(sys.argv[1]), Path(sys.argv[2])
    output.write_bytes(build(json.loads(source.read_text())))
    print(output, HEADER+SLOTS*ROW, 'bytes')
