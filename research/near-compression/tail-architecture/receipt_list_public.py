#!/usr/bin/env python3
"""Independent dense public statement for the diagnostic ordered-list circuit.

NPMULT02: 16x18-word account table first, then per-list context/records.
"""
import argparse, json, struct
from pathlib import Path
from make_account_ledger_fixture import build as build_ledger, SLOTS, ROW

def table_words(ledger_json):
    fixture = build_ledger(ledger_json)
    words = []
    for r in range(SLOTS):
        row = fixture[41+r*ROW:41+(r+1)*ROW]
        active, name_len = struct.unpack_from('<QQ', row, 0)
        name = row[16:80]
        initial = row[80:152]
        final = row[152:224]
        words += [active, name_len] + [int.from_bytes(name[i:i+8],'little') for i in range(0,64,8)]
        words += [int.from_bytes(initial[i:i+8],'little') for i in range(0,16,8)]
        words += [int.from_bytes(initial[i:i+8],'little') for i in range(16,32,8)]
        words += [int.from_bytes(initial[i:i+8],'little') for i in range(64,72,8)] + [0]
        words += [int.from_bytes(final[i:i+8],'little') for i in range(0,16,8)]
    assert len(words) == SLOTS*18
    return struct.pack('<%dQ' % len(words), *words)

def emit(raw,cap):
 assert raw[:8]==b'NPLST001'
 count=struct.unpack_from('<I',raw,40)[0]
 assert count<=cap and len(raw)==76+504*count
 public=raw[8:40]+struct.pack('<Q',count)
 public+=b''.join(struct.pack('<Q',int.from_bytes(raw[i:i+8],'big')) for i in range(44,76,8))
 for i in range(cap):
  out=[0]*11
  if i<count:
   w=struct.unpack_from('<63Q',raw,76+504*i)
   out=[1,i,w[21]+(69 if w[57] or w[58] else 37),*w[30:34],*w[59:63]]
  public+=struct.pack('<11Q',*out)
 assert len(public)==8*(9+11*cap)
 return public
if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('fixture',type=Path);p.add_argument('capacity',int,type=int);p.add_argument('output',type=Path);p.add_argument('ledger',type=Path);a=p.parse_args()
 ledger_json=json.loads(a.ledger.read_text())
 a.output.write_bytes(table_words(ledger_json)+emit(a.fixture.read_bytes(),a.capacity))
