#!/usr/bin/env python3
"""Independently derive receipt-leaf reconstruction fixtures and complete roots."""
import argparse
import hashlib
import json
import struct
from pathlib import Path
from audit_hash_events import expected_dense
from audit_public_merkle import reconstruct

p=argparse.ArgumentParser(description=__doc__)
p.add_argument('corpus',type=Path);p.add_argument('output',type=Path);a=p.parse_args()
a.output.mkdir(parents=True,exist_ok=True)
cases=[(f.parent.name,json.loads(f.read_text())) for f in sorted(a.corpus.glob('*/sha_r.json'))]
assert len(cases)==64
for n in [0,1,2,3,5]:
    messages=[];digests=[]
    for i in range(n):
        peo=bytes([i])*17;rid=bytes([i+1])*32
        pre=b'\x02\0\0\0'+rid+hashlib.sha256(peo).digest()
        messages.extend([{'id':3+16*i,'bytes':list(peo),'dmult':1},{'id':4+16*i,'bytes':list(pre),'dmult':1}]);digests.append(hashlib.sha256(pre).digest())
    nodes,_=reconstruct(digests)
    messages.extend({'id':ident,'bytes':list(pre),'dmult':1} for ident,(pre,_) in nodes.items())
    cases.append((f'synthetic-{n}',messages))
for name,messages in cases:
    dense,wire=expected_dense(messages);byid={m['id']:m for m in messages}
    leaves=sorted((m for m in messages if m['id']%16==4),key=lambda m:m['id']);rids=[]
    assert len(leaves)==sum(m['id']%16==3 for m in messages)
    for i,m in enumerate(leaves):
        assert m['id']==4+16*i and m['dmult']==1
        pre=bytes(m['bytes']);peo=byid[m['id']-1]
        assert peo['dmult']==1 and len(pre)==68 and pre[:4]==b'\x02\0\0\0' and pre[36:]==hashlib.sha256(bytes(peo['bytes'])).digest()
        rids.append(pre[4:36])
    rows=[wire[i:i+41] for i in range(12,len(wire),41) if int.from_bytes(wire[i:i+4],'little')%16 not in [4,6]]
    compact=b'NPNOLEF1'+struct.pack('<I',len(rows))+b''.join(rows)+struct.pack('<I',len(rids))+b''.join(rids)
    (a.output/f'{name}.wire').write_bytes(compact);(a.output/f'{name}.root').write_bytes(hashlib.sha512(dense).digest())
print(f'Generated {len(cases)} receipt-leaf fixtures')
