#!/usr/bin/env python3
"""Independently check the split SHA proof's public contract, not full NEAR validity."""
import argparse
import hashlib
import json
import struct
from pathlib import Path
from audit_export import Reader
from audit_hash_events import expected_dense
from audit_public_merkle import reconstruct
from hash_template_root import POLICY


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('packet',type=Path);p.add_argument('messages',type=Path);p.add_argument('root',type=Path);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    data=a.packet.read_bytes();r=Reader(data);assert r.take(8)==b'NPNOMRK2';parts=[r.take(r.integer()) for _ in range(7)];r.done()
    messages=json.loads(a.messages.read_text());original_dense,original_wire=expected_dense(messages)
    rows=[original_wire[i:i+41] for i in range(12,len(original_wire),41) if int.from_bytes(original_wire[i:i+4],'little')%16!=6]
    assert parts[0]==b'NPNOMRK1'+struct.pack('<I',len(rows))+b''.join(rows)
    records={}
    for row in rows:
        ident,length,flag=struct.unpack('<IIB',row[:9]);assert ident not in records and ident%16!=6;records[ident]=(length,flag,row[9:])
    leaves=sorted(i for i in records if i%16==4);assert leaves==[4+16*i for i in range(len(leaves))]
    assert all(records[i][:2]==(68,1) for i in leaves)
    native,outcome_root=reconstruct([records[i][2] for i in leaves])
    for ident,(pre,digest) in native.items():assert ident not in records;records[ident]=(64,1,digest)
    source={m['id']:(len(m['bytes']),m['dmult'],hashlib.sha256(bytes(m['bytes'])).digest()) for m in messages}
    assert records==source
    buckets=[[] for _ in POLICY]
    for ident,(length,flag,digest) in records.items():
        bi=next(i for i,(blocks,_) in enumerate(POLICY) if (length+72)//64<=blocks)
        buckets[bi].append((ident,length,flag,digest))
    dense=bytearray(b'NEARSHATEMPL0001'+struct.pack('>Q',3088))
    for bucket,(_,count) in zip(buckets,POLICY):
        bucket.sort();assert len(bucket)<=count
        for i in range(count):
            if i<len(bucket):ident,length,flag,digest=bucket[i];active,tag=1,(ident<<32)|(length<<1)|flag
            else:active,tag,digest=0,0,hashlib.sha256(b'').digest()
            dense.extend(struct.pack('>QQ',active,tag)+digest)
    assert bytes(dense)==original_dense and hashlib.sha512(dense).digest()==a.root.read_bytes()
    report={'status':'SAME_COMPLETE_JOB_ROOT_NOT_FULL_NEAR_STATEMENT','packet_bytes':len(data),
        'packet_sha256':hashlib.sha256(data).hexdigest(),'source_sha256':hashlib.sha256(a.messages.read_bytes()).hexdigest(),
        'proven_sha_jobs':len(rows),'native_merkle_jobs':len(native),'complete_sha_jobs':len(messages),
        'outcome_root_hex':outcome_root.hex() if outcome_root else None,'expected_complete_job_root':a.root.read_bytes().hex(),
        'all_complete_source_records_equal':True,'complete_root_matches_external_expected':True,
        'sections':dict(zip(['public_records','tape','claim','left_rns','opening_rns','norms','backend'],map(len,parts))),
        'limitations':['Job-root-to-NEAR-claim binding remains outside this component.',
            'D0a outcome-tree semantics only; no D1 transaction-leaf equivalence claim.',
            'Other SHA bin, receipt byte buses, Wasm/state constraints, history recursion and composed PQ analysis remain open.']}
    a.output.write_text(json.dumps(report,indent=2)+'\n');print(report['packet_bytes'],report['proven_sha_jobs'],report['native_merkle_jobs'],report['complete_root_matches_external_expected'])


if __name__=='__main__':main()
