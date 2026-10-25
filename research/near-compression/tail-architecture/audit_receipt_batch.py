#!/usr/bin/env python3
"""Audit batch packet public bytes against independent fixtures, not proof soundness."""
import argparse,hashlib,json
from pathlib import Path
from audit_export import Reader
from receipt_batch_public import emit,compact
p=argparse.ArgumentParser(description=__doc__);p.add_argument('packet',type=Path);p.add_argument('batch',type=Path);p.add_argument('--output',type=Path,required=True);a=p.parse_args();data=a.packet.read_bytes();r=Reader(data);magic=r.take(8);assert magic in [b'NPRCBP01',b'NPRCBP02',b'NPRCBU01'];parts=[r.take(r.integer()) for _ in range(7)];r.done();unified=magic==b'NPRCBU01';expected,root=emit(a.batch.read_bytes(),unified);assert parts[0]==(expected if magic==b'NPRCBP01' else compact(expected,unified));assert root==a.batch.with_suffix('.root').read_bytes();assert expected[:24]==a.batch.with_suffix('.context').read_bytes()
report={'status':'PRIVATE_RECEIPT_KERNEL_PACKET_NOT_FULL_NEAR','packet_version':magic.decode(),'packet_bytes':len(data),'packet_sha256':hashlib.sha256(data).hexdigest(),'batch_sha256':hashlib.sha256(a.batch.read_bytes()).hexdigest(),'public_bytes_equal_independent_fixture':True,'outcome_root_matches_external':True,'outcome_root':root.hex(),'sections':dict(zip(['public','tape','claimed_value','left_rns','opening_rns','norms','backend'],map(len,parts))),'limitations':['Other hash jobs/source/state authentication/history omitted.','Declared context is external input, not proved here from full claim.','Backend security and byte-level proof verification are separate checks.']}
a.output.write_text(json.dumps(report,indent=2)+'\n');print(a.packet.name,len(data),root.hex())
