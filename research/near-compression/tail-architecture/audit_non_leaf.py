#!/usr/bin/env python3
"""Check native leaf packets against independent original-message fixtures."""
import argparse
import hashlib
import json
from pathlib import Path
from audit_export import Reader

p=argparse.ArgumentParser(description=__doc__)
p.add_argument('packet',type=Path);p.add_argument('fixture',type=Path);p.add_argument('root',type=Path);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
data=a.packet.read_bytes();r=Reader(data);assert r.take(8)==b'NPNOLEF2'
parts=[r.take(r.integer()) for _ in range(7)];r.done()
assert parts[0]==a.fixture.read_bytes()
assert a.fixture.with_suffix('.root').read_bytes()==a.root.read_bytes()
count=int.from_bytes(parts[0][8:12],'little');end=12+41*count
leaves=int.from_bytes(parts[0][end:end+4],'little');assert len(parts[0])==end+4+32*leaves
report={'status':'COMPONENT_PUBLIC_INTERFACE_NOT_FULL_NEAR','packet_bytes':len(data),'packet_sha256':hashlib.sha256(data).hexdigest(),'fixture_sha256':hashlib.sha256(a.fixture.read_bytes()).hexdigest(),'proven_sha_jobs':count,'native_leaf_jobs':leaves,'native_internal_jobs':max(0,leaves-1),'expected_original_root':a.root.read_bytes().hex(),'sections':list(map(len,parts)),'public_bytes_equal_independent_original_message_fixture':True,'limitations':['Cryptographic verification occurs separately in the fresh native process.','Original job-root link to NEAR claim and recursive history still missing.']}
a.output.write_text(json.dumps(report,indent=2)+'\n');print(report)
