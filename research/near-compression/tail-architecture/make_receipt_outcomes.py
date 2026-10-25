#!/usr/bin/env python3
"""Independent expectations for shared-wire arithmetic/outcome hashing."""
import argparse,hashlib,json,struct
from pathlib import Path
from receipt_interface import arithmetic,receipt,integer,G,MAX
p=argparse.ArgumentParser(description=__doc__);p.add_argument('exports',type=Path);p.add_argument('output',type=Path);p.add_argument('--report',type=Path,required=True);a=p.parse_args();records=[];kinds=[];positive=0

def add(amounts,pre,receiver,rid,height,kind,expected_digest=None):
 global positive
 assert len(pre)<=64 and len(receiver)<=64 and len(rid)==32
 try:
  assert pre and receiver
  out=arithmetic(*amounts,pre==b'system');ok=1
  refund=hashlib.sha256(rid+height.to_bytes(8,'little')+bytes(8)).digest() if out[2] else b''
  peo=bool(out[2]).to_bytes(4,'little')+refund+G.to_bytes(8,'little')+out[1].to_bytes(16,'little')+len(receiver).to_bytes(4,'little')+receiver+b'\x02\0\0\0\0'
  digest=hashlib.sha256(peo).digest()
  if expected_digest is not None:assert digest==expected_digest
  positive+=out[1]!=0
 except AssertionError:
  assert expected_digest is None
  ok=0;out=(0,0,0);digest=bytes(32)
 words=b''.join(x.to_bytes(16,'little') for x in amounts)
 words+=struct.pack('<Q',len(pre))+pre.ljust(64,b'\0')+struct.pack('<Q',len(receiver))+receiver.ljust(64,b'\0')+rid+struct.pack('<Q',height)
 words+=b''.join(x.to_bytes(16,'little') for x in out)
 words+=b''.join(struct.pack('<Q',int.from_bytes(digest[i:i+8],'big')) for i in range(0,32,8))
 assert len(words)==360
 records.append(words+bytes([ok]));kinds.append(kind)

for f in sorted(a.exports.glob('*/rcpt.json')):
 v=json.loads(f.read_text())
 for l in v['lists']:
  for r in l['rs']:
   _,peo,_,_=receipt(r,v['height'],v['bgp'])
   add(tuple(integer(r,k) for k in ['bef','dep','lk','st','gp'])+(v['bgp'],),bytes(r['p']),bytes(r['v']),bytes(r['rid']),v['height'],'corpus',hashlib.sha256(peo).digest())
for length in [1,2,23,24,31,32,55,56,63,64]:
 for pre in [b'system',b'systemx',b'syste',b'user.near']:
  for gp,bgp in [(2,3),(3,3),(5,3),(MAX,MAX)]:
   add((10**28,17,0,182,gp,bgp),pre,b'a'*length,bytes(range(32)),(1<<64)-1,'synthetic-boundary')
for amounts in [(MAX-1,1,0,0,0,0),(MAX,1,0,0,0,0),(MAX-2,1,2,0,0,0),(0,0,0,771,0,0),(1,2,0,MAX,0,0)]:
 add(amounts,b'user.near',b'receiver',bytes(32),0,'invalid-arithmetic')
for pre,receiver in [(b'',b'receiver'),(b'user',b'')]:add((0,1,0,0,2,3),pre,receiver,bytes(32),0,'invalid-length')
blob=b'NPROU001'+struct.pack('<I',len(records))+b''.join(records);a.output.write_bytes(blob)
report={'status':'INDEPENDENT_KERNEL_EXPECTATIONS_NOT_FULL_NEAR','cases':len(records),'accepted':sum(r[-1] for r in records),'rejected':sum(1-r[-1] for r in records),'positive_burns':positive,'kinds':{k:kinds.count(k) for k in sorted(set(kinds))},'sha256':hashlib.sha256(blob).hexdigest(),'inputs':'six u128 amounts, predecessor length+64 bytes, receiver length+64 bytes, receipt id32, heightu64','outputs':'after/burnt/surplus u128 and SHA256 partial-outcome digest','limits':['Synthetic kernel vectors are not accepted NEAR claims.','No source/state/access-key/routing authentication.']};a.report.write_text(json.dumps(report,indent=2)+'\n');print(report)
