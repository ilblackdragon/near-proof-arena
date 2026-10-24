#!/usr/bin/env python3
"""Export independent arithmetic expectations for circuit evaluation."""
import argparse,json,random,struct,hashlib
from pathlib import Path
from receipt_interface import arithmetic,integer,MAX,G,STORAGE_PRICE
p=argparse.ArgumentParser(description=__doc__);p.add_argument('exports',type=Path);p.add_argument('output',type=Path);p.add_argument('--report',type=Path,required=True);a=p.parse_args();rows=[];labels=[]
for f in sorted(a.exports.glob('*/rcpt.json')):
 v=json.loads(f.read_text())
 for l in v['lists']:
  for r in l['rs']:rows.append(tuple(integer(r,k) for k in ['bef','dep','lk','st','gp'])+(v['bgp'],int(r['sys'])));labels.append('corpus')
# Exercise limb carry/borrow, min branches, exact maximum, multiplication and storage thresholds.
edges=[0,1,(1<<64)-1,1<<64,(1<<64)+1,MAX//G,MAX//G+1,MAX-1,MAX]
for gp in edges:
 for bgp in edges:
  for system in [0,1]:rows.append((1,2,0,0,gp,bgp,system));labels.append('gas-edge')
for before in edges:
 for deposit in edges:
  for locked in [0,1,(1<<64)-1,MAX]:rows.append((before,deposit,locked,0,0,0,0));labels.append('balance-edge')
for storage in [0,770,771,MAX//STORAGE_PRICE,MAX//STORAGE_PRICE+1,MAX]:
 for total in [0,770*STORAGE_PRICE,771*STORAGE_PRICE-1,771*STORAGE_PRICE,MAX-1]:rows.append((total,0,0,storage,0,0,0));labels.append('storage-edge')
rng=random.Random(86128)
for i in range(256):
 rows.append((rng.randrange(1<<100),rng.randrange(1<<100),rng.randrange(1<<100),rng.randrange(1<<20),rng.randrange(1<<80),rng.randrange(1<<80),i%2));labels.append('seeded')
blob=bytearray(b'NPRAR001'+struct.pack('<I',len(rows)));accepted=0;positive=0
for values in rows:
 try:out=arithmetic(*values);ok=1;accepted+=1;positive+=out[1]!=0
 except AssertionError:out=(0,0,0);ok=0
 blob+=b''.join(n.to_bytes(16,'little') for n in values[:6])+struct.pack('<Q',values[6])+b''.join(n.to_bytes(16,'little') for n in out)+bytes([ok])
a.output.write_bytes(blob);report={'status':'ARITHMETIC_EXPECTATIONS_NOT_NEAR_CLAIM_FIXTURES','cases':len(rows),'accepted':accepted,'rejected':len(rows)-accepted,'positive_burns':positive,'kinds':{k:labels.count(k) for k in sorted(set(labels))},'sha256':hashlib.sha256(blob).hexdigest()};a.report.write_text(json.dumps(report,indent=2)+'\n');print(report)
