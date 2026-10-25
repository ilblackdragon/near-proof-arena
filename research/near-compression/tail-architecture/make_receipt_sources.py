#!/usr/bin/env python3
"""Independent source-list/outcome shared-wire fixtures (not full NEAR claims)."""
import argparse, hashlib, json, struct
from pathlib import Path
from receipt_interface import G, arithmetic

def u64(n): return struct.pack('<Q', n)
def vec(b): return struct.pack('<I', len(b))+b
def digest_words(b):
 d=hashlib.sha256(b).digest()
 return b''.join(u64(int.from_bytes(d[i:i+8],'big')) for i in range(0,32,8))

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('exports',type=Path);p.add_argument('batches',type=Path);p.add_argument('output',type=Path);p.add_argument('--report',type=Path,required=True);a=p.parse_args()
 rows=[];singletons=0
 for f in sorted(a.exports.glob('*/rcpt.json')):
  view=json.loads(f.read_text());batch=(a.batches/(f.parent.name+'.batch')).read_bytes();i=0
  messages={x['id']:bytes(x['bytes']) for x in json.loads(f.with_name('sha_r.json').read_text())}
  for j,l in enumerate(view['lists']):
   for r in l['rs']:
    kernel=batch[40+364*i:400+364*i];assert len(kernel)==360;i+=1
    extra=u64(len(r['s']))+bytes(r['s']).ljust(64,b'\0')+u64(r['kt'])+bytes(r['pk']).ljust(64,b'\0')+u64(view['own'])
    encoded=vec(bytes(r['p']))+vec(bytes(r['v']))+bytes(r['rid'])+b'\0'+vec(bytes(r['s']))+bytes([r['kt']])+bytes(r['pk'])+bytes(r['gp'])+bytes(8)+b'\x01\0\0\0\x03'+bytes(r['dep'])
    source=u64(view['own'])+struct.pack('<I',1)+encoded
    if len(l['rs'])==1:assert source==messages[1+16*j];singletons+=1
    rows.append(kernel[:280]+extra+kernel[280:]+digest_words(source)+b'\x01')
 real=len(rows)
 for n in [1,7,8,9,31,32,55,56,63,64]:
  for kt in [0,1]:
   pre=b'p'*n;recv=b'r'*n;signer=b's'*n;key=bytes(range(32 if kt==0 else 64));rid=bytes(range(32));height=123;shard=3
   amounts=(10**28,17,0,182,5,3);after,burn,surplus=arithmetic(*amounts,False)
   refund=hashlib.sha256(rid+u64(height)+bytes(8)).digest()
   peo=struct.pack('<I',1)+refund+u64(G)+burn.to_bytes(16,'little')+vec(recv)+b'\x02\0\0\0\0'
   kernel=b''.join(x.to_bytes(16,'little') for x in amounts)+u64(n)+pre.ljust(64,b'\0')+u64(n)+recv.ljust(64,b'\0')+rid+u64(height)
   extra=u64(n)+signer.ljust(64,b'\0')+u64(kt)+key.ljust(64,b'\0')+u64(shard)
   source=u64(shard)+struct.pack('<I',1)+vec(pre)+vec(recv)+rid+b'\0'+vec(signer)+bytes([kt])+key+amounts[4].to_bytes(16,'little')+bytes(8)+b'\x01\0\0\0\x03'+amounts[1].to_bytes(16,'little')
   rows.append(kernel+extra+b''.join(x.to_bytes(16,'little') for x in [after,burn,surplus])+digest_words(peo)+digest_words(source)+b'\x01')
 # Full-word metadata guards, including high-bit-only length/key violations.
 base=rows[-1]
 for word,values in [(12,[0,65,1<<32]),(21,[0,65,1<<32]),(35,[65,1<<32]),(44,[2,3,1<<32,1<<63])]:
  for value in values:
   bad=bytearray(base);bad[8*word:8*word+8]=u64(value);bad[-1]=0;rows.append(bytes(bad))
 assert all(len(row)==545 for row in rows)
 blob=b'NPRSO001'+struct.pack('<I',len(rows))+b''.join(rows);a.output.write_bytes(blob)
 report={'status':'LOCAL_SOURCE_OUTCOME_FIXTURES_NOT_FULL_NEAR','real_receipts':real,'original_singleton_lists_matched':singletons,'synthetic_positive':20,'invalid_metadata':12,'cases':len(rows),'sha256':hashlib.sha256(blob).hexdigest(),'limits':['Non-singleton corpus receipts are wrapped in synthetic singleton lists.','No source inclusion, account authentication or recursive history.']}
 a.report.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
if __name__=='__main__':main()
