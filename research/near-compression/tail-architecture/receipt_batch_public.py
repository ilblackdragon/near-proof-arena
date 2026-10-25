#!/usr/bin/env python3
"""Independent fixed-profile receipt batch public vector and outcome root."""
import argparse,hashlib,json,struct
from pathlib import Path
from audit_public_merkle import reconstruct
CAP=[1024,8,8,8]
def emit(batch,unified=False):
 caps=[1024] if unified else CAP
 assert batch[:8]==b'NPRCB001';ctx=batch[8:32];n=struct.unpack_from('<I',batch,32)[0];assert len(batch)==36+364*n
 groups=[[] for _ in caps];leaves=[]
 for off in range(36,len(batch),364):
  row=batch[off:off+364];index=struct.unpack_from('<I',row)[0];words=struct.unpack('<45Q',row[4:]);refund=bool(words[39]or words[40]);length=words[21];cls=(2 if length<=50 else 3) if refund else (0 if length<=18 else 1)
  peo_len=length+(69 if refund else 37);rid=row[4+240:4+272];digest=b''.join(w.to_bytes(8,'big') for w in words[41:45]);leaves.append((index,hashlib.sha256(b'\x02\0\0\0'+rid+digest).digest()))
  groups[0 if unified else cls].append((index,struct.pack('<3Q',1,index,peo_len)+rid+struct.pack('<4Q',*words[41:45])))
 public=bytearray(ctx)
 for group,capacity in zip(groups,caps):
  group.sort();assert len(group)<=capacity
  public+=b''.join(row for _,row in group)+bytes(88*(capacity-len(group)))
 leaves.sort();assert [i for i,_ in leaves]==list(range(n));_,root=reconstruct([h for _,h in leaves]);assert len(public)==24+88*sum(caps)
 return bytes(public),root or bytes(32)

def compact(public,unified=False):
 caps=[1024] if unified else CAP
 assert len(public)==24+88*sum(caps)
 rows=[];slot=0
 for cls,cap in enumerate(caps):
  for _ in range(cap):
   row=public[24+88*slot:24+88*(slot+1)];slot+=1
   active,index,length=struct.unpack('<3Q',row[:24])
   if not active:assert row==bytes(88);continue
   assert active==1 and length<256
   rows.append(bytes([cls,length])+struct.pack('<I',index)+row[24:56]+b''.join(struct.unpack('<Q',row[j:j+8])[0].to_bytes(8,'big') for j in range(56,88,8)))
 return (b'NPRCBWU1' if unified else b'NPRCBW01')+public[:24]+struct.pack('<I',len(rows))+b''.join(rows)

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('batches',type=Path);p.add_argument('--report',type=Path,required=True);a=p.parse_args();rows=[]
 for f in sorted(a.batches.glob('*.batch')):
  public,root=emit(f.read_bytes());assert f.with_suffix('.context').read_bytes()==public[:24];assert f.with_suffix('.root').read_bytes()==root;f.with_suffix('.public').write_bytes(public);rows.append({'case':f.stem,'public_sha256':hashlib.sha256(public).hexdigest(),'root':root.hex()})
 a.report.write_text(json.dumps({'status':'INDEPENDENT_PUBLIC_VECTOR_AUDIT','cases':rows},indent=2)+'\n');print('Checked',len(rows),'independent public vectors/roots')
if __name__=='__main__':main()
