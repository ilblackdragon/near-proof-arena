#!/usr/bin/env python3
"""Add synthetic context/capacity stress fixtures; these are not NEAR-valid claims."""
import argparse,struct,shutil,json,hashlib
from receipt_interface import arithmetic,G
from pathlib import Path
from receipt_batch_public import emit
p=argparse.ArgumentParser(description=__doc__);p.add_argument('vectors',type=Path);p.add_argument('typed_batches',type=Path);p.add_argument('uniform_batches',type=Path);a=p.parse_args();raw=a.vectors.read_bytes();assert raw[:8]==b'NPROU001';rows=[raw[i:i+361] for i in range(12,len(raw),361)]
selected=[]
for cls in range(4):
 for i,r in enumerate(rows):
  w=struct.unpack('<45Q',r[:360]);refund=bool(w[39]or w[40]);got=(2 if w[21]<=50 else 3) if refund else (0 if w[21]<=18 else 1)
  if r[-1] and got==cls and w[10]==3 and w[11]==0 and w[34]==(1<<64)-1:selected.append(i);break
assert len(selected)==4
max_ctx=next(i for i,r in enumerate(rows) if r[-1] and r[80:96]==bytes([255])*16)
def write(directory,name,indices,unified):
 ctx=rows[indices[0]][80:96]+rows[indices[0]][272:280]
 assert all(rows[i][80:96]+rows[i][272:280]==ctx for i in indices)
 blob=b'NPRCB001'+ctx+struct.pack('<I',len(indices))+b''.join(struct.pack('<I',j)+rows[i][:360] for j,i in enumerate(indices));public,root=emit(blob,unified);base=directory/name
 for ext,data in [('batch',blob),('context',ctx),('root',root),('public',public)]:base.with_suffix('.'+ext).write_bytes(data)
write(a.typed_batches,'synthetic-positive',selected,False);write(a.typed_batches,'synthetic-max-context',[max_ctx],False)
a.uniform_batches.mkdir(parents=True,exist_ok=True)
for f in a.typed_batches.glob('*'):
 if f.suffix in ['.batch','.context','.root']:shutil.copy2(f,a.uniform_batches/f.name)
long_refund=next(i for i,r in enumerate(rows) if r[-1] and struct.unpack_from('<Q',r,168)[0]==64 and any(r[296:312]) and any(r[312:328]))
write(a.uniform_batches,'synthetic-1024-long-refunds',[long_refund]*1024,True)
# Distinct IDs, receivers and arithmetic values remove repeated-input bias.
records=[];template=struct.unpack('<45Q',rows[long_refund][:360])
for i in range(1024):
 w=list(template);before=10**28+i;deposit=17+i;storage=182+i%32;gp=5+i
 for off,value in [(0,before),(2,deposit),(6,storage),(8,gp)]:w[off:off+2]=[value&((1<<64)-1),value>>64]
 rid=hashlib.sha256(b'receipt-capacity-stress'+struct.pack('<I',i)).digest()
 receiver=hashlib.sha256(b'receiver'+struct.pack('<I',i)).hexdigest().encode()
 w[22:30]=struct.unpack('<8Q',receiver);w[30:34]=struct.unpack('<4Q',rid)
 after,burnt,surplus=arithmetic(before,deposit,0,storage,gp,3,False)
 for off,value in [(35,after),(37,burnt),(39,surplus)]:w[off:off+2]=[value&((1<<64)-1),value>>64]
 refund=hashlib.sha256(rid+struct.pack('<Q',w[34])+bytes(8)).digest()
 digest=hashlib.sha256(struct.pack('<I',1)+refund+struct.pack('<Q',G)+burnt.to_bytes(16,'little')+struct.pack('<I',64)+receiver+b'\x02\0\0\0\0').digest()
 w[41:45]=[int.from_bytes(digest[j:j+8],'big') for j in range(0,32,8)]
 records.append(struct.pack('<I',i)+struct.pack('<45Q',*w))
ctx=struct.pack('<3Q',template[10],template[11],template[34]);blob=b'NPRCB001'+ctx+struct.pack('<I',1024)+b''.join(records)
public,root=emit(blob,True);base=a.uniform_batches/'synthetic-1024-varied-refunds'
for ext,data in [('batch',blob),('context',ctx),('root',root),('public',public)]:base.with_suffix('.'+ext).write_bytes(data)
for f in a.uniform_batches.glob('*.batch'):
 public,root=emit(f.read_bytes(),True);assert root==f.with_suffix('.root').read_bytes();f.with_suffix('.public').write_bytes(public)
print(json.dumps({'positive':selected,'max_context':max_ctx,'repeated_long_refund':long_refund,'scope':'synthetic kernel inputs, not valid NEAR source lists'}))
