#!/usr/bin/env python3
"""Synthetic exact source-capacity boundaries; not accepted NEAR claims."""
import argparse,hashlib,json,struct
from pathlib import Path
from receipt_interface import arithmetic,G
from receipt_list_public import emit

def u64(n):return struct.pack('<Q',n)
def vec(b):return struct.pack('<I',len(b))+b
def digest_words(b):
 d=hashlib.sha256(b).digest();return b''.join(u64(int.from_bytes(d[i:i+8],'big')) for i in range(0,32,8))
def build(extra):
 source=u64(3)+struct.pack('<I',2);rows=[];height=123;bgp=3
 for i in range(2):
  pre=b'p'*64;recv=b'r'*32;signer=b's'*(31+(extra if i==1 else 0));rid=bytes([i+1])*32;key=bytes(range(32));amounts=(10**28,17,0,182,5,bgp);after,burn,surplus=arithmetic(*amounts,False)
  refund=hashlib.sha256(rid+u64(height)+bytes(8)).digest();peo=struct.pack('<I',1)+refund+u64(G)+burn.to_bytes(16,'little')+vec(recv)+b'\x02\0\0\0\0'
  encoded=vec(pre)+vec(recv)+rid+b'\0'+vec(signer)+b'\0'+key+amounts[4].to_bytes(16,'little')+bytes(8)+b'\x01\0\0\0\x03'+amounts[1].to_bytes(16,'little');source+=encoded
  ins=b''.join(x.to_bytes(16,'little') for x in amounts)+u64(len(pre))+pre.ljust(64,b'\0')+u64(len(recv))+recv.ljust(64,b'\0')+rid+u64(height)
  other=u64(len(signer))+signer.ljust(64,b'\0')+u64(0)+key.ljust(64,b'\0')
  rows.append(ins+other+b''.join(x.to_bytes(16,'little') for x in [after,burn,surplus])+digest_words(peo))
 assert len(source)==512+extra and all(len(row)==504 for row in rows)
 raw=b'NPLST001'+bgp.to_bytes(16,'little')+u64(height)+u64(3)+struct.pack('<I',2)+hashlib.sha256(source).digest()+b''.join(rows)
 return raw,source

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('output',type=Path);a=p.parse_args();a.output.mkdir(parents=True,exist_ok=True);report=[]
 for extra in [0,1]:
  raw,source=build(extra);name=f'synthetic-source-{512+extra}';base=a.output/name;base.with_suffix('.list').write_bytes(raw);base.with_suffix('.public4').write_bytes(emit(raw,4));report.append({'name':name,'source_bytes':len(source),'sha256':hashlib.sha256(raw).hexdigest(),'source_sha256':hashlib.sha256(source).hexdigest()})
 (a.output/'manifest.json').write_text(json.dumps({'status':'SYNTHETIC_SOURCE_LIMIT_TESTS_NOT_NEAR_CLAIMS','cases':report},indent=2)+'\n');print(json.dumps(report))
if __name__=='__main__':main()
