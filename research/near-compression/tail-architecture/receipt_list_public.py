#!/usr/bin/env python3
"""Independent dense public statement for the diagnostic ordered-list circuit."""
import argparse,struct
from pathlib import Path

def emit(raw,cap):
 assert raw[:8]==b'NPLST001'
 count=struct.unpack_from('<I',raw,40)[0]
 assert count<=cap and len(raw)==76+504*count
 public=raw[8:40]+struct.pack('<Q',count)
 public+=b''.join(struct.pack('<Q',int.from_bytes(raw[i:i+8],'big')) for i in range(44,76,8))
 for i in range(cap):
  out=[0]*11
  if i<count:
   w=struct.unpack_from('<63Q',raw,76+504*i)
   out=[1,i,w[21]+(69 if w[57] or w[58] else 37),*w[30:34],*w[59:63]]
  public+=struct.pack('<11Q',*out)
 assert len(public)==8*(9+11*cap)
 return public
if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('fixture',type=Path);p.add_argument('capacity',type=int);p.add_argument('output',type=Path);a=p.parse_args();a.output.write_bytes(emit(a.fixture.read_bytes(),a.capacity))
