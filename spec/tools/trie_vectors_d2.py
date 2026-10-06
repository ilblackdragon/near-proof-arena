#!/usr/bin/env python3
"""Independent canonical NEAR trie builder (RawTrieNodeWithSize, memory_usage) for testing
the Lean finalize (upsert / delete + squash). Writes vectors: initial map -> node list + root,
a change set, and the expected root of the updated map."""
import hashlib, random, struct, sys
def sha(b): return hashlib.sha256(b).digest()
def u32(x): return struct.pack('<I', x)
def u64(x): return struct.pack('<Q', x)
def nib(b):
    out=[]
    for x in b: out += [x>>4, x&15]
    return out
def hp(n, leaf):
    lb = 32 if leaf else 0
    if len(n)%2==1:
        out=[16+n[0]+lb]; rest=n[1:]
    else:
        out=[lb]; rest=n
    for i in range(0,len(rest),2): out.append(rest[i]*16+rest[i+1])
    return bytes(out)
def build(items, store):
    """items: list of (nibbles, value), distinct keys. returns (hash, mem)"""
    if len(items)==1 and True:
        k,v=items[0]
        if True:
            h=hp(k,True); mem=50+2*len(h)+len(v)+50
            node=bytes([0])+u32(len(h))+h+u32(len(v))+sha(v)+u64(mem)
            store[sha(node)]=node; store[sha(v)]=v
            return sha(node), mem
    # common prefix
    p=items[0][0]
    for k,_ in items[1:]:
        i=0
        while i<len(p) and i<len(k) and p[i]==k[i]: i+=1
        p=p[:i]
    if p:
        ch, cm = branch([(k[len(p):],v) for k,v in items], store)
        h=hp(p,False); mem=50+2*len(h)+cm
        node=bytes([3])+u32(len(h))+h+ch+u64(mem)
        store[sha(node)]=node
        return sha(node), mem
    return branch(items, store)
def branch(items, store):
    val=None; kids={}
    for k,v in items:
        if not k: val=v
        else: kids.setdefault(k[0],[]).append((k[1:],v))
    mem=50; bm=0; hs=b''
    for i in range(16):
        if i in kids:
            h,m=build(kids[i],store); bm|=1<<i; hs+=h; mem+=m
    if val is not None:
        mem+=len(val)+50; store[sha(val)]=val
        node=bytes([2])+u32(len(val))+sha(val)+struct.pack('<H',bm)+hs+u64(mem)
    else:
        node=bytes([1])+struct.pack('<H',bm)+hs+u64(mem)
    store[sha(node)]=node
    return sha(node), mem
def root_of(m, store):
    if not m: return bytes(32)
    items=[(nib(k),v) for k,v in sorted(m.items())]
    return build(items, store)[0]
def rkey(rng, pool):
    if pool and rng.random()<0.6:
        base=rng.choice(pool); cut=rng.randint(0,len(base))
        return base[:cut]+bytes(rng.randint(0,255) if rng.random()<0.5 else rng.randint(0,3) for _ in range(rng.randint(0,4)))
    return bytes(rng.randint(0,5) for _ in range(rng.randint(1,6)))
def main():
    rng=random.Random(int(sys.argv[1]) if len(sys.argv)>1 else 7)
    n=int(sys.argv[2]) if len(sys.argv)>2 else 300
    out=[]
    for c in range(n):
        m={}; pool=[]
        for _ in range(rng.randint(1,25)):
            k=rkey(rng,pool)
            if not k: continue
            pool.append(k); m[k]=bytes(rng.randint(0,255) for _ in range(rng.randint(0,40)))
        store={}; r0=root_of(m,store)
        chg={}
        for _ in range(rng.randint(1,12)):
            if m and rng.random()<0.55:
                k=rng.choice(list(m.keys()))
            else:
                k=rkey(rng,pool)
                if not k: continue
            chg[k]=None if rng.random()<0.6 else bytes(rng.randint(0,255) for _ in range(rng.randint(0,30)))
        m2=dict(m)
        for k,v in chg.items():
            if v is None: m2.pop(k,None)
            else: m2[k]=v
        r1=root_of(m2,{})
        out.append('CASE')
        out.append('root '+r0.hex())
        for v in store.values(): out.append('node '+v.hex())
        for k,v in sorted(chg.items()): out.append('chg '+k.hex()+' '+('-' if v is None else (v.hex() or '.')))
        out.append('exp '+r1.hex())
    print('\n'.join(out))
main()
