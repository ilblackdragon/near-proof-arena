#!/usr/bin/env python3
"""Independent D0a transfer byte/arithmetic oracle, NOT a cryptographic proof."""
import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path

G=int.from_bytes(bytes([196,164,183,246,51,0,0,0]),'little')
MAX=(1<<128)-1
STORAGE_PRICE=10_000_000_000_000_000_000
TAIL=bytes([0]*8+[1,0,0,0,3])


def le(n,k):return n.to_bytes(k,'little')
def digest(b):return hashlib.sha256(b).digest()
def raw(r,k,n=None):
    b=bytes(r[k]);assert n is None or len(b)==n,(k,len(b),n);return b
def integer(r,k):return int.from_bytes(raw(r,k,16),'little')
def vec(b):return le(len(b),4)+b


def arithmetic(before,deposit,locked,storage,gp,bgp,system):
    assert all(0<=n<=MAX for n in [before,deposit,locked,storage,gp,bgp])
    after=before+deposit;assert after<MAX
    total=after+locked;assert total<=MAX
    assert total>=STORAGE_PRICE*storage or storage<=770
    effective=min(gp,bgp)
    burnt=0 if system else G*effective
    surplus=0 if system else G*(gp-effective)
    assert burnt<=MAX and surplus<=MAX
    return after,burnt,surplus


def receipt(r,height,bgp):
    predecessor=raw(r,'p');receiver=raw(r,'v');signer=raw(r,'s')
    assert 1<=len(receiver)<=64 and len(predecessor)<=64 and len(signer)<=64
    rid=raw(r,'rid',32);pk=raw(r,'pk');assert (r['kt'],len(pk)) in [(0,32),(1,64)]
    system=predecessor==b'system';assert r['sys']==system
    after,burnt,surplus=arithmetic(integer(r,'bef'),integer(r,'dep'),integer(r,'lk'),integer(r,'st'),integer(r,'gp'),bgp,system)
    assert integer(r,'aft')==after and integer(r,'burnt')==burnt and integer(r,'ramt')==surplus
    assert r['ge']==(bgp<=integer(r,'gp')) and r['hr']==(surplus!=0)
    assert r['ee']==(system and signer==receiver)
    rid_pre=rid+le(height,8)+bytes(8)
    refund_id=digest(rid_pre) if surplus else bytes(32)
    assert raw(r,'rfid',32)==refund_id
    encoded=vec(predecessor)+vec(receiver)+rid+b'\0'+vec(signer)+bytes([r['kt']])+pk+raw(r,'gp',16)+TAIL+raw(r,'dep',16)
    peo=le(bool(surplus),4)+(refund_id if surplus else b'')+le(G,8)+le(burnt,16)+vec(receiver)+bytes([2,0,0,0,0])
    peoh=digest(peo);assert raw(r,'peoh',32)==peoh
    leaf=le(2,4)+rid+peoh
    return encoded,peo,leaf,rid_pre if surplus else None


def check_case(view,messages):
    byid={m['id']:m for m in messages};assert len(byid)==len(messages)
    expected={};previous={};counter=Counter();index=0
    for j,l in enumerate(view['lists']):
        assert l['n0']+256*l['n1']==len(l['rs'])
        blob=le(view['own'],8)+bytes([l['n0'],l['n1'],0,0])
        for r in l['rs']:
            encoded,peo,leaf,ridpre=receipt(r,view['height'],view['bgp']);blob+=encoded
            receiver=raw(r,'v');prior=previous.get(receiver)
            assert r['tprev']==(prior[0]+1 if prior else 0)
            if prior:assert integer(r,'bef')==prior[1]
            previous[receiver]=(index,integer(r,'aft'))
            expected[3+16*index]=peo;expected[4+16*index]=leaf
            if ridpre is not None:expected[5+16*index]=ridpre
            counter['receipts']+=1;counter['system' if r['sys'] else 'regular']+=1
            counter['refund']+=r['hr'];counter['nonzero_burnt']+=bool(integer(r,'burnt'))
            index+=1
        expected[1+16*j]=blob
    relevant={i:bytes(m['bytes']) for i,m in byid.items() if i%16 in [1,3,4,5]}
    assert expected==relevant,'missing/extra/mismatched receipt hash jobs'
    counter['producer_jobs']=len(expected);counter['producer_bytes']=sum(map(len,expected.values()))
    return dict(counter)


def arithmetic_boundaries():
    # Positive burns below/equal/above block gas price; system bypass.
    good=[(0,1,0,0,2,3,False),(0,1,0,0,3,3,False),(0,1,0,0,5,3,False),(0,1,0,0,MAX,MAX,True),
          (MAX-2,1,0,0,0,0,False),(0,0,0,770,0,0,False),
          (771*STORAGE_PRICE,0,0,771,0,0,False)]
    want=[(1,2*G,0),(1,3*G,0),(1,3*G,2*G),(1,0,0),(MAX-1,0,0),(0,0,0),(771*STORAGE_PRICE,0,0)]
    for args,result in zip(good,want):assert arithmetic(*args)==result
    bad=[(MAX-1,1,0,0,0,0,False),(MAX,1,0,0,0,0,False),(MAX-2,1,2,0,0,0,False),
         (0,0,0,771,0,0,False),(0,1,0,0,MAX,MAX,False),(0,1,0,0,MAX,0,False)]
    for args in bad:
        try:arithmetic(*args)
        except AssertionError:continue
        raise AssertionError(('accepted invalid arithmetic',args))
    return {'valid':len(good),'invalid':len(bad),'positive_burn_cases':3,'scope':'arithmetic only; synthetic cases are not accepted NEAR claims'}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('exports',type=Path);p.add_argument('--output',type=Path,required=True);a=p.parse_args();rows=[];mutations=0
    for f in sorted(a.exports.glob('*/rcpt.json')):
        v=json.loads(f.read_text());mp=f.with_name('sha_r.json');m=json.loads(mp.read_text());counts=check_case(v,m)
        row={'case':f.parent.name,'receipt_view_sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'messages_sha256':hashlib.sha256(mp.read_bytes()).hexdigest(),'block_gas_price':v['bgp'],**counts};rows.append(row)
        if counts.get('receipts',0):
            for field in ['rid','gp','dep','aft','burnt','rfid','peoh','bef']:
                changed=json.loads(f.read_text());r=next(r for l in changed['lists'] for r in l['rs']);r[field][0]^=1
                try:check_case(changed,m)
                except AssertionError:mutations+=1;continue
                raise AssertionError(('mutation survived',f,field))
    assert len(rows)==64
    report={'status':'INDEPENDENT_HOST_CONFORMANCE_NOT_PROOF','cases':rows,'arithmetic_boundaries':arithmetic_boundaries(),'rejected_view_mutations':mutations,'limitations':['Native receipt views are not authenticated execution inputs.','No proof binds producer bytes to private hash input wires yet.','All real corpus block gas prices are zero; positive burns only synthetic.','Routing, trie/access-key membership, complete execution and recursion omitted.']}
    a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'cases':len(rows),'receipts':sum(r.get('receipts',0) for r in rows),'mutations':mutations,'arithmetic':report['arithmetic_boundaries']}))

if __name__=='__main__':main()
