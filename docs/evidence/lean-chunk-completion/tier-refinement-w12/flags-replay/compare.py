import json,sys,collections
def load(p):
    d={}
    for l in open(p):
        r=json.loads(l)
        d[r.get('case') or r.get('case_dir')]=r
    return d
a=load(sys.argv[1]); b=load(sys.argv[2])
assert set(a)==set(b), (len(a),len(b))
diff=0; cnt=collections.Counter()
keys=None
for k in a:
    ra,rb=a[k],b[k]
    va=(ra.get('verdict'),ra.get('reason')); vb=(rb.get('verdict'),rb.get('reason'))
    cnt[va[0]]+=1
    if va!=vb: diff+=1; print('DIFF',k,va,vb)
print(json.dumps({'cases':len(a),'identical':len(a)-diff,'changed':diff,'verdicts':cnt}))
