# Mechanical port of a v1 Extract/Rcpt*.lean module to NearV3/Rcpt/Extract/V/ (run from zk-formal/): python3 test/port_rcpt_v3.py RcptKey
import re,sys
names={'RcptFacts':'Facts','RcptSegs':'Segs','RcptLayout':'Layout','RcptTable':'Table','RcptRegs':'Regs','RcptRowT':'RowT','RcptOf':'Of',
 'RcptChunks':'Chunks','RcptFB1':'FB1','RcptFB2':'FB2','RcptBytes':'Bytes','RcptGates':'Gates','RcptBus':'Bus','RcptChars':'Chars',
 'RcptKey':'Key','RcptDig':'Dig','RcptClaim':'Claim','RcptShape':'Shape','RcptTraffic':'Traffic','RcptWfEasy':'WfEasy','RcptCount':'Count',
 'RcptGas1':'Gas1','RcptGas2':'Gas2','RcptGas3':'Gas3','RcptDep':'Dep','RcptArith':'Arith','RcptToks':'Toks','RcptClaimArith':'ClaimArith',
 'RcptStrField':'StrField','RcptStrings':'Strings','RcptCharClass':'CharClass','RcptNames':'Names','RcptWfIds':'WfIds','RcptProof':'Proof'}
OPEN3 = ("open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.RcptV3\n"
         
         "open ZkFormal.Near.RcptProof (sumL chain chainC convS convR sumL_congr sumL_lt le256_map_range sumL_add convS_id)")
f=sys.argv[1]
s=open(f'ZkFormal/Near/Extract/{f}.lean').read()
s=s.replace('ZkFormal.Near.RcptProof','ZkFormal.NearV3.RcptV3Proof')
s=s.replace('open ZkFormal.NearV3.RcptV3Proof (sumL','open ZkFormal.Near.RcptProof (sumL')
for k,v in names.items():
    s=s.replace(f'import ZkFormal.Near.Extract.{k}\n',f'import ZkFormal.NearV3.Rcpt.Extract.V.{v}\n')
    s=s.replace(f'# ZkFormal.Near.Extract.{k} ',f'# ZkFormal.NearV3.Rcpt.Extract.V.{v} (v1 `{k}`) ')
s=s.replace('open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt', OPEN3)
s=s.replace('variable {tr : Trace Fp} {pub : List Fp}','variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}')
for nm in ['table','constraints','interactions','hr','succ','Lp','Lv','Ls','kt']:
    s=s.replace(f'Rcpt.{nm}',f'RcptV3.{nm}')
s=re.sub(r'\bRcpt\.r\b','RcptV3.r',s)
s=s.replace('T_RCPT','tt')
for fn in ['RFld','Layout','RowV','slotT','colAt','rcptOf','regsAt','fieldRows','Shape','viewOf','PN','SN','bvN','hiV','loV','tin','tout']:
    s=re.sub(r'(?<![A-Za-z])'+fn+r' tr ',fn+' tr tt ',s)
    s=s.replace('def '+fn+' (tr : Trace Fp) (','def '+fn+' (tr : Trace Fp) (tt : Nat) (')
s=s.replace('structure Shape (tr : Trace Fp)','structure Shape (tr : Trace Fp) (tt : Nat)')
s=s.replace('PV_HEIGHT','PH_HEIGHT').replace('PV_BGP','PH_GP')
s=s.replace('colAt_get _ _ _ _ _ hi','colAt_get _ _ _ _ _ _ hi')
s=re.sub(r'(?<![A-Za-z])Fld tr ','Fld tr tt ',s)
s=re.sub(r'\bC tr q','C tr tt q',s)
s=s.replace('RcptView','RcptView')
open(f'ZkFormal/NearV3/Rcpt/Extract/V/{names[f]}.lean','w').write(s)
print('ported',f)
