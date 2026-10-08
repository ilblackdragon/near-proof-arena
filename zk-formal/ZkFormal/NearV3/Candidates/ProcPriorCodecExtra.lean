import ZkFormal.NearV3.Sched.Gen.Codec
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecExtra
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec

def baseExtra (n kk f gg alv gbv : Nat) : List (Nat×Nat) :=
  [(rs,if f=0 ∧ gg=0 then 1 else 0),(al,alv),(gb,gbv),
   (srcC,kk/n),(hasC,if kk%n+1=n then 1 else 0),(useC,kk%n)]
def startExtra (n kk : Nat) : List (Nat×Nat) :=
  [(nzb,if kk%n=0 then 1 else 0),(ig2,finv (kk%n)),(ib,finv (fsub (kk%n) (n-1)))]
def priorExtra (apRv bigRv : Nat) : List (Nat×Nat) := [(apR,apRv),(bigR,bigRv)]
def allowanceExtra (gg lowfv wtv apv bigv apostv nzbv bpr : Nat) : List (Nat×Nat) :=
  [(lowf,lowfv),(wt,wtv%ZkFormal.Algebra.P),(ap,apv),(big,bigv),(apost,apostv),
   (nzb,nzbv),(ib,finv bpr),(ig2,finv (fsub gg 2)),(e2,if gg=2 then 1 else 0)]
def wrapExtra (n kk : Nat) : List (Nat×Nat) := [(a0g,if kk%n+1=n then 1 else 0)]
def compareExtra (x cbv : Nat) : List (Nat×Nat) := [(cx,x),(cy,Codec.MA),(cbit,cbv),(cg,1)]
def carryExtra (cbv : Nat) : List (Nat×Nat) := [(cb,cbv)]
def endExtra (bFv a1v a2v alv baseV afinV gf receiver : Nat) : List (Nat×Nat) :=
  [(rend,1),(bF,bFv),(a1,a1v),(a2,a2v),(g2,alv*baseV),(afin,afinV),(gfin,gf),(u0g,receiver)]
def forwardExtra (gf gbv ft kk : Nat) : List (Nat×Nat) :=
  [(fwg,1),(cx,gf+gbv),(cy,ft),(cbit,1),(cg,1),(pm0,kk%256),(pm1,kk/256),
   (fb 0,ft%256),(fb 1,ft/256%256),(fb 2,ft/65536%256)]

end ZkFormal.NearV3.Candidates.ProcPriorCodecExtra
