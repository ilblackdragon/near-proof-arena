import ZkFormal.NearV3.Candidates.ProcScanRequestNativeFacts
namespace ZkFormal.NearV3.Candidates.ProcScanRequestNativeLocal
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcScanRequestFactor
attribute [local irreducible] ProcScanRequestFactor.row Scan.reqRows

theorem physical (I:Input)(tau:Nat)(R:Run)(hRun:ActualRun.run I tau=.ok R)
    (hParam:NearSpecV3.Scheduler.Params.calculate NearSpecV3.Scheduler.Config.pv86 I.ids.length=some I.p)
    (c:CReq)(hc:c∈R.conv)(rho:Nat)(hr:rho<20)
    (tr:Trace Fp)(t r:Nat)(pub:List Fp)
    (hrow:∀col,tr.cell t r col=Fp.ofNat (Scan.reqRows R c)[rho]![col]!)
    (hnext:rho<19→∀col,tr.cell t ((r+1)%tr.height t) col=Fp.ofNat (Scan.reqRows R c)[rho+1]![col]!)
    (hboundary:rho=19→ProcScanRequestBodyBoundary.Next tr t r)
    (hfirst:r≠0)(hlast:r+1<tr.height t)
    (hgh:tr.cell t ((r+1)%tr.height t) Dist.kGH=0)
    (hkc:tr.cell t ((r+1)%tr.height t) Dist.kC=0)
    (hn:tr.cell t ((r+1)%tr.height t) Dist.kSh=0 ∨
      (tr.cell t ((r+1)%tr.height t) Dist.side=0 ∧
       tr.cell t ((r+1)%tr.height t) Dist.a=0 ∧tr.cell t ((r+1)%tr.height t) Dist.kp=0)) :
    ∀e∈ScanDist.constraints,e.eval tr t r pub=0 := by
  obtain ⟨hD,hfacts⟩:=ProcScanRequestNativeFacts.native I tau R hRun hParam
  obtain ⟨hbits,hlink,hkey⟩:=hfacts c hc
  exact ProcScanRequestLocal.physical R c rho hr hD hbits hlink hkey tr t r pub
    hrow hnext hboundary hfirst hlast hgh hkc hn

end ZkFormal.NearV3.Candidates.ProcScanRequestNativeLocal
