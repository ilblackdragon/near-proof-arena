import ZkFormal.NearV3.Candidates.ProcScanRequestBody
namespace ZkFormal.NearV3.Candidates.ProcScanRequestLocal
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcScanRequestFactor
attribute [local irreducible] ProcScanRequestFactor.row Scan.reqRows

theorem physical (R:Run)(c:CReq)(rho:Nat)(hr:rho<20)(hD:R.D≤4194304)
    (hbits:c.bits=setBits c.bm)(hlink:c.link=c.s*R.n+c.r)(hk:c.key<P)
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
  have hb:=ProcScanRequestBody.physical R c rho hr hbits hlink hk tr t r pub hrow hnext hboundary
  have hcur:∀col,tr.cell t r col=Fp.ofNat
      (row R c rho (ProcScanRequestCount.before c.bm rho) (ProcScanRequestState.state R c rho).2.2)[col]! := by
    intro col;rw [hrow,ProcScanRequestState.native_at R c rho hr]
  have hd:=ProcScanRequestDist.physical R c rho _ _ hr hD tr t r pub hcur hfirst hlast hgh hkc hn
  have ho:=ProcScanRequestDist.own_bools R c rho _ _ tr t r pub hcur
  simp only [ScanDist.constraints,Scan.own,List.forall_mem_append]
  exact ⟨hd,ho,hb⟩
end ZkFormal.NearV3.Candidates.ProcScanRequestLocal
