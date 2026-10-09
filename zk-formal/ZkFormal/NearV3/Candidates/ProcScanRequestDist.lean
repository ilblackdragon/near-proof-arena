import ZkFormal.NearV3.Candidates.ProcScanRequestKind
import ZkFormal.NearV3.Candidates.ProcScanRequestRangePhysical
namespace ZkFormal.NearV3.Candidates.ProcScanRequestDist
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcScanRequestFactor
attribute [local irreducible] ProcScanRequestFactor.row

theorem quiet_frame (Z:ZEnv)(hs:Z.cur Dist.kSh=0)(hg:Z.cur Dist.kGH=0)(hc:Z.cur Dist.kC=0)
    (ha:Z.cur Dist.al=0)(hcmp:Z.cur Dist.cg=0)(hsg:Z.cur Dist.dlsg=0)
    (hrg:Z.cur Dist.dlrg=0)(he:Z.cur Dist.eI=0) :
    ∀e∈Dist.cShard++Dist.cGrid,zev Z e=0 := by
  simp [Dist.cShard,Dist.cGrid,Dist.mul3,Dist.notE,Dist.bits2E,Dist.bits1E,Dist.b0E,
    Dist.x1E,Dist.instCols,zev,ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.n,
    ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.smul,
    hs,hg,hc,ha,hcmp,hsg,hrg,he]

theorem quiet (R:Run)(c:CReq)(rho jj cv:Nat)(tr:Trace Fp)(t r:Nat)(pub:List Fp)
    (hrow:∀col,tr.cell t r col=Fp.ofNat (row R c rho jj cv)[col]!) :
    ∀e∈Dist.cShard++Dist.cGrid,e.eval tr t r pub=0 := by
  rcases ProcScanRequestQuietCells.zeros R c rho jj cv with
    ⟨hp,hs,hg,hc,hz,ha,hend,hcb,hcg,hsg,hrg,he⟩
  have zcell (col:Nat)(h:(row R c rho jj cv)[col]! =0) : (tenv tr t r pub).cur col=0 := by
    change (tr.cell t r col).toNat=0
    rw [hrow,h];rfl
  intro e hem
  apply eval_zero_of
  exact quiet_frame (tenv tr t r pub) (zcell _ hs) (zcell _ hg) (zcell _ hc)
    (zcell _ ha) (zcell _ hcg) (zcell _ hsg) (zcell _ hrg) (zcell _ he) e hem

theorem physical (R:Run)(c:CReq)(rho jj cv:Nat)(hrho:rho<20)(hD:R.D≤4194304)
    (tr:Trace Fp)(t r:Nat)(pub:List Fp)
    (hrow:∀col,tr.cell t r col=Fp.ofNat (row R c rho jj cv)[col]!)
    (hfirst:r≠0)(hlast:r+1<tr.height t)
    (hgh:tr.cell t ((r+1)%tr.height t) Dist.kGH=0)
    (hkc:tr.cell t ((r+1)%tr.height t) Dist.kC=0)
    (hn:tr.cell t ((r+1)%tr.height t) Dist.kSh=0 ∨
      (tr.cell t ((r+1)%tr.height t) Dist.side=0 ∧
       tr.cell t ((r+1)%tr.height t) Dist.a=0 ∧tr.cell t ((r+1)%tr.height t) Dist.kp=0)) :
    ∀e∈Dist.constraints,e.eval tr t r pub=0 := by
  have hk:=ProcScanRequestKind.physical R c rho jj cv tr t r pub hrow hfirst hlast hgh hkc hn
  have hq:=quiet R c rho jj cv tr t r pub hrow
  have hr:=ProcScanRequestRangePhysical.physical R c rho jj cv hrho hD tr t r pub hrow
  simp only [Dist.constraints,List.forall_mem_append]
  exact ⟨⟨⟨hk,(List.forall_mem_append.mp hq).1⟩,
    (List.forall_mem_append.mp hq).2⟩,hr⟩

theorem own_bools (R:Run)(c:CReq)(rho jj cv:Nat)(tr:Trace Fp)(t r:Nat)(pub:List Fp)
    (hrow:∀col,tr.cell t r col=Fp.ofNat (row R c rho jj cv)[col]!) :
    ∀e∈Scan.ownBool.map ZkFormal.Chacha.Table.boolC,e.eval tr t r pub=0 := by
  intro e he
  obtain ⟨col,hcol,rfl⟩:=List.mem_map.mp he
  apply eval_zero_of
  apply Complete.zev_boolC
  change (tr.cell t r col).toNat≤1
  rw [hrow,Fp.toNat_ofNat]
  exact Nat.le_trans (Nat.mod_le _ _) (ProcScanRequestBools.own_columns R c rho jj cv col hcol)
end ZkFormal.NearV3.Candidates.ProcScanRequestDist
