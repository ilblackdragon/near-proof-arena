import ZkFormal.NearV3.Candidates.ProcScanRequestBools
namespace ZkFormal.NearV3.Candidates.ProcScanRequestKind
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcScanRequestFactor
attribute [local irreducible] ProcScanRequestFactor.row

theorem frame (Z:ZEnv)
    (hbits:∀col∈Dist.boolCols,Z.cur col≤1)
    (ha:Z.cur Dist.act=1)(hs:Z.cur Dist.kS=1)
    (hp:Z.cur Dist.kP=0)(hsh:Z.cur Dist.kSh=0)(hgh:Z.cur Dist.kGH=0)(hc:Z.cur Dist.kC=0)
    (hf:Z.first=0)(hl:Z.last=0)
    (hngh:Z.nxt Dist.kGH=0)(hnc:Z.nxt Dist.kC=0)
    (hnsh:Z.nxt Dist.kSh=0 ∨ (Z.nxt Dist.side=0 ∧Z.nxt Dist.a=0 ∧Z.nxt Dist.kp=0)) :
    ∀e∈Dist.cKind,zev Z e=0 := by
  simp only [Dist.cKind,List.forall_mem_append]
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro e he
    obtain ⟨col,hcol,rfl⟩:=List.mem_map.mp he
    exact Complete.zev_boolC (hbits col hcol)
  · simp [Dist.cCommon,Dist.notE,Dist.mul3,zev,ZkFormal.Chacha.Table.E.c,
      ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.sub,
      ha,hs,hp,hsh,hgh,hc,hf,hl]
  · rcases hnsh with hnsh|⟨hnside,hna,hnkp⟩
    all_goals simp [Dist.notE,Dist.mul3,Dist.x1E,zev,ZkFormal.Chacha.Table.E.c,
      ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.sub,
      ZkFormal.Chacha.Table.boolC,ha,hs,hp,hsh,hgh,hc,hf,hl,hngh,hnc, *]

theorem physical (R:Run)(c:CReq)(rho jj cv:Nat)(tr:Trace Fp)(t r:Nat)(pub:List Fp)
    (hrow:∀col,tr.cell t r col=Fp.ofNat (row R c rho jj cv)[col]!)
    (hfirst:r≠0)(hlast:r+1<tr.height t)
    (hgh:tr.cell t ((r+1)%tr.height t) Dist.kGH=0)
    (hkc:tr.cell t ((r+1)%tr.height t) Dist.kC=0)
    (hn:tr.cell t ((r+1)%tr.height t) Dist.kSh=0 ∨
      (tr.cell t ((r+1)%tr.height t) Dist.side=0 ∧
       tr.cell t ((r+1)%tr.height t) Dist.a=0 ∧tr.cell t ((r+1)%tr.height t) Dist.kp=0)) :
    ∀e∈Dist.cKind,e.eval tr t r pub=0 := by
  have hz:=ProcScanRequestQuietCells.zeros R c rho jj cv
  have hc:=ProcScanRequestCells.controls R c rho jj cv
  simp only [Scan.act,Scan.kS] at hc
  have zcell (col:Nat)(h:(row R c rho jj cv)[col]! =0) : (tenv tr t r pub).cur col=0 := by
    change (tr.cell t r col).toNat=0
    rw [hrow,h];rfl
  have ocell (col:Nat)(h:(row R c rho jj cv)[col]! =1) : (tenv tr t r pub).cur col=1 := by
    change (tr.cell t r col).toNat=1
    rw [hrow,h];rfl
  intro e he
  apply eval_zero_of
  apply frame (tenv tr t r pub) _ (ocell _ hc.1) (ocell _ hc.2.1)
    (zcell _ hz.1) (zcell _ hz.2.1) (zcell _ hz.2.2.1) (zcell _ hz.2.2.2.1) _ _ _ _ _ e he
  · intro col hcol
    change (tr.cell t r col).toNat≤1
    rw [hrow,Fp.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le _ _) (ProcScanRequestBools.all_columns R c rho jj cv col hcol)
  · simp [tenv,hfirst]
  · simp [tenv,show r+1≠tr.height t by omega]
  · change (tr.cell t ((r+1)%tr.height t) Dist.kGH).toNat=0
    rw [hgh];rfl
  · change (tr.cell t ((r+1)%tr.height t) Dist.kC).toNat=0
    rw [hkc];rfl
  · rcases hn with hn|⟨ha,hb,hc⟩
    · left;change (tr.cell t ((r+1)%tr.height t) Dist.kSh).toNat=0;rw [hn];rfl
    · right
      change _∧_∧_
      simp [tenv,ha,hb,hc]
      decide
end ZkFormal.NearV3.Candidates.ProcScanRequestKind
