import ZkFormal.NearV3.Candidates.ProcDistCellControls
namespace ZkFormal.NearV3.Candidates.ProcDistCellKind
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcDistCellRow
attribute [local irreducible] ProcDistCellRow.row
set_option maxRecDepth 32768

theorem frame (Z:ZEnv)(ha:Z.cur Dist.act=1)(hp:Z.cur Dist.kP=0)(hs:Z.cur Dist.kS=0)
    (hsh:Z.cur Dist.kSh=0)(hg:Z.cur Dist.kGH=0)(hc:Z.cur Dist.kC=1)
    (hf:Z.first=0)(hl:Z.last=0) :
    ∀e∈(Dist.cKind.drop (Dist.boolCols.map ZkFormal.Chacha.Table.boolC).length).take 13,
      zev Z e=0 := by
  simp only [Dist.cKind,List.append_assoc,List.drop_left,Dist.cCommon,List.cons_append,List.nil_append,
    List.take_succ_cons,List.take_zero,List.forall_mem_cons,List.forall_mem_nil]
  simp [Dist.mul3,Dist.notE,zev,ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.n,
    ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.boolC,
    ha,hp,hs,hsh,hg,hc,hf,hl]

theorem physical (ids:List Nat)(tv n i j sv rr n1 l1 n2 l2:Nat)(allowed:Bool)
    (hi:i<n)(hj:j<n)(hn:n≤64)(tr:Trace Fp)(t r:Nat)(pub:List Fp)
    (hrow:∀col,tr.cell t r col=Fp.ofNat (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[col]!)
    (hf:r≠0)(hl:r+1<tr.height t) :
    ∀e∈Dist.cKind,e.eval tr t r pub=0 := by
  have ho:=ProcDistCellOutputCells.fields ids tv n i j sv rr n1 l1 n2 l2 allowed
  have hc:=ProcDistCellControls.fields ids tv n i j sv rr n1 l1 n2 l2 allowed
  have zcell (col v:Nat)(hv:v≤1)(h:(row ids tv n i j sv rr n1 l1 n2 l2 allowed)[col]! =v) :
      (tenv tr t r pub).cur col=v := by
    change (tr.cell t r col).toNat=v
    rw [hrow,h,Fp.toNat_ofNat,Nat.mod_eq_of_lt (by unfold P;omega)]
  have hz:=frame (tenv tr t r pub) (zcell _ 1 (by decide) hc.1)
    (zcell _ 0 (by decide) hc.2.1) (zcell _ 0 (by decide) hc.2.2.1)
    (zcell _ 0 (by decide) ho.1) (zcell _ 0 (by decide) ho.2.1)
    (zcell _ 1 (by decide) ho.2.2.1)
    (by simp [tenv,hf]) (by simp [tenv,show r+1≠tr.height t by omega])
  have ht:=ProcDistCellKindTests.physical ids tv n i j sv rr n1 l1 n2 l2 allowed hi hj hn tr t r pub hrow
  have hsplit:Dist.cKind=Dist.boolCols.map ZkFormal.Chacha.Table.boolC++
      ((Dist.cKind.drop (Dist.boolCols.map ZkFormal.Chacha.Table.boolC).length).take 13++
       (Dist.cKind.drop (Dist.boolCols.map ZkFormal.Chacha.Table.boolC).length).drop 13) := by
    rw [List.take_append_drop]
    simp only [Dist.cKind,List.append_assoc,List.drop_left]
  rw [hsplit]
  simp only [List.forall_mem_append]
  refine ⟨?_,?_,ht⟩
  · intro e he
    obtain ⟨col,hcol,rfl⟩:=List.mem_map.mp he
    apply eval_zero_of
    apply Complete.zev_boolC
    change (tr.cell t r col).toNat≤1
    rw [hrow,Fp.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le _ _) (ProcDistCellBools.columns ids tv n i j sv rr n1 l1 n2 l2 allowed col hcol)
  · intro e he
    exact eval_zero_of (hz e he)
end ZkFormal.NearV3.Candidates.ProcDistCellKind
