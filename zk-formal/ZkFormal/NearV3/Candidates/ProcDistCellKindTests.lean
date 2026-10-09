import ZkFormal.NearV3.Candidates.ProcDistCellInverseCells
namespace ZkFormal.NearV3.Candidates.ProcDistCellKindTests
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Chacha ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcDistCellRow
attribute [local irreducible] ProcDistCellRow.row
set_option maxRecDepth 32768

theorem physical (ids:List Nat)(tv n i j sv rr n1 l1 n2 l2:Nat)(allowed:Bool)
    (hi:i<n)(hj:j<n)(hn:n≤64)(tr:Trace Fp)(t r:Nat)(pub:List Fp)
    (hrow:∀col,tr.cell t r col=Fp.ofNat (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[col]!) :
    ∀e∈(Dist.cKind.drop (Dist.boolCols.map ZkFormal.Chacha.Table.boolC).length).drop 13,
      e.eval tr t r pub=0 := by
  have ho:=ProcDistCellOutputCells.fields ids tv n i j sv rr n1 l1 n2 l2 allowed
  have hp:=ProcDistCellPosition.fields ids tv n i j sv rr n1 l1 n2 l2 allowed
  have hc:tr.cell t r Dist.kC=1:=by rw [hrow,ho.2.2.1];rfl
  have hs:tr.cell t r Dist.kSh=0:=by rw [hrow,ho.1];rfl
  have ha:tr.cell t r Dist.a=Fp.ofNat i:=by rw [hrow,ho.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  have hb:tr.cell t r Dist.b=Fp.ofNat j:=by rw [hrow,ho.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  have hnn:tr.cell t r Dist.nn=Fp.ofNat n:=by rw [hrow,ho.2.2.2.2.1]
  have he1:tr.cell t r Dist.e1=(if j+1=n then 1 else 0):=by rw [hrow,hp.2];split <;> rfl
  have he2:tr.cell t r Dist.e2=(if i+1=n then 1 else 0):=by
    rw [hrow,ho.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1];split <;> rfl
  have hg1:tr.cell t r Dist.ig1=Fp.ofNat (finv (fsub j (n-1))):=
    (hrow _).trans (congrArg Fp.ofNat (ProcDistCellInverseCells.first ids tv n i j sv rr n1 l1 n2 l2 allowed))
  have hg2:tr.cell t r Dist.ig2=Fp.ofNat (finv (fsub i (n-1))):=
    (hrow _).trans (congrArg Fp.ofNat (ProcDistCellInverseCells.second ids tv n i j sv rr n1 l1 n2 l2 allowed))
  have hjInv:=ProcDistIndexTest.inverse j n hj hn
  have hiInv:=ProcDistIndexTest.inverse i n hi hn
  have hjZero:=ProcDistIndexTest.annihilate j n hj
  have hiZero:=ProcDistIndexTest.annihilate i n hi
  clear hrow ho hp
  simp only [Dist.cKind,List.append_assoc,List.drop_left,Dist.cCommon,List.cons_append,List.nil_append,
    List.drop_succ_cons,List.drop_zero,List.forall_mem_cons]
  refine ⟨?_,?_,?_,?_,by simp⟩
  · change (tr.cell t r Dist.kSh+tr.cell t r Dist.kC)*
      (tr.cell t r Dist.e1 + -(1 + -(((tr.cell t r Dist.kSh*tr.cell t r Dist.a+tr.cell t r Dist.kC*tr.cell t r Dist.b)+-(tr.cell t r Dist.nn + -(1:Fp)))*tr.cell t r Dist.ig1)))=0
    rw [hs,hc,he1,ha,hb,hnn,hg1];grind only
  · change (tr.cell t r Dist.kSh+tr.cell t r Dist.kC)*
      (((tr.cell t r Dist.kSh*tr.cell t r Dist.a+tr.cell t r Dist.kC*tr.cell t r Dist.b)+-(tr.cell t r Dist.nn + -(1:Fp)))*tr.cell t r Dist.e1)=0
    rw [hs,hc,he1,ha,hb,hnn];grind only
  · change tr.cell t r Dist.kC*
      (tr.cell t r Dist.e2 + -(1 + -((tr.cell t r Dist.a + -(tr.cell t r Dist.nn + -(1:Fp)))*tr.cell t r Dist.ig2)))=0
    rw [hc,he2,ha,hnn,hg2];grind only
  · change tr.cell t r Dist.kC*((tr.cell t r Dist.a + -(tr.cell t r Dist.nn + -(1:Fp)))*tr.cell t r Dist.e2)=0
    rw [hc,he2,ha,hnn];grind only
end ZkFormal.NearV3.Candidates.ProcDistCellKindTests
