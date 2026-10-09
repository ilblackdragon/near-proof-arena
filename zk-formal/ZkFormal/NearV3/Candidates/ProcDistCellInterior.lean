import ZkFormal.NearV3.Candidates.ProcDistCellPosition
namespace ZkFormal.NearV3.Candidates.ProcDistCellInterior
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcDistCellRow
attribute [local irreducible] ProcDistCellRow.row
set_option maxRecDepth 32768

private theorem cast_sub (a b:Nat)(h:b≤a) : Fp.ofNat (a-b)=Fp.ofNat a-Fp.ofNat b := by
  have he:a=(a-b)+b:=by omega
  have hf:=congrArg Fp.ofNat he
  simp only [←ofNat_add'] at hf
  grind only

theorem physical (ids:List Nat)(tv n i j sv rr n1 l1 n2 l2 rr' n2' l2':Nat)(allowed allowed':Bool)
    (hj:j+1<n)(hp:allowed=true→0<n1)
    (tr:Trace Fp)(t r:Nat)(pub:List Fp)
    (hrow:∀col,tr.cell t r col=Fp.ofNat (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[col]!)
    (hnext:∀col,tr.cell t ((r+1)%tr.height t) col=Fp.ofNat
      (row ids tv n i (j+1) sv rr' (n1-b2n allowed) (l1-grant allowed n1 l1 n2 l2) n2' l2' allowed')[col]!) :
    ∀e∈(Dist.cGrid.drop 26).take 8,e.eval tr t r pub=0 := by
  let rnext:=(r+1)%tr.height t
  have hc:=ProcDistCellOutputCells.fields ids tv n i j sv rr n1 l1 n2 l2 allowed
  have hn:=ProcDistCellOutputCells.fields ids tv n i (j+1) sv rr' (n1-b2n allowed) (l1-grant allowed n1 l1 n2 l2) n2' l2' allowed'
  have hd:=ProcDistCellDivisionCells.fields ids tv n i j sv rr n1 l1 n2 l2 allowed
  have hdn:=ProcDistCellDivisionCells.fields ids tv n i (j+1) sv rr' (n1-b2n allowed) (l1-grant allowed n1 l1 n2 l2) n2' l2' allowed'
  have hpos:=ProcDistCellPosition.fields ids tv n i j sv rr n1 l1 n2 l2 allowed
  have hposn:=ProcDistCellPosition.fields ids tv n i (j+1) sv rr' (n1-b2n allowed) (l1-grant allowed n1 l1 n2 l2) n2' l2' allowed'
  have skC:tr.cell t r Dist.kC=Fp.ofNat (1):=by rw [hrow,hc.2.2.1]
  have sa:tr.cell t r Dist.a=Fp.ofNat (i):=by rw [hrow,hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  have sb:tr.cell t r Dist.b=Fp.ofNat (j):=by rw [hrow,hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  have ss:tr.cell t r Dist.s=Fp.ofNat (sv):=by rw [hrow,hc.2.2.2.1]
  have snn:tr.cell t r Dist.nn=Fp.ofNat (n):=by rw [hrow,hc.2.2.2.2.1]
  have sal:tr.cell t r Dist.al=Fp.ofNat (b2n allowed):=by rw [hrow,hc.2.2.2.2.2.2.2.2.2.1]
  have sgb:tr.cell t r Dist.gb=Fp.ofNat (grant allowed n1 l1 n2 l2):=by rw [hrow,hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  have nkC:tr.cell t rnext Dist.kC=Fp.ofNat (1):=by rw [hnext,hn.2.2.1]
  have na:tr.cell t rnext Dist.a=Fp.ofNat (i):=by rw [hnext,hn.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  have nb:tr.cell t rnext Dist.b=Fp.ofNat (j+1):=by rw [hnext,hn.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  have ns:tr.cell t rnext Dist.s=Fp.ofNat (sv):=by rw [hnext,hn.2.2.2.1]
  have nnn:tr.cell t rnext Dist.nn=Fp.ofNat (n):=by rw [hnext,hn.2.2.2.2.1]
  have sN:tr.cell t r Dist.N1=Fp.ofNat n1:=by rw [hrow,hd.2.1]
  have sL:tr.cell t r Dist.L1=Fp.ofNat l1:=by rw [hrow,hd.2.2.1]
  have nN:tr.cell t rnext Dist.N1=Fp.ofNat (n1-b2n allowed):=by rw [hnext,hdn.2.1]
  have nL:tr.cell t rnext Dist.L1=Fp.ofNat (l1-grant allowed n1 l1 n2 l2):=by rw [hnext,hdn.2.2.1]
  have st:tr.cell t r Dist.tau=Fp.ofNat tv:=by rw [hrow,hpos.1]
  have nt:tr.cell t rnext Dist.tau=Fp.ofNat tv:=by rw [hnext,hposn.1]
  have se:tr.cell t r Dist.e1=0:=by rw [hrow,hpos.2,if_neg (by omega)];rfl
  have huse:b2n allowed≤n1:=by
    cases allowed
    · change 0≤n1;omega
    · have h:=hp rfl;change 1≤n1;omega
  have hN:=cast_sub n1 (b2n allowed) huse
  have hL:=cast_sub l1 (grant allowed n1 l1 n2 l2) (ProcDistCellArithmetic.grant_le allowed n1 l1 n2 l2).1
  clear hrow hnext hc hn hd hdn hpos hposn
  simp only [Dist.cGrid,Dist.instCols,List.cons_append,List.nil_append,List.map_cons,List.map_nil,
    List.drop_succ_cons,List.drop_zero,List.take_succ_cons,List.take_zero,List.forall_mem_cons]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,by simp⟩
  · change tr.cell t r Dist.kC*(1 + -tr.cell t r Dist.e1)*(1 + -tr.cell t rnext Dist.kC)=0
    rw [skC,se,nkC];change (1:Fp)*(1+-0)*(1+-1)=0;grind only
  · change tr.cell t r Dist.kC*(1 + -tr.cell t r Dist.e1)*(tr.cell t rnext Dist.a + -tr.cell t r Dist.a)=0
    rw [skC,se,na,sa];grind only
  · change tr.cell t r Dist.kC*(1 + -tr.cell t r Dist.e1)*(tr.cell t rnext Dist.b + -(tr.cell t r Dist.b+1))=0
    rw [skC,se,nb,sb,←ofNat_add']
    change (1:Fp)*(1+-0)*((Fp.ofNat j+1)+-(Fp.ofNat j+1))=0;grind only
  · change tr.cell t r Dist.kC*(1 + -tr.cell t r Dist.e1)*(tr.cell t rnext Dist.s + -tr.cell t r Dist.s)=0
    rw [skC,se,ns,ss];grind only
  · change tr.cell t r Dist.kC*(1 + -tr.cell t r Dist.e1)*(tr.cell t rnext Dist.N1 + -(tr.cell t r Dist.N1 + -tr.cell t r Dist.al))=0
    rw [skC,se,nN,sN,sal];grind only
  · change tr.cell t r Dist.kC*(1 + -tr.cell t r Dist.e1)*(tr.cell t rnext Dist.L1 + -(tr.cell t r Dist.L1 + -tr.cell t r Dist.gb))=0
    rw [skC,se,nL,sL,sgb];grind only
  · change tr.cell t r Dist.kC*(1 + -tr.cell t r Dist.e1)*(tr.cell t rnext Dist.tau + -tr.cell t r Dist.tau)=0
    rw [skC,se,nt,st];grind only
  · change tr.cell t r Dist.kC*(1 + -tr.cell t r Dist.e1)*(tr.cell t rnext Dist.nn + -tr.cell t r Dist.nn)=0
    rw [skC,se,nnn,snn];grind only
end ZkFormal.NearV3.Candidates.ProcDistCellInterior
