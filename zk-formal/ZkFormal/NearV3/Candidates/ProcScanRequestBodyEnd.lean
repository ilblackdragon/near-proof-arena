import ZkFormal.NearV3.Candidates.ProcScanRequestEndFlag
namespace ZkFormal.NearV3.Candidates.ProcScanRequestBodyEnd
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcScanRequestFactor ProcScanRequestFieldEquations
attribute [local irreducible] ProcScanRequestFactor.row

private theorem counted (R:Run)(c:CReq)(cv:Nat)(hb:c.bits=setBits c.bm) :
    cell R c 19 (ProcScanRequestCount.before c.bm 19) cv Scan.m=
      cell R c 19 (ProcScanRequestCount.before c.bm 19) cv Scan.j+
      (cell R c 19 (ProcScanRequestCount.before c.bm 19) cv Scan.b0+
      cell R c 19 (ProcScanRequestCount.before c.bm 19) cv Scan.b1) := by
  have hp:=ProcScanRequestCells.progress R c 19 (ProcScanRequestCount.before c.bm 19) cv
  have hv:=ProcScanRequestCells.payload R c 19 (ProcScanRequestCount.before c.bm 19) cv
  simp only [cell,hv.2.2.2.2.1,hp.1,hp.2.2.2.1,hp.2.2.2.2.1,ofNat_add']
  apply congrArg Fp.ofNat
  have h:=ProcScanRequestCount.finish c hb
  unfold nextCount at h
  omega

set_option maxRecDepth 32768 in
theorem physical (R:Run)(c:CReq)(rho cv:Nat)(hr:rho<20)(hb:c.bits=setBits c.bm)
    (tr:Trace Fp)(t r:Nat)(pub:List Fp)
    (hrow:∀col,tr.cell t r col=Fp.ofNat (row R c rho (ProcScanRequestCount.before c.bm rho) cv)[col]!) :
    ∀e∈(Scan.body.drop 49).take 4,e.eval tr t r pub=0 := by
  let jj:=ProcScanRequestCount.before c.bm rho
  have hy:=ProcScanRequestFieldFlags.y_test R c rho jj cv hr
  have hz:=ProcScanRequestFieldFlags.y_zero R c rho jj cv
  have hm:=ProcScanRequestEndFlag.mask R c rho jj cv
  have ht:=ProcScanRequestEndFlag.terminal R c rho jj cv hr
  have hs:tr.cell t r Scan.kS=1:=by rw [hrow,(ProcScanRequestCells.controls R c rho jj cv).2.1];rfl
  have hc:∀col,cell R c rho jj cv col=tr.cell t r col:=fun col=>(hrow col).symm
  simp only [hc,Lean.Grind.Ring.sub_eq_add_neg] at hy hz hm ht
  have hcount:tr.cell t r Scan.re*(tr.cell t r Scan.m+
      -(tr.cell t r Scan.j+(tr.cell t r Scan.b0+tr.cell t r Scan.b1)))=0 := by
    by_cases he:rho=19
    · subst rho
      have hh:=counted R c cv hb
      change cell R c 19 jj cv Scan.m=cell R c 19 jj cv Scan.j+
        (cell R c 19 jj cv Scan.b0+cell R c 19 jj cv Scan.b1) at hh
      simp only [hc] at hh
      rw [hh];grind only
    · rw [ht,if_neg he];grind only
  clear hrow hc ht
  simp only [Scan.body,Scan.instCols,Scan.reqCols,List.range_succ,List.range_zero,
    List.map_cons,List.map_nil,List.cons_append,List.nil_append,List.drop_succ_cons,List.drop_zero,
    List.take_succ_cons,List.take_zero,List.forall_mem_cons,List.forall_mem_nil]
  refine ⟨?_,?_,?_,?_,by simp⟩
  · change tr.cell t r Scan.kS*(tr.cell t r Scan.e4+
      -(1 + -((tr.cell t r Scan.y + -(4:Fp))*tr.cell t r Scan.iy)))=0
    rw [hy];grind only
  · change tr.cell t r Scan.kS*(tr.cell t r Scan.y + -(4:Fp))*tr.cell t r Scan.e4=0
    rw [hs];grind only
  · change tr.cell t r Scan.kS*(tr.cell t r Scan.re+
      -(tr.cell t r Scan.e4*tr.cell t r Scan.u0*tr.cell t r Scan.u1))=0
    rw [hm];grind only
  · exact hcount
end ZkFormal.NearV3.Candidates.ProcScanRequestBodyEnd
