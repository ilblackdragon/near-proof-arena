import ZkFormal.NearV3.Candidates.ProcScanRequestFieldDivision
import ZkFormal.NearV3.Candidates.ProcScanRequestFieldFlags
namespace ZkFormal.NearV3.Candidates.ProcScanRequestBodyTail
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcScanRequestFactor
attribute [local irreducible] ProcScanRequestFactor.row

set_option maxRecDepth 32768 in
set_option maxHeartbeats 800000 in
theorem physical (R:Run)(c:CReq)(rho jj cv:Nat)(hk:c.key<P)
    (tr:Trace Fp)(t r:Nat)(pub:List Fp)
    (hrow:∀col,tr.cell t r col=Fp.ofNat (row R c rho jj cv)[col]!) :
    ∀e∈Scan.body.drop 59,e.eval tr t r pub=0 := by
  have hd:=ProcScanRequestFieldDivision.divisions R c rho jj cv tr t r pub hrow
  have hb:=ProcScanRequestFieldDivision.remainder_high_bits R c rho jj cv tr t r hrow
  have hm:=ProcScanRequestFieldEquations.intermediate R c rho jj cv
  have hk1:=ProcScanRequestFieldFlags.key_test R c rho jj cv hk
  have hk0:=ProcScanRequestFieldFlags.key_zero R c rho jj cv
  have hcell : ∀col,ProcScanRequestFieldEquations.cell R c rho jj cv col=tr.cell t r col :=
    fun col=>(hrow col).symm
  simp only [hcell,Lean.Grind.Ring.sub_eq_add_neg] at hm hk1 hk0
  have hs:tr.cell t r Scan.kS=1:=by rw [hrow,(ProcScanRequestCells.controls R c rho jj cv).2.1];rfl
  clear hrow hcell
  simp only [Scan.body,Scan.instCols,Scan.reqCols,List.range_succ,List.range_zero,
    List.map_cons,List.map_nil,List.cons_append,List.nil_append,List.drop_succ_cons,List.drop_zero,
    List.forall_mem_cons,List.forall_mem_nil]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,by simp⟩
  · change tr.cell t r Scan.kS*(40*tr.cell t r Scan.Q0+Scan.r0E.eval tr t r pub+
      -(tr.cell t r Scan.dd*(Scan.posE.eval tr t r pub+1)))=0
    rw [hd.1];grind only
  · change tr.cell t r Scan.kS*(40*tr.cell t r Scan.Q1+Scan.r1E.eval tr t r pub+
      -(tr.cell t r Scan.dd*(Scan.posE.eval tr t r pub+2)))=0
    rw [hd.2];grind only
  · change tr.cell t r Scan.kS*tr.cell t r (Scan.rb0 5)*tr.cell t r (Scan.rb0 4)=0
    rw [hs];grind only
  · change tr.cell t r Scan.kS*tr.cell t r (Scan.rb0 5)*tr.cell t r (Scan.rb0 3)=0
    rw [hs];grind only
  · change tr.cell t r Scan.kS*tr.cell t r (Scan.rb1 5)*tr.cell t r (Scan.rb1 4)=0
    rw [hs];grind only
  · change tr.cell t r Scan.kS*tr.cell t r (Scan.rb1 5)*tr.cell t r (Scan.rb1 3)=0
    rw [hs];grind only
  · change tr.cell t r Scan.kS*(tr.cell t r Scan.cm+
      -(tr.cell t r Scan.b0*(tr.cell t r Scan.base+tr.cell t r Scan.Q0)+
      (1 + -tr.cell t r Scan.b0)*tr.cell t r Scan.cur))=0
    rw [hm];grind only
  · change tr.cell t r Scan.kS*(tr.cell t r Scan.zk0 + -(1 + -(tr.cell t r Scan.key*tr.cell t r Scan.ikey)))=0
    rw [hk1];grind only
  · change tr.cell t r Scan.kS*tr.cell t r Scan.key*tr.cell t r Scan.zk0=0
    rw [hs];grind only
end ZkFormal.NearV3.Candidates.ProcScanRequestBodyTail
