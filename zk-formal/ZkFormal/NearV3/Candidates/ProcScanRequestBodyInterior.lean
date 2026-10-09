import ZkFormal.NearV3.Candidates.ProcScanRequestInteriorFrame
import ZkFormal.NearV3.Candidates.ProcScanRequestEndFlag
namespace ZkFormal.NearV3.Candidates.ProcScanRequestBodyInterior
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcScanRequestFactor ProcScanRequestFieldEquations
attribute [local irreducible] ProcScanRequestFactor.row

private theorem byte_end (R:Run)(c:CReq)(rho jj cv:Nat) :
    cell R c rho jj cv Scan.u0*cell R c rho jj cv Scan.u1=if rho%4=3 then 1 else 0 := by
  have hp:=ProcScanRequestCells.progress R c rho jj cv
  simp only [cell,hp.2.2.2.2.2.1,hp.2.2.2.2.2.2.1,ofNat_mul']
  rw [(ProcScanBitmapArithmetic.two_bits (rho%4) (Nat.mod_lt _ (by decide))).2]
  simp only [b2n,beq_iff_eq]
  split <;> rfl

theorem physical (R:Run)(c:CReq)(rho jj cv:Nat)(hr:rho<19)
    (tr:Trace Fp)(t r:Nat)(pub:List Fp)
    (hrow:∀col,tr.cell t r col=cell R c rho jj cv col)
    (hnext:∀col,tr.cell t ((r+1)%tr.height t) col=
      cell R c (rho+1) (nextCount c rho jj) (nextCur R c rho cv) col) :
    ∀e∈(Scan.body.drop 23).take 26,e.eval tr t r pub=0 := by
  let C:=cell R c rho jj cv
  let N:=cell R c (rho+1) (nextCount c rho jj) (nextCur R c rho cv)
  have hc:=ProcScanRequestCells.controls R c rho jj cv
  have hn:=ProcScanRequestCells.controls R c (rho+1) (nextCount c rho jj) (nextCur R c rho cv)
  have hs:C Scan.kS=1:=by change Fp.ofNat _=1;rw [hc.2.1];rfl
  have hns:N Scan.kS=1:=by change Fp.ofNat _=1;rw [hn.2.1];rfl
  have hnf:N Scan.fQ=0:=by
    change Fp.ofNat _=0
    rw [hn.2.2.1]
    simp only [b2n,beq_iff_eq,if_neg (show rho+1≠0 by omega)]
    rfl
  have he:C Scan.re=0:=by
    change cell R c rho jj cv Scan.re=0
    rw [ProcScanRequestEndFlag.terminal R c rho jj cv (by omega),if_neg (by omega)]
  apply ProcScanRequestInteriorFrame.frame tr t r pub C N (fun col=>(hrow col).symm)
    (fun col=>(hnext col).symm) hs he hns hnf
    (current_next R c rho jj cv) (count_next R c rho jj cv)
    (ProcScanRequestFieldCoordinates.next_u R c rho jj cv _ _)
    (ProcScanRequestFieldCoordinates.next_y R c rho jj cv _ _)
  · have hb:=byte_end R c rho jj cv
    by_cases hu:rho%4=3
    · exact Or.inl ⟨by simpa only [if_pos hu] using hb,
        ProcScanRequestFieldBytes.exhausted R c rho jj cv hu,
        fun i hi=>ProcScanRequestFieldBytes.rotates R c rho jj cv _ _ i hi hu⟩
    · exact Or.inr ⟨by simpa only [if_neg hu] using hb,
        ProcScanRequestFieldBytes.consumes R c rho jj cv _ _ hu,
        fun i hi=>ProcScanRequestFieldBytes.stays R c rho jj cv _ _ i hi hu⟩
  · intro col hcol
    exact constants R c rho jj cv _ _ _ col hcol
end ZkFormal.NearV3.Candidates.ProcScanRequestBodyInterior
