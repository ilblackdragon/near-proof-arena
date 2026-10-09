import ZkFormal.NearV3.Candidates.ProcScanRequestZeroValue
import ZkFormal.NearV3.Candidates.ProcScanRequestDist
namespace ZkFormal.NearV3.Candidates.ProcScanRequestBodyPrefix
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcScanRequestFactor
attribute [local irreducible] ProcScanRequestFactor.row

set_option maxRecDepth 32768 in
private theorem frame (tr:Trace Fp)(t r:Nat)(pub:List Fp)
    (hs:tr.cell t r Scan.kS=1)(hp:tr.cell t r Scan.kP=0)(hv:tr.cell t r Scan.bvz=0)
    (hu0:tr.cell t r Scan.us0*(1-tr.cell t r Scan.b0)=0)
    (hu1:tr.cell t r Scan.us1*(1-tr.cell t r Scan.b1)=0) :
    ∀e∈Scan.body.take 16,e.eval tr t r pub=0 := by
  simp only [Lean.Grind.Ring.sub_eq_add_neg] at hu0 hu1
  simp [Scan.body,Scan.instCols,Scan.reqCols,Scan.notE,Scan.mul3,
    ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.k,
    ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.smul,
    Expr.eval,Expr.evalWith,rowEnv,hs,hp,hv,hu0,hu1]
  simp only [show ((1:Nat):Fp)=1 from rfl]
  grind only

private theorem use_bit (b u:Bool) :
    Fp.ofNat (b2n (b2n b==1 && u))*(1-Fp.ofNat (b2n b))=0 := by
  cases b <;> cases u <;> decide +kernel

theorem physical (R:Run)(c:CReq)(rho jj cv:Nat)(tr:Trace Fp)(t r:Nat)(pub:List Fp)
    (hrow:∀col,tr.cell t r col=Fp.ofNat (row R c rho jj cv)[col]!) :
    ∀e∈Scan.body.take 16,e.eval tr t r pub=0 := by
  have hs:tr.cell t r Scan.kS=1:=by rw [hrow,(ProcScanRequestCells.controls R c rho jj cv).2.1];rfl
  have hp:tr.cell t r Scan.kP=0:=by rw [hrow,Scan.kP,(ProcScanRequestQuietCells.zeros R c rho jj cv).1];rfl
  have hv:tr.cell t r Scan.bvz=0:=by rw [hrow,ProcScanRequestZeroValue.zero_value];rfl
  apply frame tr t r pub hs hp hv
  · rw [hrow,hrow,(ProcScanRequestQuietCells.uses R c rho jj cv).1,
      (ProcScanRequestCells.progress R c rho jj cv).2.2.2.1]
    exact use_bit _ _
  · rw [hrow,hrow,(ProcScanRequestQuietCells.uses R c rho jj cv).2,
      (ProcScanRequestCells.progress R c rho jj cv).2.2.2.2.1]
    exact use_bit _ _
end ZkFormal.NearV3.Candidates.ProcScanRequestBodyPrefix
