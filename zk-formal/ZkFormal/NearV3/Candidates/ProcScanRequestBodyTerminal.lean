import ZkFormal.NearV3.Candidates.ProcScanRequestBodyInterior
namespace ZkFormal.NearV3.Candidates.ProcScanRequestBodyTerminal
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcScanRequestFactor ProcScanRequestFieldEquations
attribute [local irreducible] ProcScanRequestFactor.row

set_option maxRecDepth 32768 in
private theorem frame (tr:Trace Fp)(t r:Nat)(pub:List Fp)
    (hs:tr.cell t r Scan.kS=1)(he:tr.cell t r Scan.re=1)
    (hb:tr.cell t r Scan.u0*tr.cell t r Scan.u1=1)
    (hq:tr.cell t r (Scan.q 0)=tr.cell t r Scan.b0+2*tr.cell t r Scan.b1) :
    ∀e∈(Scan.body.drop 23).take 26,e.eval tr t r pub=0 := by
  simp only [Scan.body,Scan.instCols,Scan.reqCols,List.range_succ,List.range_zero,
    List.map_cons,List.map_nil,List.cons_append,List.nil_append,List.drop_succ_cons,List.drop_zero,
    List.take_succ_cons,List.take_zero,List.forall_mem_cons,List.forall_mem_nil]
  simp only [Scan.gC,Scan.notE,Scan.mul3,Scan.be,Scan.uE,Scan.val1,
    ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.k,
    ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.smul,Expr.eval,Expr.evalWith,rowEnv,
    Bool.false_eq_true,ite_false,ite_true,hs,he]
  simp only [List.not_mem_nil,false_implies,implies_true,forall_const,and_true,
    show ((1:Nat):Fp)=1 from rfl,show ((2:Nat):Fp)=2 from rfl,show ((4:Nat):Fp)=4 from rfl]
  grind only

theorem physical (R:Run)(c:CReq)(jj cv:Nat)(tr:Trace Fp)(t r:Nat)(pub:List Fp)
    (hrow:∀col,tr.cell t r col=cell R c 19 jj cv col) :
    ∀e∈(Scan.body.drop 23).take 26,e.eval tr t r pub=0 := by
  have hs:tr.cell t r Scan.kS=1:=by
    rw [hrow];change Fp.ofNat _=1
    rw [(ProcScanRequestCells.controls R c 19 jj cv).2.1];rfl
  have he:tr.cell t r Scan.re=1:=by
    rw [hrow,ProcScanRequestEndFlag.terminal R c 19 jj cv (by decide),if_pos rfl]
  have hp:=ProcScanRequestCells.progress R c 19 jj cv
  have hb:tr.cell t r Scan.u0*tr.cell t r Scan.u1=1:=by
    rw [hrow,hrow]
    simp only [cell,hp.2.2.2.2.2.1,hp.2.2.2.2.2.2.1]
    decide +kernel
  have hq:=ProcScanRequestFieldBytes.exhausted R c 19 jj cv (by decide)
  have hc:∀col,cell R c 19 jj cv col=tr.cell t r col:=fun col=>(hrow col).symm
  simp only [hc] at hq
  exact frame tr t r pub hs he hb hq
end ZkFormal.NearV3.Candidates.ProcScanRequestBodyTerminal
