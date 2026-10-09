import ZkFormal.NearV3.Candidates.ProcScanRequestFieldBytes
import ZkFormal.NearV3.Candidates.ProcScanRequestFieldCoordinates
namespace ZkFormal.NearV3.Candidates.ProcScanRequestInteriorFrame
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched

set_option maxRecDepth 32768 in
set_option maxHeartbeats 800000 in
theorem frame (tr:Trace Fp)(t r:Nat)(pub:List Fp)
    (C N:Nat→Fp)(hc:∀col,C col=tr.cell t r col)
    (hn:∀col,N col=tr.cell t ((r+1)%tr.height t) col)
    (hs:C Scan.kS=1)(he:C Scan.re=0)(hns:N Scan.kS=1)(hnf:N Scan.fQ=0)
    (hv:N Scan.cur=C Scan.b1*(C Scan.base+C Scan.Q1)+(1-C Scan.b1)*C Scan.cm)
    (hj:N Scan.j=C Scan.j+C Scan.b0+C Scan.b1)
    (hu:N Scan.u0+2*N Scan.u1=C Scan.u0+2*C Scan.u1+1-4*(C Scan.u0*C Scan.u1))
    (hy:N Scan.y=C Scan.y+C Scan.u0*C Scan.u1)
    (hb:(C Scan.u0*C Scan.u1=1 ∧C (Scan.q 0)=C Scan.b0+2*C Scan.b1 ∧
      (∀i<4,N (Scan.q i)=C (Scan.q (i+1)))) ∨
      (C Scan.u0*C Scan.u1=0 ∧C (Scan.q 0)=C Scan.b0+2*C Scan.b1+4*N (Scan.q 0) ∧
      (∀i<4,N (Scan.q (i+1))=C (Scan.q (i+1)))))
    (hk:∀col∈Scan.reqCols,N col=C col) :
    ∀e∈(Scan.body.drop 23).take 26,e.eval tr t r pub=0 := by
  have h0:=hk Scan.tau (by simp [Scan.reqCols])
  have h1:=hk Scan.nn (by simp [Scan.reqCols])
  have h2:=hk Scan.base (by simp [Scan.reqCols])
  have h3:=hk Scan.dd (by simp [Scan.reqCols])
  have h4:=hk Scan.cid (by simp [Scan.reqCols])
  have h5:=hk Scan.s (by simp [Scan.reqCols])
  have h6:=hk Scan.r (by simp [Scan.reqCols])
  have h7:=hk Scan.link (by simp [Scan.reqCols])
  have h8:=hk Scan.m (by simp [Scan.reqCols])
  have h9:=hk Scan.key (by simp [Scan.reqCols])
  simp only [Scan.body,Scan.instCols,Scan.reqCols,List.range_succ,List.range_zero,
    List.map_cons,List.map_nil,List.cons_append,List.nil_append,List.drop_succ_cons,List.drop_zero,
    List.take_succ_cons,List.take_zero,List.forall_mem_cons,List.forall_mem_nil]
  simp only [Scan.gC,Scan.notE,Scan.mul3,Scan.be,Scan.uE,Scan.val1,
    ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.k,
    ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.smul,Expr.eval,Expr.evalWith,rowEnv,
    Bool.false_eq_true,ite_false,ite_true,←hc,←hn]
  simp only [List.not_mem_nil,false_implies,implies_true,forall_const,and_true]
  clear hc hn hk
  rcases hb with ⟨hb,hq,hr⟩|⟨hb,hq,hr⟩
  all_goals
    have hr0:=hr 0 (by decide)
    have hr1:=hr 1 (by decide)
    have hr2:=hr 2 (by decide)
    have hr3:=hr 3 (by decide)
    clear hr
    simp only [show ((1:Nat):Fp)=1 from rfl,show ((2:Nat):Fp)=2 from rfl,
      show ((4:Nat):Fp)=4 from rfl,hs,he,hns,hnf,hb,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
    grind only
end ZkFormal.NearV3.Candidates.ProcScanRequestInteriorFrame
