import ZkFormal.NearV3.Candidates.ProcScanRequestEndFlag
namespace ZkFormal.NearV3.Candidates.ProcScanRequestBodyBoundary
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcScanRequestFactor ProcScanRequestFieldEquations
attribute [local irreducible] ProcScanRequestFactor.row

/-- Exact metadata required when the successor begins another request. -/
def Next (tr:Trace Fp)(t r:Nat) : Prop :=
  (tr.cell t ((r+1)%tr.height t) Scan.kS=0 ∨tr.cell t ((r+1)%tr.height t) Scan.fQ=1) ∧
  (tr.cell t ((r+1)%tr.height t) Scan.fQ=0 ∨
    (tr.cell t ((r+1)%tr.height t) Scan.cid=tr.cell t r Scan.cid+1 ∧
      ∀col∈Scan.instCols,tr.cell t ((r+1)%tr.height t) col=tr.cell t r col))

set_option maxRecDepth 32768 in
private theorem frame (tr:Trace Fp)(t r:Nat)(pub:List Fp)
    (hb:tr.cell t r Scan.re=0 ∨Next tr t r) :
    ∀e∈(Scan.body.drop 53).take 6,e.eval tr t r pub=0 := by
  simp only [Scan.body,Scan.instCols,Scan.reqCols,List.range_succ,List.range_zero,
    List.map_cons,List.map_nil,List.cons_append,List.nil_append,List.drop_succ_cons,List.drop_zero,
    List.take_succ_cons,List.take_zero,List.forall_mem_cons,List.forall_mem_nil]
  simp only [Scan.notE,Scan.mul3,ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.n,
    ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.smul,
    Expr.eval,Expr.evalWith,rowEnv,Bool.false_eq_true,ite_false,ite_true]
  simp only [List.not_mem_nil,false_implies,implies_true,forall_const,and_true,
    show ((1:Nat):Fp)=1 from rfl]
  rcases hb with hb|⟨ha,hb⟩
  · rw [hb];grind only
  · rcases hb with hb|⟨hb,hcols⟩
    · rw [hb];grind only
    · have h0:=hcols Scan.tau (by simp [Scan.instCols])
      have h1:=hcols Scan.nn (by simp [Scan.instCols])
      have h2:=hcols Scan.base (by simp [Scan.instCols])
      have h3:=hcols Scan.dd (by simp [Scan.instCols])
      clear hcols
      rcases ha with ha|ha <;> grind only

theorem physical (R:Run)(c:CReq)(rho jj cv:Nat)(hr:rho<20)
    (tr:Trace Fp)(t r:Nat)(pub:List Fp)
    (hrow:∀col,tr.cell t r col=cell R c rho jj cv col)
    (hboundary:rho=19→Next tr t r) :
    ∀e∈(Scan.body.drop 53).take 6,e.eval tr t r pub=0 := by
  apply frame
  by_cases he:rho=19
  · exact Or.inr (hboundary he)
  · apply Or.inl
    rw [hrow,ProcScanRequestEndFlag.terminal R c rho jj cv hr,if_neg he]
end ZkFormal.NearV3.Candidates.ProcScanRequestBodyBoundary
