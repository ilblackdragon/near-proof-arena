import ZkFormal.NearV3.Assembly.RcptCandidateBounds

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RcptSkeleton
variable {tr : Trace Fp} {pub : List Fp} {tt pos : Nat}

/-- The candidate's non-system comparison gate is derived from its actual
constraint, rather than added as a semantic side condition. -/
theorem gas_gate (hL : TableLocal receiptArithmeticCandidate tr tt pub)
    (hp : pos<tr.height tt) (hr : rowE.eval tr tt pos pub=1) :
    tr.cell tt pos gq=tr.cell tt pos ge*(1-tr.cell tt pos sys) := by
  have h := con hL hp (mem_gs (show
    Expr.mul rowE (sub (c gq) (.mul (c ge) (Dsl.not (c sys))))∈systemGasConstraints by
      simp [systemGasConstraints,gasConstraintsWith]))
  simp only [eval_mul,eval_sub,eval_c,eval_not,hr] at h
  grind

theorem gas_surplus_system (hL : TableLocal receiptArithmeticCandidate tr tt pub)
    (hp : pos<tr.height tt) (hr : rowE.eval tr tt pos pub=1)
    (hs : tr.cell tt pos sys=1) : systemSurplus.eval tr tt pos pub=0 := by
  have hg := gas_gate hL hp hr
  simp only [systemSurplus,eval_mul,eval_c]
  rw [hg,hs]
  grind

theorem gas_surplus_ordinary (hL : TableLocal receiptArithmeticCandidate tr tt pub)
    (hp : pos<tr.height tt) (hr : rowE.eval tr tt pos pub=1)
    (hs : tr.cell tt pos sys=0) : systemSurplus.eval tr tt pos pub=surE.eval tr tt pos pub := by
  have hg := gas_gate hL hp hr
  simp only [systemSurplus,surE,eval_mul,eval_c]
  rw [hg,hs]
  grind

theorem gas_effective_system (hL : TableLocal receiptArithmeticCandidate tr tt pub)
    (hp : pos<tr.height tt) (hg : tr.cell tt pos sGP=1)
    (hs : tr.cell tt pos sys=1) : tr.cell tt pos pc=0 := by
  have h := con hL hp (mem_gs (show
    Expr.mul gp (sub (c pc) (.mul (Dsl.not (c sys)) pE))∈systemGasConstraints by
      simp [systemGasConstraints,gasConstraintsWith]))
  simp only [gp,eval_mul,eval_sub,eval_c,eval_not,hg,hs] at h
  grind

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
