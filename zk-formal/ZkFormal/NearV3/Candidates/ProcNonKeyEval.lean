import ZkFormal.NearV3.Candidates.ProcOtherRows
namespace ZkFormal.NearV3.Candidates.ProcNonKeyEval
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ProcHeightBits ProcNativeRows ProcKindHeight ProcKeyRows ProcOtherRows
open ZkFormal.Chacha.Table.E

theorem pad_inverse : (-(15 : Fp))*Fp.ofNat Gen.Proc.ikcPad=1 := by
  have h := SchedField.inverse_product (fneg 15)
  rw [if_neg (by decide : ¬fneg 15 % P=0),SchedField.fneg_cast] at h
  exact h

theorem scalar_eval (V : PV) (hv : NonKey V) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hc : ∀ c,tr.cell t r c=Fp.ofNat (V.cell c))
    (hboundary : tr.cell t ((r+1)%tr.height t) Proc.kK=0 ∨ V.le=0) :
    ∀ e ∈ Proc.cKey.take 13,e.eval tr t r pub=0 := by
  rcases hboundary with hn | hn
  all_goals rcases hv with ⟨hkk,hkc,hkl,hki⟩
  all_goals simp only [Proc.cKey,List.take,List.append,List.forall_mem_cons,List.forall_mem_nil]
  all_goals simp [Proc.gB,Proc.notE,Proc.mul3,sub,smul,c,n,ZkFormal.Chacha.Table.E.k,
    Expr.eval,Expr.evalWith,rowEnv,hc,PV.cell,Proc.kK,Proc.kl,Proc.kc,Proc.ikc,Proc.le,Proc.tau,Proc.colL,Proc.sbIn,Proc.sbOut,Proc.kq,Proc.Tq,Proc.Kq,Proc.zq,
    ProcKeyScalar.cast_eq,hkk,hkc,hkl,hki] at hn ⊢
  all_goals
    simp only [hn]
    have hi := pad_inverse
    change -(15 : Fp)*(Gen.Proc.ikcPad : Fp)=1 at hi
    grind
end ZkFormal.NearV3.Candidates.ProcNonKeyEval
