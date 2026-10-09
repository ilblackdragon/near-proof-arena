import ZkFormal.NearV3.Assembly.RcptCandidateNativeComplete

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/-- Gas and version-distance repairs only. The separate routing-q strengthening
and its public normalization are not silently installed by this table. -/
def receiptArithmeticCandidate : Air.Table :=
  { RcptV3.table with constraints :=
    cRegs++cEmit++cStates++cEnd++cChars++cSys++cRoute++cKey++systemGasConstraints++depositAgeConstraints }

set_option maxRecDepth 4096 in
theorem receiptArithmeticCandidate_mult_bool :
    ∀i∈RcptV3.interactions,∀e∈i.mult,Dsl.bool e∈cStates++cEmit := by
  have h : RcptV3.interactions.all (fun i=>i.mult.all (fun e=>(cStates++cEmit).any (fun p=>decide (p=Dsl.bool e))))=true := by decide
  intro i hi e he
  have hh := List.all_eq_true.mp (List.all_eq_true.mp h i hi) e he
  obtain ⟨p,hp,heq⟩ := List.any_eq_true.mp hh
  exact (of_decide_eq_true heq) ▸ hp

theorem receiptCandidate_bool_eval (tr : Trace Fp) (pub : List Fp) (pos : Nat) (e : Expr)
    (h : (Dsl.bool e).eval tr 0 pos pub=0) : e.eval tr 0 pos pub=0 ∨ e.eval tr 0 pos pub=1 := by
  rw [eval_bool] at h
  exact bool_cases h

set_option maxRecDepth 4096 in
theorem receiptArithmeticCandidate_local (tr : Trace Fp) (pub : List Fp)
    (hl : tr.log 0=22)
    (hc : ∀pos,pos<2^22→∀e∈receiptArithmeticCandidate.constraints,e.eval tr 0 pos pub=0) :
    TableLocal receiptArithmeticCandidate tr 0 pub := by
  refine ⟨?_,?_,?_,?_⟩
  · rw [hl];decide
  · rw [hl];decide
  · intro pos hp
    exact hc pos (by simpa only [Trace.height,hl] using hp)
  · intro pos hp i hi e he
    have hm := receiptArithmeticCandidate_mult_bool i hi e he
    have hz := hc pos (by simpa only [Trace.height,hl] using hp) (Dsl.bool e) (by
      simp only [receiptArithmeticCandidate,List.mem_append] at hm ⊢
      grind only)
    exact receiptCandidate_bool_eval tr pub pos e hz

end ZkFormal.NearV3.Assembly.RcptSkeleton
