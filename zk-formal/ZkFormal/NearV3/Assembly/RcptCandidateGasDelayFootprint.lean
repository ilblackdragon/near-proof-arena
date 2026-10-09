import ZkFormal.NearV3.Assembly.RcptCandidateGasDelayLocal

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def candidateGasDelayColumn (col : Nat) : Bool :=
  col∈[sGP,fs,fe,pc,gq] || decide (xb 0≤col ∧ col<xb 8) || decide (dl 0≤col ∧ col<dl 8)

def candidateGasDelayFootprint : Expr→Bool
  | .const _ | .pub _=>true
  | .col col nx=>if nx then decide (dl 0≤col ∧ col<dl 8) else candidateGasDelayColumn col
  | .add a b | .mul a b=>candidateGasDelayFootprint a && candidateGasDelayFootprint b
  | .neg a=>candidateGasDelayFootprint a
  | _=>false

theorem candidateGasDelay_footprint : candidateGasDelayConstraints.all candidateGasDelayFootprint=true := by decide

theorem candidateGasDelay_no_emission (col : Nat) (hc : candidateGasDelayColumn col=true) : emissionColumn col=false := by
  simp only [candidateGasDelayColumn,Bool.or_eq_true,decide_eq_true_eq,List.mem_cons,List.not_mem_nil,or_false] at hc
  simp only [sGP,fs,fe,pc,gq,xb,dl] at hc
  simp only [emissionColumn,decide_eq_false_iff_not]
  omega

theorem candidateGasDelay_eval_agree (tr tr' : Trace Fp) (t pos t' pos' : Nat) (pub : List Fp)
    (hc : ∀col,candidateGasDelayColumn col=true→tr.cell t pos col=tr'.cell t' pos' col)
    (hn : ∀col,dl 0≤col ∧ col<dl 8→tr.cell t ((pos+1)%tr.height t) col=
      tr'.cell t' ((pos'+1)%tr'.height t') col)
    (e : Expr) (he : candidateGasDelayFootprint e=true) : e.eval tr t pos pub=e.eval tr' t' pos' pub := by
  induction e with
  | const | pub => rfl
  | col col nx =>
    cases nx
    · exact hc col he
    · exact hn col (of_decide_eq_true he)
  | isFirst | isLast | isTransition => cases he
  | add a b ia ib =>
    have hh : candidateGasDelayFootprint a=true ∧ candidateGasDelayFootprint b=true := by simpa only [candidateGasDelayFootprint,Bool.and_eq_true] using he
    simp only [eval_add,ia hh.1,ib hh.2]
  | mul a b ia ib =>
    have hh : candidateGasDelayFootprint a=true ∧ candidateGasDelayFootprint b=true := by simpa only [candidateGasDelayFootprint,Bool.and_eq_true] using he
    simp only [eval_mul,ia hh.1,ib hh.2]
  | neg a ia => simp only [eval_neg,ia he]

theorem candidateGasDelay_inactive (tr : Trace Fp) (pos : Nat) (pub : List Fp)
    (hz : tr.cell 0 pos sGP=0 ∨ (tr.cell 0 pos fs=0 ∧ tr.cell 0 pos fe=1)) :
    ∀e∈candidateGasDelayConstraints,e.eval tr 0 pos pub=0 := by
  intro e he
  simp only [candidateGasDelayConstraints,List.mem_append] at he
  rcases he with (he|he)|he
  · obtain ⟨j,_,rfl⟩ := List.mem_map.mp he
    simp only [gp,eval_mul3,eval_c]
    rcases hz with hz|⟨hz,_⟩ <;> rw [hz] <;> grind only
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl
    all_goals simp only [gp,eval_mul3,eval_not,eval_c]
    all_goals rcases hz with hz|⟨_,hz⟩ <;> rw [hz] <;> grind only
  · obtain ⟨j,_,rfl⟩ := List.mem_map.mp he
    simp only [gp,eval_mul3,eval_not,eval_c]
    rcases hz with hz|⟨_,hz⟩ <;> rw [hz] <;> grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
