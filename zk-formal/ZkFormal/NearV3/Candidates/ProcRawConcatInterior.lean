import ZkFormal.NearV3.Candidates.ProcRawConcatStamp
import ZkFormal.NearV3.Candidates.ProcPriorRawActive
namespace ZkFormal.NearV3.Candidates.ProcRawConcatInterior
open ZkFormal.Air ZkFormal.Algebra NearSpec.Bandwidth
open ProcPriorCells ProcPriorRawGen ProcPriorRawSlots ProcRawConcatBoundary

theorem tau_zero (st : State) (vid i : Nat) (present : Bool) :
    (trace st vid present).cell 0 i ProcPriorRawFrame.tau=0 := by
  unfold trace
  cases he : slot st.links.length i <;> simp [he,cells,ProcPriorRawFrame.tau]

theorem not_done (st : State) (vid i : Nat) (present : Bool)
    (hi:i+1<length st.links.length) :
    (trace st vid present).cell 0 i ProcPriorRawFrame.hash *
      (trace st vid present).cell 0 i ProcPriorRawFrame.phaseEnd=0 := by
  rcases coverage st.links.length i (by omega) with ⟨g,hg,rfl,he⟩|⟨j,g,hj,hg,rfl,he⟩|⟨g,hg,rfl,he⟩
  all_goals simp only [trace,he]
  · simp [cells,ProcPriorRawFrame.hash,ProcPriorRawFrame.phaseEnd,isHash,offset,endAt,bit]
    all_goals grind
  · simp [cells,ProcPriorRawFrame.hash,ProcPriorRawFrame.phaseEnd,isHash,offset,endAt,bit]
    all_goals grind
  · have hz:g≠31 := by unfold length at hi; omega
    simp [cells,ProcPriorRawFrame.hash,ProcPriorRawFrame.phaseEnd,isHash,offset,endAt,bit,hz]
    all_goals grind

theorem inside (st : State) (vid i : Nat) (present : Bool) (tauV : Fp)
    (hn:st.links.length<16777216) (hp:present=false→st=State.initial)
    (hi:i+1<length st.links.length) (e : Expr) (he:e∈ProcPriorRawFrame.constraints) :
    e.evalWith (env (stamp tauV ((trace st vid present).cell 0 i))
      (stamp tauV ((trace st vid present).cell 0 (i+1))) 0 0 1)=0 := by
  rw [ProcRawConcatStamp.interior _ _ tauV (tau_zero st vid i present)
    (tau_zero st vid (i+1) present) (not_done st vid i present hi) e he]
  have hh:=ProcPriorRawActive.active_constraints st vid i present hn hp (by omega) e he
  by_cases hz:i=0
  · subst i
    have ha:(trace st vid present).cell 0 0 ProcPriorRawFrame.act=
        (trace st vid present).cell 0 0 ProcPriorRawFrame.first := by
      simp [trace,ProcPriorRawSlots.header _ 0 (by decide +kernel),cells,
        ProcPriorRawFrame.act,ProcPriorRawFrame.first,isHeader,offset,bit]
    rw [ProcRawConcatStamp.without_first _ _ _ (tau_zero st vid 0 present) ha e he] at hh
    exact hh
  · simpa [hz,bit] using hh
end ZkFormal.NearV3.Candidates.ProcRawConcatInterior
