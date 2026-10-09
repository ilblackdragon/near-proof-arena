import ZkFormal.NearV3.Candidates.ProcPriorCodecGen
import ZkFormal.NearV3.Candidates.ExceptLoop
namespace ZkFormal.NearV3.Candidates.ProcCodecComparisonCost
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcPriorCodecRecordStep

def byteCost (g : Nat) : Nat:=if g=2 ∨ g=7 then 1 else 0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 800000 in
theorem step_cost (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd inst : List (Nat×Nat)) (k f g : Nat) (st : State) (out : ForInStep State)
    (h:step I R present gb fwd inst k f g st=.ok out) :
    ∃s,out=.yield s ∧ s.2.1.length≤st.2.1.length+byteCost g := by
  have az (n j : Nat) : (Array.replicate n (0:Nat))[j]! = 0 := by
    by_cases hj:j<n
    · simp [getElem!_pos, hj]
    · simp [getElem!_neg, hj]
  by_cases h0:f=0 ∧ g=0
  all_goals by_cases h2:f=2
  all_goals by_cases hg2:g=2
  all_goals by_cases hg7:g=7
  all_goals by_cases hge:g≥2
  all_goals try omega
  all_goals simp (maxSteps := 1000000) only [step,az,Nat.zero_div,Nat.zero_mod,ne_eq,not_true_eq_false,h0,h2,hg2,hg7,hge,and_true,and_false,true_and,false_and,
    ite_true,ite_false,ite_self,Nat.reduceEqDiff,Nat.reduceLeDiff,Nat.reduceLT,bind,Except.bind,pure,Except.pure] at h
  all_goals repeat first | cases h | split at h
  all_goals try { unfold check at h; simp only [bind,Except.bind,pure,Except.pure] at h }
  all_goals repeat first | cases h | split at h
  all_goals first | refine ⟨_,rfl,?_⟩ | refine ⟨_,(Except.ok.inj h).symm,?_⟩
  all_goals simp only [List.length_append,List.length_cons,List.length_nil]
  all_goals unfold byteCost
  all_goals split <;> omega

/-- A generic successful yield-only loop pays the sum of its actual costs. -/
theorem loop_cost {α σ ε : Type} (xs : List α) (f : α→σ→Except ε (ForInStep σ))
    (measure : σ→Nat) (cost : α→Nat)
    (hf:∀a∈xs,∀s out,f a s=.ok out→∃u,out=.yield u ∧ measure u≤measure s+cost a)
    (st out : σ) (h:forIn xs st f=.ok out) : measure out≤measure st+(xs.map cost).sum := by
  induction xs generalizing st with
  | nil=>simp only [List.forIn_nil] at h;cases h;simp
  | cons a xs ih=>
    rw [List.forIn_cons] at h
    cases he:f a st with
    | error e=>simp only [he,bind,Except.bind] at h;cases h
    | ok u=>
      obtain ⟨v,rfl,hv⟩:=hf a (by simp) st u he
      simp only [he,bind,Except.bind] at h
      have hh:=ih (fun b hb=>hf b (by simp [hb])) v h
      simp only [List.map_cons,List.sum_cons]
      omega

theorem phase_cost (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd inst : List (Nat×Nat)) (k f : Nat) (st out : State)
    (h:forIn (List.range 8) st (fun g s=>step I R present gb fwd inst k f g s)=.ok out) :
    out.2.1.length≤st.2.1.length+2 := by
  have hh:=loop_cost (List.range 8) (fun g s=>step I R present gb fwd inst k f g s)
    (fun s:State=>s.2.1.length) byteCost (fun g _ s o=>step_cost I R present gb fwd inst k f g s o) st out h
  have hc:((List.range 8).map byteCost).sum=2:=by decide +kernel
  simpa only [hc] using hh
end ZkFormal.NearV3.Candidates.ProcCodecComparisonCost
