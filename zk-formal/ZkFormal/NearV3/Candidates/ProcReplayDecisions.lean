import ZkFormal.NearV3.Candidates.ProcReplayShape
import ZkFormal.NearV3.Candidates.ProcConverted
namespace ZkFormal.NearV3.Candidates.ProcReplayDecisions
open ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcReplayChain ProcReplayShape

def Decisions (z : Nat) (e : Entry) : Prop :=
  e.rem<P ∧ e.ok=(e.cS&&e.cR&&e.cL) ∧ e.zn=(if e.alOut=0 then z+1 else 0)

def EntryInv (z : Nat) (s : EntryAcc) : Prop :=
  ∀e∈s.2.2.2.2.2.2.2.2.2.2.toList,Decisions z e

def Inv (s : ReplayAcc) : Prop :=
  ∀rd∈s.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.toList,∀e∈rd.entries,Decisions rd.z e

theorem rem_lt (cv : Array CReq) (hcv : ProcConverted.Bounded cv) (cid j : Nat)
    (hc : cid<cv.size) : cv[cid]!.incs.length-j-1<P := by
  have hm : cv[cid]!∈cv.toList := by
    rw [getElem!_pos cv cid hc]
    exact Array.getElem_mem_toList hc
  have hn := hcv _ hm
  have hp : 40<P := by decide
  omega

theorem check_lt (a b : Nat) (msg : String) (h : check (decide (a<b)) msg=.ok ()) : a<b := by
  have hh := check_true _ _ h
  simpa using hh

set_option maxHeartbeats 1000000 in
/-- The actual replay constructors determine success bits and zero ordinals;
converted-request bounds imply each emitted remaining-increase counter fits Fp. -/
theorem run_decisions (I : Input) (tau : Nat) (R : Run) (h : Gen.run I tau=.ok R) :
    ∀rd∈R.rounds,∀e∈rd.entries,Decisions rd.z e := by
  have hconv := ProcConverted.run_converted I tau R h
  unfold Gen.run at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals
    change Inv _
    refine ExceptLoop.invariant (α := Round) (ε := String) ?xs ?f Inv ?step ?b _ ?init ?loop
    case loop => assumption
    case init => simp [Inv]
    case step =>
      intro rd hrd s hs out ho
      repeat first | cases ho | split at ho
      all_goals
        rename_i entryOut hentry
        have hi : EntryInv rd.z entryOut := by
          refine ExceptLoop.invariant (α := Nat) (ε := String) ?exs ?ef (EntryInv rd.z) ?estep ?eb _ ?einit ?eloop
          case eloop => exact hentry
          case einit => simp [EntryInv]
          case estep =>
            intro i hil st hst eo heo
            repeat first | cases heo | split at heo
            all_goals repeat first | cases heo | split at heo
            all_goals
              simp only [ExceptLoop.StepInv,EntryInv,Array.toList_push,List.mem_append,List.mem_singleton]
              intro e he
              rcases he with he|rfl
              · exact hst e he
              · refine ⟨?_,rfl,rfl⟩
                apply rem_lt _ hconv
                apply check_lt _ _ "entry cid"
                assumption
        simp only [ExceptLoop.StepInv,Inv,Array.toList_push,List.mem_append,List.mem_singleton]
        intro r hr
        rcases hr with hr|rfl
        · exact hs r hr
        · exact hi
end ZkFormal.NearV3.Candidates.ProcReplayDecisions
