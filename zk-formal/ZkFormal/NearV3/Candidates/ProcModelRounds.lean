import ZkFormal.NearV3.Candidates.ProcReplayEntries
import ZkFormal.NearV3.Candidates.ExceptSummary
namespace ZkFormal.NearV3.Candidates.ProcModelRounds
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ProcReplayChain

def model (I : Input) : Except String (PState × List Round) :=
  let lp := linkPass I.ids.length I.p I.allowed (a0Src I.ids I.prev)
  let reqs := convRaw I.p I.ids.length I.raw
  processEv I.ids.length I.allowed reqs
    ⟨lp.sb,lp.rb,lp.a2,lp.g2,NearSpecV3.Rng.ofSeed I.seed⟩
    (1+(reqs.map (·.incs.length)).sum)

def keys (s : ReplayAcc) : List (Nat×Nat) :=
  s.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.toList.map (fun rd=>(rd.K,rd.z))

set_option maxHeartbeats 600000 in
/-- The replayed round key/ordinal sequence is exactly that of the successful
native event model, preserving order and multiplicity. -/
theorem run_model (I : Input) (tau : Nat) (R : Run) (h : Gen.run I tau=.ok R) :
    ∃st rs,model I=.ok (st,rs) ∧ R.rounds.map (fun rd=>(rd.K,rd.z))=rs.map (fun rd=>(rd.key,rd.z)) := by
  unfold Gen.run at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals
    refine ⟨?st,?rs,?hm,?hk⟩
    case hm => assumption
    case hk =>
      change keys _=_
      refine ExceptSummary.from_empty (ε := String) ?xs ?f keys (fun rd : Round=>(rd.key,rd.z)) ?step ?b _ ?init ?loop
      case loop => assumption
      case init => rfl
      case step =>
        intro rd hrd s out ho
        repeat first | cases ho | split at ho
        all_goals
          refine ⟨_,rfl,?_⟩
          simp [keys,Array.toList_push,List.map_append]
end ZkFormal.NearV3.Candidates.ProcModelRounds
