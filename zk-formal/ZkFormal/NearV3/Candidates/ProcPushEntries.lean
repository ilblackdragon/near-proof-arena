import ZkFormal.NearV3.Candidates.ProcEntryEvent
import ZkFormal.NearV3.Candidates.ProcPushPerm
namespace ZkFormal.NearV3.Candidates.ProcPushEntries
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen NearSpecV3.Scheduler
private theorem throw_eq {α : Type} (e : String) : (throw e : Except String α)=.error e := rfl

def pushOf (K z : Nat) (e : Step) : List Push :=
  if e.ok && !e.last then
    [⟨e.t,e.aOut,if e.aOut=0 then (if K=0 then z+1 else 1) else 0,e.v+1⟩]
  else []

def pushes (K z : Nat) (es : List Step) := es.flatMap (pushOf K z)
def Inv (K z : Nat) (pending : List Push) (s : ProcModelStep.EntryAcc) : Prop :=
  s.1=pending++pushes K z s.2.2.2

theorem entry_inv (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (K z v : Nat) (pending : List Push) (s : ProcModelStep.EntryAcc) (hs : Inv K z pending s)
    (out : ForInStep ProcModelStep.EntryAcc)
    (h : ProcModelStep.entryStep n allowed reqs K z v s=.ok out) :
    ExceptLoop.StepInv (Inv K z pending) out := by
  unfold ProcModelStep.entryStep at h
  simp only [bind,Except.bind,pure,Except.pure,throw_eq] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals
    change s.1=pending++pushes K z s.2.2.2 at hs
    simp_all only [ExceptLoop.StepInv,Inv,pushes,pushOf,List.flatMap_append,List.flatMap_cons,
      List.flatMap_nil,List.append_nil,List.append_assoc,Bool.false_eq_true,ite_true,ite_false]

theorem entries_pushes (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (K z : Nat) (vs : List Nat) (pending : List Push) (st : PState) (t : Nat)
    (out : ProcModelStep.EntryAcc)
    (h : forIn vs (pending,st,t,[]) (ProcModelStep.entryStep n allowed reqs K z)=.ok out) :
    out.1=pending++pushes K z out.2.2.2 := by
  apply ExceptLoop.invariant vs (ProcModelStep.entryStep n allowed reqs K z) (Inv K z pending)
    (fun v _ s hs out h=>entry_inv n allowed reqs K z v pending s hs out h) _ out ?_ h
  simp [Inv,pushes]
end ZkFormal.NearV3.Candidates.ProcPushEntries
