import ZkFormal.NearV3.Candidates.ProcCodecComparisonConservation
import ZkFormal.NearV3.Candidates.ProcCodecComparisonTotal
namespace ZkFormal.NearV3.Candidates.ProcCodecComparisonConservationLoops
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Sched.Complete
open ZkFormal.NearV3.Assembly.CodecDigest

def Good (s : RecordState) :=s.1.toList.flatMap (fun row=>ProcCodecConcatTraffic.natMessages row B_SCMP true)=s.2.map cmpMsg

theorem phase (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (k f : Nat)
    (st out : ProcPriorCodecRecordStep.State)
    (hst:ProcCodecComparisonConservation.Good st)
    (h:forIn (List.range 8) st (fun g s=>ProcPriorCodecRecordStep.step I R present gb fwd
      (ProcPriorCodecNativeHash.instanceCells I R present vid) k f g s)=.ok out) :
    ProcCodecComparisonConservation.Good out := by
  apply ExceptLoop.invariant _ _ _ ?_ st out hst h
  intro g hg s hs u hu
  exact ProcCodecComparisonConservation.step I R present gb fwd vid k f g s u hs hu

theorem field (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (k f : Nat) (st : RecordState) (out : ForInStep RecordState)
    (hst:Good st) (h:fieldStep I R present vid gb fwd k f st=.ok out) : ExceptLoop.StepInv Good out := by
  unfold fieldStep at h
  cases he:forIn (List.range 8) (st.1,st.2,0,0,0,0)
    (fun g s=>ProcPriorCodecRecordStep.step I R present gb fwd
      (ProcPriorCodecNativeHash.instanceCells I R present vid) k f g s) with
  | error e=>simp only [he,bind,Except.bind] at h;cases h
  | ok s=>
    simp only [he,bind,Except.bind,pure,Except.pure,Except.ok.injEq] at h
    subst out
    exact phase I R present vid gb fwd k f (st.1,st.2,0,0,0,0) s hst he

theorem block (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (k : Nat) (st : RecordState) (out : ForInStep RecordState)
    (hst:Good st) (h:blockStep I R present vid gb fwd k st=.ok out) : ExceptLoop.StepInv Good out := by
  unfold blockStep at h
  cases he:forIn (List.range 3) st (fieldStep I R present vid gb fwd k) with
  | error e=>simp only [he,bind,Except.bind] at h;cases h
  | ok s=>
    simp only [he,bind,Except.bind,pure,Except.pure,Except.ok.injEq] at h
    subst out
    exact ExceptLoop.invariant _ _ Good
      (fun f _ s hs u hu=>field I R present vid gb fwd k f s u hs hu) st s hst he
end ZkFormal.NearV3.Candidates.ProcCodecComparisonConservationLoops
