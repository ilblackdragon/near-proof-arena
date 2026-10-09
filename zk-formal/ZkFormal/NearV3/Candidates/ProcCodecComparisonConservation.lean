import ZkFormal.NearV3.Candidates.ProcCodecComparisonStepTraffic
namespace ZkFormal.NearV3.Candidates.ProcCodecComparisonConservation
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec ProcPriorCodecRecordStep
open ZkFormal.NearV3.Sched.Complete

def Good (s : State) : Prop :=
  s.1.toList.flatMap (fun row=>ProcCodecConcatTraffic.natMessages row B_SCMP true)=s.2.1.map cmpMsg

theorem step (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd : List (Nat×Nat)) (vid k f g : Nat) (st : State) (out : ForInStep State)
    (hs:Good st)
    (h:ProcPriorCodecRecordStep.step I R present gb fwd (ProcPriorCodecNativeHash.instanceCells I R present vid) k f g st=.ok out) :
    ExceptLoop.StepInv Good out := by
  obtain ⟨s,a,rfl,ha,ht⟩:=ProcCodecComparisonStepTraffic.step_traffic I R present gb fwd vid k f g st out h
  obtain ⟨u,hu,hc⟩:=ProcCodecComparisonAppend.step_requests I R present gb fwd
    (ProcPriorCodecNativeHash.instanceCells I R present vid) k f g st (.yield s) h
  have he:u=s := (ForInStep.yield.inj hu).symm
  subst u
  change Good s
  unfold Good at hs ⊢
  rw [ha,hc,Array.toList_push,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    List.map_append,hs,ht]
end ZkFormal.NearV3.Candidates.ProcCodecComparisonConservation
