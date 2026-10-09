import ZkFormal.NearV3.Assembly.SchedulerCodecLoops
import ZkFormal.NearV3.Candidates.ProcPriorCodecStepRows

namespace ZkFormal.NearV3.Assembly.CodecDigest
open Candidates Sched Sched.Gen Sched.Codec ProcPriorCodecRecordStep ProcPriorCodecStepRows

abbrev RecordState := Array (Array Nat) × List (Nat×Nat×Nat)

def fieldStep (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gbA : Array Nat) (fwd : List (Nat×Nat)) (kk f : Nat) (s : RecordState) :
    Except String (ForInStep RecordState) := do
  let st←forIn (List.range 8) (s.1,s.2,0,0,0,0)
    (fun gg st=>step I R present gbA fwd (ProcPriorCodecNativeHash.instanceCells I R present vidV) kk f gg st)
  pure (.yield (st.1,st.2.1))

def blockStep (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gbA : Array Nat) (fwd : List (Nat×Nat)) (kk : Nat) (s : RecordState) :
    Except String (ForInStep RecordState) := do
  let st←forIn (List.range 3) s (fieldStep I R present vidV gbA fwd kk)
  pure (.yield st)

theorem byte_step_quiet (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gbA : Array Nat) (fwd : List (Nat×Nat)) (kk f gg : Nat)
    (hf:f<3) (hg:gg<8) (s : State) (result : ForInStep State)
    (h:step I R present gbA fwd (ProcPriorCodecNativeHash.instanceCells I R present vidV) kk f gg s=.ok result) :
    ∃out added,result=.yield out ∧ out.1.toList=s.1.toList++added ∧ added.length=1 ∧ Quiet added := by
  obtain ⟨out,rfl,tail,htail,hr⟩:=successful I R present gbA fwd _ kk f gg s result hf hg h
  refine ⟨out,[record I R present (ProcPriorCodecNativeHash.instanceCells I R present vidV)
    (ProcPriorCodecExtra.baseExtra R.n kk f gg (b2n I.allowed[kk]!) gbA[kk]!++tail) kk f gg],rfl,?_,rfl,?_⟩
  · rw [hr,Array.toList_push]
  · intro row hm
    simp only [List.mem_singleton] at hm
    subst row
    unfold record
    apply record_digest_gate
    exact ProcPriorCodecExtraColumns.extra_avoids_dgg _ _ _ _ _ _ _ htail

theorem field_step_quiet (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gbA : Array Nat) (fwd : List (Nat×Nat)) (kk f : Nat) (hf:f<3)
    (s : RecordState) (result : ForInStep RecordState)
    (h:fieldStep I R present vidV gbA fwd kk f s=.ok result) :
    ∃out added,result=.yield out ∧ out.1.toList=s.1.toList++added ∧ added.length=8 ∧ Quiet added := by
  unfold fieldStep at h
  cases he:forIn (List.range 8) (s.1,s.2,0,0,0,0)
    (fun gg st=>step I R present gbA fwd (ProcPriorCodecNativeHash.instanceCells I R present vidV) kk f gg st) with
  | error e=>simp only [he,bind,Except.bind] at h;cases h
  | ok st=>
    simp only [he,bind,Except.bind,pure,Except.pure,Except.ok.injEq] at h
    subst result
    obtain ⟨added,hr,hc,hq⟩:=loop_quiet (List.range 8) _ (fun st:State=>st.1) 1
      (fun gg hg s out h=>byte_step_quiet I R present vidV gbA fwd kk f gg hf (List.mem_range.mp hg) s out h)
      _ _ he
    exact ⟨(st.1,st.2.1),added,rfl,hr,by simpa using hc,hq⟩

theorem block_step_quiet (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gbA : Array Nat) (fwd : List (Nat×Nat)) (kk : Nat)
    (s : RecordState) (result : ForInStep RecordState)
    (h:blockStep I R present vidV gbA fwd kk s=.ok result) :
    ∃out added,result=.yield out ∧ out.1.toList=s.1.toList++added ∧ added.length=24 ∧ Quiet added := by
  unfold blockStep at h
  cases he:forIn (List.range 3) s (fieldStep I R present vidV gbA fwd kk) with
  | error e=>simp only [he,bind,Except.bind] at h;cases h
  | ok st=>
    simp only [he,bind,Except.bind,pure,Except.pure,Except.ok.injEq] at h
    subst result
    obtain ⟨added,hr,hc,hq⟩:=loop_quiet (List.range 3) _ (fun st:RecordState=>st.1) 8
      (fun f hf s out h=>field_step_quiet I R present vidV gbA fwd kk f (List.mem_range.mp hf) s out h)
      _ _ he
    exact ⟨st,added,rfl,hr,by simpa using hc,hq⟩

theorem record_loop_quiet (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gbA : Array Nat) (fwd : List (Nat×Nat)) (s out : RecordState)
    (h:forIn (List.range (R.n*R.n)) s (blockStep I R present vidV gbA fwd)=.ok out) :
    ∃added,out.1.toList=s.1.toList++added ∧ added.length=24*(R.n*R.n) ∧ Quiet added := by
  obtain ⟨added,hr,hc,hq⟩:=loop_quiet (List.range (R.n*R.n)) _ (fun st:RecordState=>st.1) 24
    (fun kk _ s out h=>block_step_quiet I R present vidV gbA fwd kk s out h) s out h
  exact ⟨added,hr,by simpa using hc,hq⟩

end ZkFormal.NearV3.Assembly.CodecDigest
