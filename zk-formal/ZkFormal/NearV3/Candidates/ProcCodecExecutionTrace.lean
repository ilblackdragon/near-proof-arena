import ZkFormal.NearV3.Assembly.SchedulerCodecRecordLoops
namespace ZkFormal.NearV3.Candidates.ProcCodecExecutionTrace
open ZkFormal.NearV3.Assembly.CodecDigest
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

/-- Ordered successful yields retain every intermediate state, so adjacent-row
proofs can use the actual prior accumulator rather than assume row invariants. -/
inductive Steps {α σ ε : Type} (step : α→σ→Except ε (ForInStep σ)) : List α→σ→σ→Prop
  | nil (s : σ) : Steps step [] s s
  | cons {a : α} {xs : List α} {s mid out : σ}
      (head : step a s=.ok (.yield mid)) (tail : Steps step xs mid out) :
      Steps step (a::xs) s out

theorem from_loop {α σ ε : Type} (xs : List α) (step : α→σ→Except ε (ForInStep σ))
    (hy : ∀a∈xs,∀s v,step a s=.ok v→∃mid,v=.yield mid)
    (s out : σ) (h : forIn xs s step=.ok out) : Steps step xs s out := by
  induction xs generalizing s with
  | nil => simp only [List.forIn_nil] at h; cases h; exact .nil _
  | cons a xs ih =>
    rw [List.forIn_cons] at h
    cases he : step a s with
    | error e => simp only [he,bind,Except.bind] at h; cases h
    | ok v =>
      obtain ⟨mid,rfl⟩ := hy a (by simp) s v he
      simp only [he,bind,Except.bind] at h
      exact .cons he (ih (fun a ha=>hy a (by simp [ha])) mid h)

theorem append_split {α σ ε : Type} {step : α→σ→Except ε (ForInStep σ)}
    (a b : List α) {s out : σ} (h : Steps step (a++b) s out) :
    ∃mid,Steps step a s mid ∧ Steps step b mid out := by
  induction a generalizing s with
  | nil => exact ⟨s,.nil s,h⟩
  | cons x xs ih =>
    cases h with
    | cons he ht =>
      obtain ⟨mid,ha,hb⟩ := ih ht
      exact ⟨mid,.cons he ha,hb⟩

/-- Two neighboring rows share the exact intermediate machine state. -/
theorem adjacent_split {α σ ε : Type} {step : α→σ→Except ε (ForInStep σ)}
    (pre post : List α) (a b : α) {s out : σ}
    (h : Steps step (pre++a::b::post) s out) :
    ∃before mid after,Steps step pre s before ∧ step a before=.ok (.yield mid) ∧
      step b mid=.ok (.yield after) ∧ Steps step post after out := by
  obtain ⟨before,hpre,ht⟩ := append_split pre (a::b::post) h
  cases ht with
  | cons ha tail =>
    cases tail with
    | cons hb rest => exact ⟨before,_,_,hpre,ha,hb,rest⟩

theorem field_execution (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (k f : Nat) (hf : f<3)
    (s out : ProcPriorCodecRecordStep.State)
    (h : forIn (List.range 8) s
      (fun g st=>ProcPriorCodecRecordStep.step I R present gb fwd
        (ProcPriorCodecNativeHash.instanceCells I R present vid) k f g st)=.ok out) :
    Steps (fun g st=>ProcPriorCodecRecordStep.step I R present gb fwd
      (ProcPriorCodecNativeHash.instanceCells I R present vid) k f g st) (List.range 8) s out := by
  apply from_loop _ _ _ s out h
  intro g hg st v hv
  obtain ⟨next,_,he,_,_,_⟩ := byte_step_quiet I R present vid gb fwd k f g hf (List.mem_range.mp hg) st v hv
  exact ⟨next,he⟩

theorem record_execution (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (k : Nat) (s out : RecordState)
    (h : forIn (List.range 3) s (fieldStep I R present vid gb fwd k)=.ok out) :
    Steps (fieldStep I R present vid gb fwd k) (List.range 3) s out := by
  apply from_loop _ _ _ s out h
  intro f hf st v hv
  obtain ⟨next,_,he,_,_,_⟩ := field_step_quiet I R present vid gb fwd k f (List.mem_range.mp hf) st v hv
  exact ⟨next,he⟩
theorem blocks_execution (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (s out : RecordState)
    (h : forIn (List.range (R.n*R.n)) s (blockStep I R present vid gb fwd)=.ok out) :
    Steps (blockStep I R present vid gb fwd) (List.range (R.n*R.n)) s out := by
  apply from_loop _ _ _ s out h
  intro k hk st v hv
  obtain ⟨next,_,he,_,_,_⟩ := block_step_quiet I R present vid gb fwd k st v hv
  exact ⟨next,he⟩
end ZkFormal.NearV3.Candidates.ProcCodecExecutionTrace
