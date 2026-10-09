import ZkFormal.NearV3.Candidates.ProcActualRunFactor
import ZkFormal.NearV3.Candidates.ProcModelClock
import ZkFormal.NearV3.Candidates.ProcPushPerm
namespace ZkFormal.NearV3.Candidates.ProcActualBucketGuards
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
private theorem throw_eq {α : Type} (e : String) : (throw e : Except String α)=.error e := rfl

def Tagged (rd : Round) : Prop := ∀b∈rd.bucket,b.key=rd.key ∧ b.z=rd.z
def Inv (s : ProcModelStep.Acc) : Prop := ∀rd∈s.2.2.2.1,Tagged rd

theorem bucket_tags (ps : List Push) (K z : Nat)
    (hz : (!(sortTs (ps.filter (·.key==K))).all (·.z==z))≠true) :
    ∀b∈sortTs (ps.filter (·.key==K)),b.key=K ∧ b.z=z := by
  intro b hb
  have hk := (List.mem_filter.mp ((ProcPushPerm.sort_perm _).mem_iff.mp hb)).2
  have hz' : (sortTs (ps.filter (·.key==K))).all (·.z==z)=true := by simpa using hz
  have hz'' := List.all_eq_true.mp hz' b hb
  exact ⟨by simpa using hk,by simpa using hz''⟩

set_option maxHeartbeats 1000000 in
theorem process_tags (n : Nat) (allowed : Array Bool) (reqs : List NearSpecV3.Scheduler.Req)
    (st0 st : PState) (fuel : Nat) (rs : List Round)
    (h : processEv n allowed reqs st0 fuel=.ok (st,rs)) : ∀rd∈rs,Tagged rd := by
  rw [ProcModelStep.process_eq] at h
  simp only [bind,Except.bind,pure,Except.pure,throw_eq] at h
  repeat first | cases h | split at h
  all_goals
    change Inv _
    refine ExceptLoop.invariant (α := Nat) (ε := String) ?xs ?f Inv ?step ?b _ ?init ?loop
    case loop => assumption
    case init => simp [Inv,ProcModelStep.initial]
    case step =>
      intro i hi s hs out ho
      unfold ProcModelStep.step at ho
      simp only [bind,Except.bind,pure,Except.pure,throw_eq] at ho
      repeat first | cases ho | split at ho
      all_goals repeat first | cases ho | split at ho
      all_goals repeat first | cases ho | split at ho
      all_goals first
        | exact hs
        | simp only [ExceptLoop.StepInv,Inv,List.mem_append,List.mem_singleton]
          intro rd hr
          rcases hr with hr|rfl
          · exact hs rd hr
          · apply bucket_tags; assumption
def collectStep (R K z : Nat) (b : Push) (acc : Array (Nat×Nat×Nat×Nat)) :
    Except String (ForInStep (Array (Nat×Nat×Nat×Nat))) := do
  check (b.key==K && b.z==z) "bucket push key/z"
  let ts := if b.ts<R then b.ts else T0+(b.ts-R)
  return .yield (acc.push (ts,b.key,b.z,b.v))

theorem collect_success (R K z : Nat) (bs : List Push) (acc : Array (Nat×Nat×Nat×Nat))
    (ht : ∀b∈bs,b.key=K ∧ b.z=z) :
    ∃out,forIn bs acc (collectStep R K z)=.ok out ∧ out.size=acc.size+bs.length := by
  induction bs generalizing acc with
  | nil => exact ⟨acc,rfl,by simp⟩
  | cons b bs ih =>
    have hb := ht b (by simp)
    let next := acc.push (if b.ts<R then b.ts else T0+(b.ts-R),b.key,b.z,b.v)
    have hstep : collectStep R K z b acc=.ok (.yield next) := by
      simp [collectStep,hb.1,hb.2,check,next,bind,Except.bind,pure,Except.pure]
    obtain ⟨out,ho,hlen⟩ := ih next (fun b hb => ht b (by simp [hb]))
    exact ⟨out,by simpa only [List.forIn_cons,hstep,bind,Except.bind] using ho,
      by simp only [next,Array.size_push,List.length_cons] at hlen ⊢; omega⟩

/-- Successful corrected processing discharges per-round count and bucket-tag
collection checks. Bucket-size bounds and combined replay remain separate. -/
theorem process_round_guards (I : Input) (st : PState) (rs : List Round)
    (h : ProcActualInput.process I=.ok (st,rs)) (rd : Round) (hrd : rd∈rs)
    (R : Nat) (acc : Array (Nat×Nat×Nat×Nat)) :
    check (rd.steps.length==rd.bucket.length) "steps ≠ bucket"=.ok () ∧
    ∃out,forIn rd.bucket acc (collectStep R rd.key rd.z)=.ok out ∧
      out.size=acc.size+rd.bucket.length := by
  have ht := process_tags I.ids.length I.allowed _ _ st _ rs h rd hrd
  have hc := (ProcModelClock.process_clock I.ids.length I.allowed _ _ st _ rs h).2 rd hrd
  exact ⟨by simp [hc,check,pure,Except.pure],collect_success R rd.key rd.z rd.bucket acc ht⟩

end ZkFormal.NearV3.Candidates.ProcActualBucketGuards
