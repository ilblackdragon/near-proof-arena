import ZkFormal.NearV3.Assembly.SchedulerCodecNonhash

namespace ZkFormal.NearV3.Assembly.CodecDigest
open ZkFormal.NearV3.Sched.Codec

def Quiet (rows : List (Array Nat)) : Prop := ∀a∈rows,a[dgg]! =0

/-- Successful row-pushing loops retain their prefix and add the exact number
of quiet rows; errors and early termination are not silently discarded. -/
theorem loop_quiet {α σ ε : Type} (xs : List α) (step : α→σ→Except ε (ForInStep σ))
    (rows : σ→Array (Array Nat)) (cost : Nat)
    (hf : ∀a∈xs,∀s out,step a s=.ok out→∃s' added,out=.yield s' ∧
      (rows s').toList=(rows s).toList++added ∧ added.length=cost ∧ Quiet added)
    (s out : σ) (h : forIn xs s step=.ok out) :
    ∃added,(rows out).toList=(rows s).toList++added ∧ added.length=cost*xs.length ∧ Quiet added := by
  induction xs generalizing s with
  | nil=>
    simp only [List.forIn_nil] at h
    cases h
    exact ⟨[],by simp,by simp,by simp [Quiet]⟩
  | cons a xs ih=>
    rw [List.forIn_cons] at h
    cases he:step a s with
    | error e=>simp only [he,bind,Except.bind] at h;cases h
    | ok val=>
      obtain ⟨next,added,rfl,hrows,hcount,hquiet⟩:=hf a (by simp) s val he
      simp only [he,bind,Except.bind] at h
      obtain ⟨rest,htrows,htcount,htquiet⟩:=ih (fun a ha=>hf a (by simp [ha])) next h
      refine ⟨added++rest,?_,?_,?_⟩
      · rw [htrows,hrows,List.append_assoc]
      · simp only [List.length_append,List.length_cons,hcount,htcount,Nat.mul_add,Nat.mul_one]
        omega
      · intro row hm
        rcases List.mem_append.mp hm with hm|hm
        exact hquiet row hm
        exact htquiet row hm

/-- Exact executable array contents for the pure header/hash/ash push loops. -/
theorem push_loop {α β ε : Type} (xs : List α) (a : Array β) (row : α→β) :
    (forIn xs a (fun x st=>Except.ok (ForInStep.yield (st.push (row x)))) : Except ε (Array β))=
      .ok ((a.toList++xs.map row).toArray) := by
  induction xs generalizing a with
  | nil=>simp; rfl
  | cons x xs ih=>
    rw [List.forIn_cons]
    simp only [bind,Except.bind]
    rw [ih]
    simp

end ZkFormal.NearV3.Assembly.CodecDigest
