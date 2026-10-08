import ZkFormal.NearV3.Candidates.ProcActualRun
import ZkFormal.NearV3.Candidates.ProcActualModelValid
namespace ZkFormal.NearV3.Candidates.ProcActualZeroPending
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

def nextZero (last : Option (Nat×Nat)) : Nat :=
  match last with | none=>1 | some (K,z)=>if K=0 then z+1 else 1

def Pending (z : Nat) (ps : List Push) : Prop := ∀p∈ps,p.key=0 → p.z=z

theorem insert_mem (p r : Push) (ps : List Push) (h : r∈insertTs p ps) : r=p ∨ r∈ps := by
  induction ps with
  | nil => simpa [insertTs] using h
  | cons q qs ih =>
    simp only [insertTs] at h
    split at h
    · simpa using h
    · simp only [List.mem_cons] at h
      rcases h with rfl|h
      · exact Or.inr (by simp)
      · rcases ih h with h|h
        · exact Or.inl h
        · exact Or.inr (by simp [h])

theorem sort_fold_mem (ps acc : List Push) (r : Push)
    (h : r∈ps.foldl (fun acc p=>insertTs p acc) acc) : r∈acc ∨ r∈ps := by
  induction ps generalizing acc with
  | nil => simpa using h
  | cons p ps ih =>
    have hh := ih (insertTs p acc) h
    rcases hh with hh|hh
    · rcases insert_mem p r acc hh with rfl|hh
      · exact Or.inr (by simp)
      · exact Or.inl hh
    · exact Or.inr (by simp [hh])

theorem sort_mem (ps : List Push) (p : Push) (h : p∈sortTs ps) : p∈ps := by
  have hh := sort_fold_mem ps [] p h
  simpa using hh

theorem seed_le_fold (ps : List Push) (seed : Nat) :
    seed≤ps.foldl (fun m p=>Nat.max m p.key) seed := by
  induction ps generalizing seed with
  | nil => exact Nat.le_refl _
  | cons p ps ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

theorem member_le_fold (ps : List Push) (seed : Nat) (p : Push) (hp : p∈ps) :
    p.key≤ps.foldl (fun m p=>Nat.max m p.key) seed := by
  induction ps generalizing seed with
  | nil => simp at hp
  | cons q qs ih =>
    simp only [List.mem_cons] at hp
    rcases hp with rfl|hp
    · exact Nat.le_trans (Nat.le_max_right _ _) (seed_le_fold _ _)
    · exact ih _ hp

theorem zero_filter (ps : List Push) (hz : ps.foldl (fun m p=>Nat.max m p.key) 0=0) :
    ps.filter (fun p=>p.key != 0)=[] := by
  apply List.filter_eq_nil_iff.mpr
  intro p hp
  have hh := member_le_fold ps 0 p hp
  rw [hz] at hh
  have hk : p.key=0 := by omega
  simp [hk]

/-- A successful zero round reads its exact ordinal from an existing pending
push. The default head cannot justify it because its ordinal is zero. -/
theorem zero_head (ps : List Push) (z : Nat) (hp : Pending z ps)
    (hn : 0<((sortTs (ps.filter (fun p=>p.key==0))).headD default).z) :
    ((sortTs (ps.filter (fun p=>p.key==0))).headD default).z=z := by
  cases hs : sortTs (ps.filter (fun p=>p.key==0)) with
  | nil =>
    rw [hs] at hn
    change 0<0 at hn
    omega
  | cons p tail =>
    have hm := sort_mem (ps.filter (fun p=>p.key==0)) p (by rw [hs]; simp)
    simp only [List.mem_filter,beq_iff_eq] at hm
    simpa [hs] using hp p hm.1 hm.2

theorem initial (reqs : List NearSpecV3.Scheduler.Req) (st : PState) :
    Pending 1 (ProcActualModelStep.initial reqs st).1 := by
  intro p hp hz
  simp only [ProcActualModelStep.initial,List.mem_filterMap] at hp
  rcases hp with ⟨i,hi,he⟩
  split at he
  · cases he
  · have hh := Option.some.inj he
    subst p
    change st.al[reqs.toArray[i]!.link]! = 0 at hz
    change (if st.al[reqs.toArray[i]!.link]! = 0 then 1 else 0)=1
    rw [if_pos hz]
end ZkFormal.NearV3.Candidates.ProcActualZeroPending
