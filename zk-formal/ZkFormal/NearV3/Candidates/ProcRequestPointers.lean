import ZkFormal.NearV3.Candidates.ProcPushEntries
namespace ZkFormal.NearV3.Candidates.ProcRequestPointers
open ZkFormal.NearV3.Sched NearSpecV3.Scheduler

def Valid (reqs : List Req) (v : Nat) : Prop :=
  v/64<reqs.length ∧ v%64<reqs.toArray[v/64]!.incs.length

def Small (reqs : List Req) : Prop := ∀q∈reqs,q.incs.length≤64

theorem next_valid (reqs : List Req) (v : Nat) (hs : Small reqs)
    (hv : Valid reqs v) (hn : (v%64+1==reqs.toArray[v/64]!.incs.length)=false) :
    Valid reqs (v+1) := by
  have hm : reqs.toArray[v/64]!∈reqs := by
    rw [getElem!_pos reqs.toArray (v/64) (by simpa using hv.1)]
    exact List.mem_iff_getElem.mpr ⟨v/64,hv.1,by simp⟩
  have hb := hs _ hm
  have hne : v%64+1≠reqs.toArray[v/64]!.incs.length := by simpa using hn
  have hl : v%64+1<64 := by have := hv.2; omega
  have hd : (v+1)/64=v/64 := by omega
  have hr : (v+1)%64=v%64+1 := by omega
  simp only [Valid,hd,hr]
  exact ⟨hv.1,by have := hv.2; omega⟩

theorem initial_valid (reqs : List Req) (st : PState) :
    ∀p∈(ProcModelStep.initial reqs st).1,Valid reqs p.v := by
  intro p hp
  simp only [ProcModelStep.initial,List.mem_filterMap] at hp
  obtain ⟨i,hi,hp⟩ := hp
  have hi' : i<reqs.length := List.mem_range.mp hi
  split at hp
  · contradiction
  · cases hp
    simp only [Valid,Nat.mul_div_cancel _ (by decide : 0<64),Nat.mul_mod_left]
    refine ⟨hi',?_⟩
    rename_i hne
    have hh : reqs.toArray[i]!.incs≠[] := by simpa using hne
    exact List.length_pos_iff.mpr hh

/-- A successful model entry only emits a next pointer within the same request. -/
theorem event_push_valid (reqs : List Req) (n : Nat) (allowed : Array Bool)
    (K z v t : Nat) (st : PState) (hs : Small reqs) (hv : Valid reqs v) :
    ∀p∈ProcPushEntries.pushOf K z (ProcEntryEvent.event n allowed reqs.toArray[v/64]! v t st),
      Valid reqs p.v := by
  intro p hp
  unfold ProcPushEntries.pushOf at hp
  split at hp
  · rename_i h
    simp only [List.mem_singleton] at hp
    subst p
    apply next_valid reqs v hs hv
    simp only [Bool.and_eq_true,Bool.not_eq_true',ProcEntryEvent.event] at h
    exact h.2
  · simp at hp
end ZkFormal.NearV3.Candidates.ProcRequestPointers
