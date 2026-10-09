import ZkFormal.NearV3.Candidates.ProcModelEntrySuccess
import ZkFormal.NearV3.Candidates.ProcZeroPending
namespace ZkFormal.NearV3.Candidates.ProcPendingCurrent
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen NearSpecV3.Scheduler

def link (reqs : List Req) (v : Nat) : Nat := reqs.toArray[v/64]!.link

def Current (reqs : List Req) (al : Array Nat) (ps : List Push) : Prop :=
  ∀p∈ps,link reqs p.v<al.size ∧ p.key=al[link reqs p.v]!

theorem filter_current (reqs : List Req) (al : Array Nat) (ps : List Push)
    (h : Current reqs al ps) (f : Push → Bool) : Current reqs al (ps.filter f) := by
  intro p hp
  exact h p (List.mem_filter.mp hp).1

theorem sort_current (reqs : List Req) (al : Array Nat) (ps : List Push)
    (h : Current reqs al ps) : Current reqs al (sortTs ps) := by
  intro p hp
  exact h p (ProcZeroPending.sort_mem ps p hp)

theorem update_other (reqs : List Req) (al : Array Nat) (ps : List Push)
    (h : Current reqs al ps) (l x : Nat) (hn : ∀p∈ps,l≠link reqs p.v) :
    Current reqs (al.set! l x) ps := by
  intro p hp
  have hh := h p hp
  exact ⟨by simpa using hh.1,by rw [Array.getElem!_set!_ne _ _ _ _ (hn p hp)]; exact hh.2⟩

theorem append_current (reqs : List Req) (al : Array Nat) (ps : List Push)
    (h : Current reqs al ps) (p : Push) (hp : link reqs p.v<al.size)
    (hk : p.key=al[link reqs p.v]!) : Current reqs al (ps++[p]) := by
  intro q hq
  simp only [List.mem_append,List.mem_singleton] at hq
  rcases hq with hq|rfl
  · exact h q hq
  · exact ⟨hp,hk⟩

theorem initial_current (reqs : List Req) (st : PState)
    (hreq : ∀q∈reqs,q.link<st.al.size) : Current reqs st.al (ProcModelStep.initial reqs st).1 := by
  intro p hp
  simp only [ProcModelStep.initial,List.mem_filterMap] at hp
  rcases hp with ⟨i,hi,hp⟩
  have hil : i<reqs.length := List.mem_range.mp hi
  split at hp
  · cases hp
  · simp only [Option.some.injEq] at hp
    subst p
    have hm : reqs.toArray[i]!∈reqs := by
      rw [List.getElem!_toArray,getElem!_pos reqs i hil]
      exact List.getElem_mem hil
    have hb := hreq _ hm
    simpa [link] using And.intro hb (Eq.refl st.al[reqs.toArray[i]!.link]!)

theorem next_link (reqs : List Req) (v : Nat) (h : v%64+1<64) :
    link reqs (v+1)=link reqs v := by
  unfold link
  congr 2
  omega
end ZkFormal.NearV3.Candidates.ProcPendingCurrent
