import ZkFormal.NearV3.Candidates.ProcPendingTime
namespace ZkFormal.NearV3.Candidates.ProcMaxBucket
open ZkFormal.NearV3.Sched NearSpecV3.Scheduler ProcNativePush

theorem insert_last (ps : List Push) (p : Push) (h : ∀q∈ps,q.ts<p.ts) :
    insertTs p ps=ps++[p] := by
  induction ps with
  | nil => rfl
  | cons q qs ih =>
    have hq := h q (by simp)
    simp only [insertTs,show ¬p.ts<q.ts by omega,ite_false,List.cons_append]
    rw [ih (fun q hq=>h q (by simp [hq]))]

theorem sort_id (ps : List Push) (h : ps.Pairwise (fun p q=>p.ts<q.ts)) : sortTs ps=ps := by
  induction ps using snoc_induction with
  | h0 => rfl
  | hs ps p ih =>
    have hh := List.pairwise_append.mp h
    have hi := ih hh.1
    change (ps++[p]).foldl (fun acc p=>insertTs p acc) []=ps++[p]
    rw [List.foldl_append]
    change insertTs p (sortTs ps)=ps++[p]
    rw [hi,insert_last ps p (fun q hq=>hh.2.2 q hq p (by simp))]

def maxKey (ps : List Push) : Nat := ps.foldl (fun m p=>max m p.key) 0

theorem fold_max (ps : List Push) (a : Nat) :
    a≤ps.foldl (fun m p=>max m p.key) a ∧
    (∀p∈ps,p.key≤ps.foldl (fun m p=>max m p.key) a) ∧
    (ps.foldl (fun m p=>max m p.key) a=a ∨
      ∃p∈ps,p.key=ps.foldl (fun m p=>max m p.key) a) := by
  induction ps generalizing a with
  | nil => simp
  | cons p ps ih =>
    have hh := ih (max a p.key)
    refine ⟨Nat.le_trans (Nat.le_max_left _ _) hh.1,?_,?_⟩
    · intro q hq
      rcases List.mem_cons.mp hq with rfl|hq
      · exact Nat.le_trans (Nat.le_max_right _ _) hh.1
      · exact hh.2.1 q hq
    · rcases hh.2.2 with he|⟨q,hq,he⟩
      · by_cases ha : p.key≤a
        · left; simpa [List.foldl_cons,Nat.max_eq_left ha] using he
        · right; exact ⟨p,by simp,by simp only [List.foldl_cons]; omega⟩
      · exact Or.inr ⟨q,List.mem_cons_of_mem p hq,he⟩

theorem max_mem (ps : List Push) (hn : ps≠[]) : ∃p∈ps,p.key=maxKey ps := by
  have hh := fold_max ps 0
  rcases hh.2.2 with hz|hm
  · cases ps with
    | nil => contradiction
    | cons p ps =>
      refine ⟨p,by simp,?_⟩
      have hb := hh.2.1 p (by simp)
      change p.key=(p::ps).foldl (fun m p=>max m p.key) 0
      omega
  · exact hm

/-- Native pop-last chooses exactly the model's maximal-key bucket and leaves
exactly its filtered pending dictionary. Strict timestamps make sortTs the
identity, preserving the native insertion order. -/
theorem native_pop (reqs : List Req) (ps : List Push) (hn : ps≠[])
    (ht : ps.Pairwise (fun p q=>p.ts<q.ts)) :
    (bucketsOf reqs (ps.map toPM)).getLast! =
      (maxKey ps,(sortTs (ps.filter (fun p=>p.key==maxKey ps))).map (fun p=>reqAt reqs p.v)) ∧
    (bucketsOf reqs (ps.map toPM)).dropLast =
      bucketsOf reqs ((ps.filter (fun p=>p.key != maxKey ps)).map toPM) := by
  obtain ⟨p,hp,he⟩ := max_mem ps hn
  have hm : ∃p∈ps.map toPM,p.key=maxKey ps := ⟨toPM p,List.mem_map_of_mem hp,he⟩
  have hb : ∀p∈ps.map toPM,p.key≤maxKey ps := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    exact (fold_max ps 0).2.1 q hq
  have hh := groups_pop reqs (ps.map toPM) (maxKey ps) hm hb
  rw [←bucketsOf_eq_groups,←bucketsOf_eq_groups] at hh
  rw [sort_id _ (ht.filter _)]
  have heq (a b : Nat) : decide (a=b)=(a==b) := Bool.eq_iff_iff.mpr (by simp)
  simpa [heq,grp,List.filter_map,List.map_map,toPM,bne,Function.comp_def] using hh
end ZkFormal.NearV3.Candidates.ProcMaxBucket
