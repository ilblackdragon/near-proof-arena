import ZkFormal.NearV3.Rcpt.Candidates.WalkRankTraffic
import ZkFormal.NearV3.Rcpt.Candidates.UpsRequestCoverage

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near

theorem keyEdges3_distinct (n : Nat) (k : List Nat) : (keyEdges3 n k).Nodup := by
  unfold keyEdges3 List.Nodup
  rw [List.pairwise_map]
  exact List.pairwise_lt_range.imp (fun h he=>by simp at he;omega)

theorem keyEdges3_position (n : Nat) (k : List Nat) (e : Msg) (h : e∈keyEdges3 n k) :
    e.getD 1 0<k.length ∧ e.head?=some n := by
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp h
  simpa using List.mem_range.mp hi

theorem edgesOf3_distinct (n : Nat) (s : NodeS3) : (edgesOf3 n s).Nodup := by
  unfold edgesOf3
  cases s.v with
  | leaf k v m =>
    dsimp only
    rw [List.append_assoc]
    apply List.pairwise_append.mpr
    refine ⟨keyEdges3_distinct n k,?_,?_⟩
    · cases v <;> simp [EK_VAL,EK_LEND]
    · intro a ha b hb
      have hp:=(keyEdges3_position n k a ha).1
      have hbpos : b.getD 1 0=k.length := by cases v <;> simp_all <;> grind
      intro he;rw [he,hbpos] at hp;omega
  | ext k c m =>
    apply List.pairwise_append.mpr
    refine ⟨keyEdges3_distinct n k.dropLast,?_,?_⟩
    · cases c <;> cases k.getLast? <;> simp
    · intro a ha b hb
      have hp:=(keyEdges3_position n k.dropLast a ha).1
      have hbpos : b.getD 1 0=k.length-1 := by cases c <;> cases hh : k.getLast? <;> simp_all [hh]
      rw [List.length_dropLast] at hp
      intro he;rw [he,hbpos] at hp;omega
  | branch v cs m =>
    have hz:=Near.Render.BusEdge.zip_range_pairwise cs 0
    rw [←List.range_eq_range'] at hz
    apply List.pairwise_append.mpr
    refine ⟨?_,?_,?_⟩
    · refine (List.Pairwise.filterMap (S:=fun a b=>a.getD 2 0<b.getD 2 0) _ ?_ hz).imp
        (fun h e=>by rw [e] at h;omega)
      intro a a' haa b hb b' hb'
      split at hb
      · split at hb'
        · simp at hb hb';subst hb hb';simpa using haa
        · cases hb'
      · cases hb
    · cases v with
      | none=>simp
      | some v=>cases v <;> simp
    · intro a ha b hb
      obtain ⟨⟨c,j⟩,_,hh⟩:=List.mem_filterMap.mp ha
      have hak : a.getD 5 0=EK_DOWN := by
        cases c <;> simp only [Option.some.injEq,reduceCtorEq] at hh
        subst a;rfl
      have hbk : b.getD 5 0=EK_VAL := by cases v with
        | none=>simp at hb
        | some v=>cases v <;> simp_all
      intro he;rw [he,hbk] at hak;exact (by decide : EK_VAL≠EK_DOWN) hak

theorem edgesOf3_head (n : Nat) (s : NodeS3) (e : Msg) (h : e∈edgesOf3 n s) : e.head?=some n := by
  unfold edgesOf3 at h
  cases hv : s.v with
  | leaf k v m =>
    rw [hv] at h
    dsimp only at h
    simp only [List.mem_append] at h
    rcases h with (h|h)|h
    · exact (keyEdges3_position n k e h).2
    · cases v <;> simp_all
    · simp only [List.mem_singleton] at h;subst e;rfl
  | ext k c m =>
    rw [hv] at h
    dsimp only at h
    simp only [List.mem_append] at h
    rcases h with h|h
    · exact (keyEdges3_position n k.dropLast e h).2
    · cases c <;> cases hh : k.getLast? <;> simp_all
  | branch v cs m =>
    rw [hv] at h
    dsimp only at h
    simp only [List.mem_append] at h
    rcases h with h|h
    · obtain ⟨⟨c,j⟩,_,hh⟩:=List.mem_filterMap.mp h
      cases c <;> simp only [Option.some.injEq,reduceCtorEq] at hh
      subst e;rfl
    · cases v with
      | none=>simp at h
      | some v=>cases v <;> simp_all

theorem nodeEdgeKeys_distinct (ss : List NodeS3) : (nodeEdgeKeys ss).Nodup := by
  unfold nodeEdgeKeys List.Nodup
  rw [List.pairwise_flatMap]
  refine ⟨fun x _=>edgesOf3_distinct x.2 x.1,?_⟩
  have hz:=Near.Render.BusEdge.zip_range_pairwise ss 0
  rw [←List.range_eq_range'] at hz
  refine hz.imp_of_mem (fun {_ _} _ _ hlt a ha b hb he=>?_)
  have h1:=edgesOf3_head _ _ a ha
  have h2:=edgesOf3_head _ _ b hb
  rw [he,h2] at h1
  simp only [Option.some.injEq] at h1
  omega

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
