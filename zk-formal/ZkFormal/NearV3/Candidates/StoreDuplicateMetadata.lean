import ZkFormal.NearV3.Candidates.HonestStoreRepresentatives
import ZkFormal.NearV3.Extract.NodeView
namespace ZkFormal.NearV3.Candidates.StoreDuplicateMetadata
open ZkFormal.Near ZkFormal.Algebra NearSpec HonestStoreRepresentatives

/-- Concrete AIR entity IDs attached to native transition-tagged byte classes.
The combined input may contain both node and value occurrences. -/
structure Occurrence where
  key : Key
  eid : Nat

def representativeId (rs : List Occurrence) (key : Key) : Nat :=
  ((rs.find? fun r=>r.key==key).map Occurrence.eid).getD 0

theorem representative_small (rs : List Occurrence) (key : Key)
    (h : ∀r∈rs,r.eid<P) : representativeId rs key<P := by
  unfold representativeId
  cases hf : rs.find? (fun r=>r.key==key) with
  | none => change 0<P; decide
  | some r => exact h r (List.mem_of_find?_eq_some hf)

theorem representative_found (rs : List Occurrence) (key : Key)
    (h : ∃r∈rs,r.key=key) :
    ∃r∈rs,r.key=key ∧ representativeId rs key=r.eid := by
  have hex : ∃r,rs.find? (fun r=>r.key==key)=some r := by
    induction rs with
    | nil => simp at h
    | cons r rs ih =>
      by_cases he : r.key=key
      · exact ⟨r,by simp [he]⟩
      · have ht : ∃s∈rs,s.key=key := by
          obtain ⟨s,hs,hk⟩ := h
          rcases List.mem_cons.mp hs with rfl|hs
          · exact False.elim (he hk)
          · exact ⟨s,hs,hk⟩
        obtain ⟨s,hs⟩ := ih ht
        exact ⟨s,by simp [he,hs]⟩
  obtain ⟨r,hr⟩ := hex
  exact ⟨r,List.mem_of_find?_eq_some hr,by simpa using List.find?_some hr,by simp [representativeId,hr]⟩

def nodeKey (s : NodeS3) : Key := (s.tau,toBytes (s.v.ser false))

def patch (rs : List Occurrence) (n : Nat) (s : NodeS3) : NodeS3 :=
  let rep:=representativeId rs (nodeKey s)
  {s with dup:=!(eidN n==rep),hd:=(eidN n==rep),repE:=rep}

def assign (rs : List Occurrence) : Nat→List NodeS3→List NodeS3
  | _,[] => []
  | n,s::ss => patch rs n s::assign rs (n+1) ss

theorem assign_length (rs : List Occurrence) (n : Nat) (ss : List NodeS3) :
    (assign rs n ss).length=ss.length := by
  induction ss generalizing n with
  | nil => rfl
  | cons s ss ih => simp [assign,ih]

theorem assign_member (rs : List Occurrence) : ∀(ss : List NodeS3)(n : Nat)(s : NodeS3),
    s∈assign rs n ss → ∃i o,o∈ss ∧ s=patch rs i o
  | [],_,_,h => by simp [assign] at h
  | o::ss,n,s,h => by
    simp only [assign,List.mem_cons] at h
    rcases h with rfl|h
    · exact ⟨n,o,by simp,rfl⟩
    · obtain ⟨i,o,ho,he⟩:=assign_member rs ss (n+1) s h
      exact ⟨i,o,by simp [ho],he⟩

theorem assign_get (rs : List Occurrence) : ∀(ss : List NodeS3)(n i : Nat),
    (assign rs n ss)[i]?=ss[i]?.map (patch rs (n+i))
  | [],_,_ => by simp [assign]
  | s::ss,n,0 => by simp [assign]
  | s::ss,n,i+1 => by
    simpa [assign,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using assign_get rs ss (n+1) i

theorem assign_bytes (rs : List Occurrence) (ss : List NodeS3) (n : Nat) :
    (assign rs n ss).map (fun s=>(s.v.ser false).length)=ss.map (fun s=>(s.v.ser false).length) := by
  induction ss generalizing n with
  | nil => rfl
  | cons s ss ih => simp [assign,patch,ih]

/-- Duplicate/head/representative updates preserve the same complete local
forest view. Semantic duplicate ownership requires actual occurrence coverage. -/
theorem assign_wf (rs : List Occurrence) (ss : List NodeS3) (h : NodeWf3 ss)
    (hid : ∀r∈rs,r.eid<P) : NodeWf3 (assign rs 0 ss) := by
  have hg : ∀i (hi : i<(assign rs 0 ss).length),
      ∃(ho : i<ss.length),(assign rs 0 ss)[i]=patch rs i ss[i] := by
    intro i hi
    have ho : i<ss.length := by simpa [assign_length] using hi
    refine ⟨ho,?_⟩
    have hh:=assign_get rs ss 0 i
    simpa [List.getElem?_eq_getElem hi,List.getElem?_eq_getElem ho] using hh
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro s hs;obtain ⟨i,o,ho,rfl⟩:=assign_member rs ss 0 s hs;exact h.wf o ho
  · intro s hs;obtain ⟨i,o,ho,rfl⟩:=assign_member rs ss 0 s hs;exact h.depth o ho
  · intro i hi;obtain ⟨ho,hget⟩:=hg i hi;rw [hget];exact h.res i ho
  · intro i hi;obtain ⟨ho,hget⟩:=hg i hi;rw [hget];exact h.uses i ho
  · intro s hs;obtain ⟨i,o,ho,rfl⟩:=assign_member rs ss 0 s hs
    have hh:=h.small o ho
    exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,representative_small rs _ hid,hh.2.2.2.2.2⟩
  · intro s hs;obtain ⟨i,o,ho,rfl⟩:=assign_member rs ss 0 s hs;exact h.canon o ho
  · simpa [assign_length] using h.count
  · simpa [assign_bytes] using h.rows
  · intro s hs;obtain ⟨i,o,ho,rfl⟩:=assign_member rs ss 0 s hs;exact h.upbLen o ho
  · intro s hs;obtain ⟨i,o,ho,rfl⟩:=assign_member rs ss 0 s hs;exact h.upbSmall o ho
  · intro s hs;obtain ⟨i,o,ho,rfl⟩:=assign_member rs ss 0 s hs;exact h.kidCid o ho
end ZkFormal.NearV3.Candidates.StoreDuplicateMetadata
