import ZkFormal.NearV3.Rcpt.Candidates.NodeUsage

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near ZkFormal.Algebra

def assignList (q : UseRequests) : Nat→List NodeS3→List NodeS3
  | _,[] => []
  | n,s::ss => assignUses q n s::assignList q (n+1) ss

theorem assignList_length (q : UseRequests) (n : Nat) (ss : List NodeS3) :
    (assignList q n ss).length=ss.length := by
  induction ss generalizing n with
  | nil => rfl
  | cons s ss ih => simp [assignList,ih]

theorem assignList_member (q : UseRequests) : ∀(ss : List NodeS3)(n : Nat)(s : NodeS3),
    s∈assignList q n ss → ∃i o,o∈ss ∧ s=assignUses q i o
  | [],_,_,h => by simp [assignList] at h
  | o::ss,n,s,h => by
    simp only [assignList,List.mem_cons] at h
    rcases h with rfl|h
    · exact ⟨n,o,by simp,rfl⟩
    · obtain ⟨i,o,ho,he⟩:=assignList_member q ss (n+1) s h
      exact ⟨i,o,by simp [ho],he⟩

theorem assignList_get (q : UseRequests) : ∀(ss : List NodeS3)(n i : Nat),
    (assignList q n ss)[i]?=ss[i]?.map (assignUses q (n+i))
  | [],_,_ => by simp [assignList]
  | s::ss,n,0 => by simp [assignList]
  | s::ss,n,i+1 => by
    simpa [assignList,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using assignList_get q ss (n+1) i

theorem assignList_bytes (q : UseRequests) (ss : List NodeS3) (n : Nat) :
    (assignList q n ss).map (fun s=>(s.v.ser false).length)=ss.map (fun s=>(s.v.ser false).length) := by
  induction ss generalizing n with
  | nil => rfl
  | cons s ss ih => simp [assignList,assignUses,ih]

theorem assignList_wf (q : UseRequests) (ss : List NodeS3) (h : NodeWf3 ss)
    (he : q.edges.length<P) (hb : q.bmaps.length<P) (hw : q.windows.length<P) :
    NodeWf3 (assignList q 0 ss) := by
  have hg : ∀i (hi : i<(assignList q 0 ss).length),
      ∃(ho : i<ss.length),(assignList q 0 ss)[i]=assignUses q i ss[i] := by
    intro i hi
    have ho : i<ss.length := by simpa [assignList_length] using hi
    refine ⟨ho,?_⟩
    have hh:=assignList_get q ss 0 i
    simpa [List.getElem?_eq_getElem hi,List.getElem?_eq_getElem ho] using hh
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro s hs;obtain ⟨i,o,ho,rfl⟩:=assignList_member q ss 0 s hs;exact h.wf o ho
  · intro s hs;obtain ⟨i,o,ho,rfl⟩:=assignList_member q ss 0 s hs;exact h.depth o ho
  · intro i hi;obtain ⟨ho,hget⟩:=hg i hi;rw [hget];exact h.res i ho
  · intro i hi;obtain ⟨ho,hget⟩:=hg i hi;rw [hget];exact (assignUses_arrays q i ss[i]).1
  · intro s hs;obtain ⟨i,o,ho,rfl⟩:=assignList_member q ss 0 s hs
    have hh:=h.small o ho
    have hu:=assignUses_small q i o he hb hw
    exact ⟨hh.1,hh.2.1,hh.2.2.1,hu.2.1,hh.2.2.2.2.1,hu.1⟩
  · intro s hs;obtain ⟨i,o,ho,rfl⟩:=assignList_member q ss 0 s hs;exact h.canon o ho
  · simpa [assignList_length] using h.count
  · simpa [assignList_bytes] using h.rows
  · intro s hs;obtain ⟨i,o,ho,rfl⟩:=assignList_member q ss 0 s hs
    exact ⟨(h.upbLen o ho).1,(assignUses_arrays q i o).2⟩
  · intro s hs;obtain ⟨i,o,ho,rfl⟩:=assignList_member q ss 0 s hs
    exact ⟨(h.upbSmall o ho).1,(assignUses_small q i o he hb hw).2.2⟩
  · intro s hs;obtain ⟨i,o,ho,rfl⟩:=assignList_member q ss 0 s hs;exact h.kidCid o ho

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
