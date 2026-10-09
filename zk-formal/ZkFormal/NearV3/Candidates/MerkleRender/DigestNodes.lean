import ZkFormal.NearV3.Candidates.MerkleRender.Bytes
import ZkFormal.Near.Render.Proof.DigMrk2

namespace ZkFormal.NearV3.Candidates.MerkleRender
open ZkFormal.Near.Render ZkFormal.Near ZkFormal.Air ZkFormal.Algebra
open MrkTraffic MrkGen BusDigest BusMpos ZkFormal.NearV3.Rcpt.Candidates

/-- Whole leaf jobs retain each actual preimage and its actual length. -/
def leafShaJobs (leaves : List (List Nat)) : List ZkFormal.Near.Render.Msg :=
  leaves.zipIdx.map (fun (b,r) => ⟨msgId K_LEAF r,b⟩)

/-- Promotion reuses the child's digest request, rather than creating a hash job. -/
theorem concrete_promoted (leaves : List (List Nat)) (hn : 1≤leaves.length)
    {x : Nat×Nat×Bool} (hx : x∈mrkShape leaves.length) (hh : x.2.2=false) :
    (pk x).map (dm (levelTable leaves))=(pp x).map (dm (levelTable leaves)) := by
  obtain ⟨hj1,hjn,hi,hd,_⟩ := shape_rec hn hx
  obtain ⟨j,i,h⟩ := x
  simp only at hh hj1 hjn hi hd
  subst hh
  obtain ⟨j',rfl⟩ : ∃j',j=j'+1 := ⟨j-1,by omega⟩
  simp only [pk,pp,childPos,Bool.false_eq_true,↓reduceIte,List.map_cons,List.map_nil,dm,
    Nat.add_sub_cancel]
  rw [levelTable_get leaves (j'+1) (by omega),levelTable_get leaves j' (by omega),
    succ_get leaves j' i hi,ite_eq_right_of_eq_false _ _ (by simp at hd; simp; omega)]

/-- Every hashed parent requests exactly the digest of its two concrete children. -/
theorem concrete_hashed (leaves : List (List Nat)) (hn : 1≤leaves.length)
    {x : Nat×Nat×Bool} (hx : x∈mrkShape leaves.length) :
    (hp x).map (dm (levelTable leaves))=
      (if x.2.2 then [digestMsg ⟨msgId K_MRK (qBase leaves.length x.1+x.2.1),
        (((levelTable leaves).getD (x.1-1) []).getD (2*x.2.1) default).dig++
        (((levelTable leaves).getD (x.1-1) []).getD (2*x.2.1+1) default).dig⟩] else []) := by
  obtain ⟨hj1,hjn,hi,hd,_⟩ := shape_rec hn hx
  obtain ⟨j,i,h⟩ := x
  simp only at hj1 hjn hi hd ⊢
  cases h with
  | false => rfl
  | true =>
    obtain ⟨j',rfl⟩ : ∃j',j=j'+1 := ⟨j-1,by omega⟩
    have h2 : 2*i+1<size leaves.length j' := by simpa using hd.symm
    simp only [hp,↓reduceIte,List.map_cons,List.map_nil,dm,Nat.add_sub_cancel,digestMsg,digMsg]
    rw [levelTable_get leaves (j'+1) (by omega),levelTable_get leaves j' (by omega),
      succ_get leaves j' i hi]
    simp only [h2,↓reduceIte]
    have hlen : ∀k,k<size leaves.length j' →
        ((levelsFromLeaves leaves j').getD k default).dig.length=32 := by
      intro k hk
      have hkl : k<(levelsFromLeaves leaves j').length := by rwa [levelsFromLeaves_length]
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hkl]
      exact levelsFromLeaves_digest leaves j' _ (List.getElem_mem _)
    simp only [List.length_append,hlen _ (by omega : 2*i<size leaves.length j'),hlen _ h2]

/-- Leaf requests refer to the actual jobs, without a fixed-size leaf assumption. -/
theorem concrete_leaves (leaves : List (List Nat)) :
    ((List.range leaves.length).map (fun i => (0,i))).map (dm (levelTable leaves))=
      (leafShaJobs leaves).map digestMsg := by
  rw [List.map_map]
  simp only [leafShaJobs,List.map_map]
  rw [List.zipIdx_eq_zip_range',←List.range_eq_range']
  rw [zip_range_getD ([] : List Nat)]
  simp only [List.map_map]
  apply List.map_congr_left
  intro i hi
  have hil := List.mem_range.mp hi
  simp only [Function.comp_apply,dm,digestMsg,digMsg]
  rw [levelTable_get leaves 0 (by omega)]
  simp [levelsFromLeaves,List.getD_eq_getElem?_getD,List.getElem?_map,
    List.getElem?_zipIdx,hil]

end ZkFormal.NearV3.Candidates.MerkleRender
