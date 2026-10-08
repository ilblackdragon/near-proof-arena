import ZkFormal.NearV3.Candidates.MerkleRender.Digest

namespace ZkFormal.NearV3.Candidates.MerkleRender
open ZkFormal.Near.Render ZkFormal.Near ZkFormal.Air ZkFormal.Algebra
open MrkTraffic MrkGen BusMpos ZkFormal.NearV3.Rcpt.Candidates

/-- Leaf position messages use the actual preimage lengths. -/
def leafPositions (leaves : List (List Nat)) : List ZkFormal.Near.Msg :=
  ((List.range leaves.length).map (fun i => (0,i))).map (msgOf (levelTable leaves))

/-- The concrete Merkle table consumes exactly its own parent positions plus
all leaf positions. This includes promoted nodes without extra leaf claims. -/
theorem view_positions (leaves : List (List Nat)) (pub : List Fp) (hn : 1≤leaves.length) :
    (leafPositions leaves++mrkSends pub (generatedView leaves.length (levelTable leaves)) B_MPOS).Perm
      (mrkRecvs pub (generatedView leaves.length (levelTable leaves)) B_MPOS) := by
  have hqs : ((mrkShape leaves.length).map (gNode (levelTable leaves))).zip
      (List.range ((mrkShape leaves.length).map (gNode (levelTable leaves))).length) =
      (List.range (mrkShape leaves.length).length).map
        fun k => (gNode (levelTable leaves) ((mrkShape leaves.length).getD k default), k) := by
    rw [zip_range_getD (default : MrkNode), List.length_map]
    apply List.map_congr_left; intro k hk
    have hk' := List.mem_range.1 hk
    simp [List.getD_eq_getElem?_getD, hk']
  have hgetD : ∀ k (hk : k < (mrkShape leaves.length).length),
      (mrkShape leaves.length).getD k default = (mrkShape leaves.length)[k] := by
    intro k hk; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  have hS2 : mrkSends pub ⟨leaves.length, topJ leaves.length,
        (((levelTable leaves).getD (topJ leaves.length) []).getD 0 default).id,
        (((levelTable leaves).getD (topJ leaves.length) []).getD 0 default).len,
        (mrkShape leaves.length).map (gNode (levelTable leaves))⟩ 9 =
      ((mrkShape leaves.length).map fun x => (x.1, x.2.1)).map (msgOf (levelTable leaves)) := by
    simp only [mrkSends, B_BYTES, B_MPOS, Nat.reduceEqDiff, ite_false, ite_true]
    rw [hqs]
    apply List.ext_getElem (by simp)
    intro k h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range]
    have hx := shape_rec hn (List.getElem_mem h1)
    rcases hxk : (mrkShape leaves.length)[k] with ⟨j, i, h⟩
    rw [hxk] at hx
    obtain ⟨hj1, hjn, hi, hh, _⟩ := hx
    simp only at hj1 hjn hi hh
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hg' : (mrkShape leaves.length).getD k default = (j' + 1, i, h) := by rw [hgetD k h1, hxk]
    have hg'' : (mrkShape leaves.length).getD k (0, 0, false) = (j' + 1, i, h) := hg'
    simp only [hg', mrkPos, hg'', msgOf, levelTable_get leaves (j' + 1) (by omega), succ_get leaves j' i hi]
    cases h with
    | true =>
      simp at hh
      simp only [gNode, ite_true, hh]
      rw [hashedBefore_eq hn (levelTable leaves) h1 (by rw [hxk]), hxk]
    | false =>
      simp at hh
      simp only [gNode, Bool.false_eq_true, ite_false, show ¬ (2 * i + 1 < size leaves.length j') by omega, ch,
        Nat.add_sub_cancel, levelTable_get leaves j' (by omega)]
  have hR : mrkRecvs pub ⟨leaves.length, topJ leaves.length,
        (((levelTable leaves).getD (topJ leaves.length) []).getD 0 default).id,
        (((levelTable leaves).getD (topJ leaves.length) []).getD 0 default).len,
        (mrkShape leaves.length).map (gNode (levelTable leaves))⟩ 9 =
      ((topJ leaves.length, 0) :: (mrkShape leaves.length).flatMap childPos).map (msgOf (levelTable leaves)) := by
    simp only [mrkRecvs, B_DIGEST, B_MPOS, Nat.reduceEqDiff, ite_false, ite_true, List.map_cons]
    rw [List.cons.injEq]
    refine ⟨rfl, ?_⟩
    rw [hqs, List.flatMap_map, List.map_flatMap, flatMap_getD default (mrkShape leaves.length)]
    apply ZkFormal.Near.Render.flatMap_congr'; intro k hk
    have hk' := List.mem_range.1 hk
    rcases hxk : (mrkShape leaves.length).getD k default with ⟨j, i, h⟩
    have hxk' : (mrkShape leaves.length).getD k (0, 0, false) = (j, i, h) := hxk
    simp only [mrkPos, hxk']
    cases h <;> rfl
  change (leafPositions leaves++mrkSends pub ⟨leaves.length,topJ leaves.length,
    (((levelTable leaves).getD (topJ leaves.length) []).getD 0 default).id,
    (((levelTable leaves).getD (topJ leaves.length) []).getD 0 default).len,
    (mrkShape leaves.length).map (gNode (levelTable leaves))⟩ B_MPOS).Perm _
  simp only [B_MPOS,generatedView]
  rw [hS2,hR]
  simp only [leafPositions,←List.map_append]
  have hrot : (mrkShape leaves.length).flatMap childPos++[(topJ leaves.length,0)]=
      (List.range leaves.length).map (fun i => (0,i))++
        (mrkShape leaves.length).map (fun x => (x.1,x.2.1)) :=
    rot leaves.length (leaves.length+1) 0 hn (by simp [size])
  rw [←hrot]
  exact (List.perm_append_singleton _ _).map (msgOf (levelTable leaves))

/-- Explicit leaf messages for the receipt-to-Merkle boundary. -/
theorem leaf_positions (leaves : List (List Nat)) :
    leafPositions leaves=leaves.zipIdx.map (fun (b,i) => [0,i,msgId K_LEAF i,b.length]) := by
  simp only [leafPositions,List.map_map]
  rw [List.zipIdx_eq_zip_range',←List.range_eq_range',zip_range_getD ([] : List Nat)]
  simp only [List.map_map]
  apply List.map_congr_left
  intro i hi
  have hil := List.mem_range.mp hi
  simp only [Function.comp_apply,msgOf]
  rw [levelTable_get leaves 0 (by omega)]
  simp [levelsFromLeaves,List.getD_eq_getElem?_getD,hil]

/-- Exact physical MPOS balance, including the empty native outcome list.
The remaining receipt-table obligation is to emit these concrete leaf messages. -/
theorem outcome_positions (os : List NearSpec.Outcome) (pub : List Fp)
    (hn : os.length≤4481) (m : List Fp) :
    ((leafPositions (outcomePreimages os)).map Msg.toFp).count m+
      tableBusCount MerkleEmpty.table.interactions (outcomeTrace os pub) T_MRK pub B_MPOS true m=
      tableBusCount MerkleEmpty.table.interactions (outcomeTrace os pub) T_MRK pub B_MPOS false m := by
  by_cases he : os=[]
  · subst os
    simp [outcomeTrace,honestTrace,tableBusCount_eq,MerkleEmpty.empty_traffic,
      leafPositions,outcomePreimages]
  · have hp : 1≤os.length := by cases os <;> simp_all
    have hl : (outcomePreimages os).length=os.length := by simp [outcomePreimages]
    have hv := view_positions (outcomePreimages os) (MerklePublic.aliasPublic pub) (by rwa [hl])
    rw [hl] at hv
    have ht := (outcome_nonempty_traffic os pub hp hn) B_MPOS m
    rw [ht.1,ht.2]
    have hc := (hv.map Msg.toFp).count_eq m
    simpa only [mrkTraffic,List.map_append,List.count_append] using hc

end ZkFormal.NearV3.Candidates.MerkleRender
