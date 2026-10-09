import ZkFormal.NearV3.Candidates.MerkleRender.NativeTrace

namespace ZkFormal.NearV3.Candidates.MerkleRender
open ZkFormal.Near.Render ZkFormal.Near ZkFormal.Air ZkFormal.Algebra
open MrkTraffic MrkGen

def generatedView (n : Nat) (lv : List (List MNode)) : MrkV :=
  ⟨n,topJ n,((lv.getD (topJ n) []).getD 0 default).id,
    ((lv.getD (topJ n) []).getD 0 default).len,(mrkShape n).map (gNode lv)⟩

set_option maxHeartbeats 1000000 in
/-- Exact traffic of the generalized physical renderer, retaining every bus.
The digest-length premise is discharged by the concrete native level builder. -/
theorem traffic19 (n : Nat) (lv : List (List MNode)) (pub : List Fp)
    (hn1 : 1≤n) (hn : n≤4481)
    (hdig : ∀ x∈mrkShape n, (ch lv x.1 (2*x.2.1)).dig.length=32 ∧
      (x.2.2=true → (ch lv x.1 (2*x.2.1+1)).dig.length=32)) :
    TableTraffic Mrk.interactions (trace n lv) T_MRK pub (mrkTraffic pub (generatedView n lv)) := by
  unfold generatedView
  have hH : (trace n lv).height T_MRK=2^19 := rfl
  have hlen := rows_fit hn
  obtain ⟨_,rok,_,_⟩ := recs_facts n hn1
  have hcell' : ∀ q col, q<2^19 → col<58 →
      (trace n lv).cell T_MRK q col=Fp.ofNat (cell n lv (recs n) q col) := by
    intros; rfl
  have hrows : ∀ b s, ((List.range ((trace n lv).height T_MRK)).flatMap fun q =>
      rowTraffic Mrk.interactions (trace n lv) T_MRK q pub b s) =
      rowRoot n lv pub b s ++ (mrkShape n).flatMap (fun x => (expand x).flatMap (fun r => rowM n lv r b s)) := by
    intro b s
    rw [hH, range_split (show (recs n).length + 1 ≤ _ by omega), List.flatMap_append,
      flatMap_nil' (l := List.map _ _) (fun q hq => by
        obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
        have := List.mem_range.1 hq'
        exact row_pad hcell' (by omega) (by omega) (by omega) b s),
      List.append_nil, List.range_succ_eq_map, List.flatMap_cons, row_root hcell' (by omega), List.flatMap_map]
    congr 1
    rw [ZkFormal.Near.Render.flatMap_congr' (g := fun k => rowM n lv ((recs n).getD k default) b s) (fun k hk => by
        have hk' := List.mem_range.1 hk
        refine row_node hcell' (by omega) (by omega) (by simpa using hk') (fun j i p hr => ?_) b s
        have hm : (recs n).getD (k + 1 - 1) default ∈ recs n := by
          simp only [Nat.add_sub_cancel, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk', Option.getD_some]
          exact List.getElem_mem _
        have := (rok _ hm).2.2.2.2.1
        rw [hr] at this; exact this rfl),
      show ((List.range (recs n).length).flatMap fun k => rowM n lv ((recs n).getD k default) b s) =
        (recs n).flatMap (fun r => rowM n lv r b s) from
        (flatMap_getD (default : Rec) (recs n) (fun r => rowM n lv r b s)).symm,
      recs_eq, List.flatMap_assoc]
  have hqs : ((mrkShape n).map (gNode lv)).zip (List.range ((mrkShape n).map (gNode lv)).length) =
      (List.range (mrkShape n).length).map fun k => (gNode lv ((mrkShape n).getD k default), k) := by
    rw [zip_range_getD (default : MrkNode), List.length_map]
    apply List.map_congr_left; intro k hk
    have hk' := List.mem_range.1 hk
    simp [List.getD_eq_getElem?_getD, hk']
  have hmem : ∀ k, k < (mrkShape n).length → (mrkShape n).getD k default ∈ mrkShape n := by
    intro k hk
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]; exact List.getElem_mem _
  have hgetD : ∀ k (hk : k < (mrkShape n).length), (mrkShape n).getD k default = (mrkShape n)[k] := by
    intro k hk; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  apply traffic_of
  · intro b
    rw [hrows, flatMap_getD default (mrkShape n)]
    apply List.Perm.of_eq
    dsimp only [mrkTraffic, mrkSends]
    rw [hqs]
    by_cases h0 : b = B_BYTES
    · subst h0
      simp only [if_true, rowRoot, show ¬ (B_BYTES = B_DIGEST ∧ true = false) by decide,
        show ¬ (B_BYTES = B_MPOS ∧ true = false) by decide, if_false, List.nil_append, List.flatMap_map,
        List.map_flatMap]
      apply ZkFormal.Near.Render.flatMap_congr'; intro k hk
      have hk' := List.mem_range.1 hk
      obtain ⟨d1, d2⟩ := hdig _ (hmem k hk')
      rcases hx : (mrkShape n).getD k default with ⟨j, i, h⟩
      rw [hx] at d1 d2
      cases h with
      | true =>
        rw [node_bytes n lv j i d1 (d2 rfl)]
        simp only [gNode, if_true]
        rw [hashedBefore_eq hn1 lv hk' (by rw [← hgetD k hk', hx]), ← hgetD k hk', hx]
      | false => rw [node_bytesP]; rfl
    · by_cases h9 : b = B_MPOS
      · subst h9
        simp only [show B_MPOS ≠ B_BYTES by decide, if_false, if_true, rowRoot,
          show ¬ (B_MPOS = B_DIGEST ∧ true = false) by decide, show ¬ (B_MPOS = B_MPOS ∧ true = false) by decide,
          List.nil_append, List.map_map]
        rw [← flatMap_single (f := fun k => [_]) (fun _ _ => rfl)]
        apply ZkFormal.Near.Render.flatMap_congr'; intro k hk
        have hk' := List.mem_range.1 hk
        rcases hx : (mrkShape n).getD k default with ⟨j, i, h⟩
        have hx' : (mrkShape n).getD k (0, 0, false) = (j, i, h) := hx
        rw [node_mposS]
        simp only [Function.comp_apply, mrkPos, hx']
        cases h with
        | true =>
          simp only [gNode, if_true]
          rw [hashedBefore_eq hn1 lv hk' (by rw [← hgetD k hk', hx]), ← hgetD k hk', hx]
          rfl
        | false => rw [hx]; rfl
      · rw [flatMap_nil' (fun k _ => flatMap_nil' (fun r _ => rowM_otherS n lv r b h0 h9))]
        simp [rowRoot, h0, h9]
  · intro b
    rw [hrows, flatMap_getD default (mrkShape n)]
    apply List.Perm.of_eq
    dsimp only [mrkTraffic, mrkRecvs]
    rw [hqs]
    by_cases h1 : b = B_DIGEST
    · subst h1
      simp only [if_true, rowRoot, and_self, show ¬ (B_DIGEST = B_MPOS) by decide, false_and, if_false,
        List.append_nil, List.flatMap_map, List.map_cons, List.map_flatMap, List.cons_append, List.nil_append]
      rw [List.cons.injEq]
      refine ⟨?_, ?_⟩
      · simp only [Msg.toFp, digMsg, List.map_append, List.map_cons, List.map_nil, List.map_map, List.cons_append,
          List.nil_append, List.cons.injEq, true_and]
        apply List.map_congr_left; intro x _
        simp only [Function.comp_apply, pubNat, Fp.ofNat_toNat]
      · apply ZkFormal.Near.Render.flatMap_congr'; intro k hk
        have hk' := List.mem_range.1 hk
        obtain ⟨d1, d2⟩ := hdig _ (hmem k hk')
        rcases hx : (mrkShape n).getD k default with ⟨j, i, h⟩
        rw [hx] at d1 d2
        rw [node_digest n lv j i h d1 d2]
        cases h <;> rfl
    · by_cases h9 : b = B_MPOS
      · subst h9
        simp only [show B_MPOS ≠ B_DIGEST by decide, if_false, if_true, rowRoot, false_and, and_self,
          List.nil_append, List.flatMap_map, List.map_cons, List.map_flatMap, List.cons_append]
        rw [List.cons.injEq]
        refine ⟨rfl, ?_⟩
        apply ZkFormal.Near.Render.flatMap_congr'; intro k hk
        rcases hx : (mrkShape n).getD k default with ⟨j, i, h⟩
        have hx' : (mrkShape n).getD k (0, 0, false) = (j, i, h) := hx
        rw [node_mposR]
        simp only [mrkPos, hx', gNode]
        cases h <;> rfl
      · rw [flatMap_nil' (fun k _ => flatMap_nil' (fun r _ => rowM_otherR n lv r b h1 h9))]
        simp [rowRoot, h1, h9]

end ZkFormal.NearV3.Candidates.MerkleRender
