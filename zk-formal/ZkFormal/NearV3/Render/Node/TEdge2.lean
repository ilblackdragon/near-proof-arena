import ZkFormal.NearV3.Render.Node.TEdge

/-!
# ZkFormal.NearV3.Render.Node.TEdge2 — EDGE: the pairs of a record are its enumerated edges
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Dsl
open ZkFormal.Near.Render.NodeGen (F Win layout bitOf b2n)

namespace NodeGen3

/-- Pairs of a record, field by field. -/
def recPairs (vs : List NodeS3) (n : Nat) : List (List Nat × Nat) :=
  (fieldsOf (rec vs n).v).flatMap fun f => (List.range (f.len (hplenOf (rec vs n).v))).flatMap fun i => gE vs n (f, i)

theorem range0' {β : Type} (G : Nat → List β) (L : Nat) (hL : 1 ≤ L) (h0 : ∀ i, i ≠ 0 → G i = []) :
    (List.range L).flatMap G = G 0 := range0 G L h0 (.inl hL)

theorem rangeNil {β : Type} (G : Nat → List β) (L : Nat) (h : ∀ i, G i = []) : (List.range L).flatMap G = [] :=
  ZkFormal.Near.Render.flatMap_nil' (fun i _ => h i)

theorem key_pairs (vs : List NodeS3) (n : Nat) (hw : (rec vs n).v.wf) (hle : isLE (rec vs n).v = true) :
    (List.range ((keyOf (rec vs n).v).length / 2)).flatMap (fun m => gE vs n (.key, m)) =
      (List.range ((keyOf (rec vs n).v).length / 2)).flatMap (fun m =>
        [keyP n (rec vs n).v (2 * m + (keyOf (rec vs n).v).length % 2),
         keyP n (rec vs n).v (2 * m + (keyOf (rec vs n).v).length % 2 + 1)]) := by
  apply ZkFormal.Near.Render.flatMap_congr'; intro m hm
  rw [gE_key vs n hw hle (List.mem_range.1 hm)]
  simp [oddOf, hle]

theorem nib_pairs (vs : List NodeS3) (n : Nat) (hw : (rec vs n).v.wf) (hle : isLE (rec vs n).v = true) :
    gE vs n (.hpf, 0) ++ (List.range ((keyOf (rec vs n).v).length / 2)).flatMap (fun m => gE vs n (.key, m)) =
      (List.range (keyOf (rec vs n).v).length).map (keyP n (rec vs n).v) := by
  rw [gE_hpf vs n hw hle, key_pairs vs n hw hle, ← nib_enum]
  congr 1
  simp [oddOf, hle]

end NodeGen3

end ZkFormal.NearV3.Render

namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Dsl
open ZkFormal.Near.Render.NodeGen (F Win layout bitOf b2n)
namespace NodeGen3

theorem enum_keyEdges (n : Nat) (k : List Nat) :
    enumL (keyEdges3 n k) = (List.range k.length).map fun i => ([n, i, k.getD i 0, n, i + 1, EK_KEY], i) := by
  simp only [enumL, keyEdges3, List.length_map, List.length_range]
  apply List.map_congr_left; intro i hi
  have := List.mem_range.1 hi
  simp [List.getD_eq_getElem?_getD, this]

theorem rec_pairs_leaf (vs : List NodeS3) (n : Nat) (hw : (rec vs n).v.wf) (k : List Nat) (sv : NSlot3)
    (m : List Nat) (hs : (rec vs n).v = .leaf k sv m) :
    recPairs vs n = enumL (edgesOf3 n (rec vs n)) := by
  have hle : isLE (rec vs n).v = true := by rw [hs]; rfl
  have hnib := nib_pairs vs n hw hle
  simp only [recPairs]
  rw [show fieldsOf (rec vs n).v = [.tag, .hpl, .hpf, .key, .vlen, .vh (valWin sv), .mem] by rw [hs]; rfl]
  have hlen : F.len (hplenOf (rec vs n).v) F.key = (keyOf (rec vs n).v).length / 2 := by
    simp [F.len, hplenOf, hle]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, hlen]
  rw [rangeNil _ (F.len _ .tag) (fun i => gE_other vs n .tag i (by simp) (by simp) (by simp) (by simp) (by simp)),
    rangeNil _ (F.len _ .hpl) (fun i => gE_other vs n .hpl i (by simp) (by simp) (by simp) (by simp) (by simp)),
    rangeNil _ (F.len _ .vlen) (fun i => gE_other vs n .vlen i (by simp) (by simp) (by simp) (by simp) (by simp)),
    range0' _ (F.len _ (.vh (valWin sv))) (by simp [F.len]) (fun i hi => by rw [gE_vh]; simp [hi]),
    range0' _ (F.len _ .mem) (by simp [F.len]) (fun i hi => by rw [gE_mem]; simp [hi])]
  simp only [F.len, List.range_one, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append]
  rw [← List.append_assoc, hnib]
  simp only [edgesOf3, hs, enumL_append, enumL_single, enum_keyEdges, gE_vh, gE_mem, keyP, sOf, keyOf, isExt,
    Bool.false_eq_true, and_false, if_false, isLeaf, if_true, typeOf, tvOf, b2n]
  have hkl : (keyEdges3 n k).length = k.length := by simp [keyEdges3]
  have hk : ∀ v, isExt v = false → List.map (keyP n v) (List.range k.length) =
      List.map (fun i => ([n, i, (keyOf v).getD i 0, n, i + 1, EK_KEY], i)) (List.range k.length) := by
    intro v hv; apply List.map_congr_left; intro i _; simp [keyP, hv]
  cases sv with
  | ref l h =>
    rw [hk _ rfl]
    simp [NodeV3.value, isLeaf, enumL, sOf, keyOf, typeOf, hkl, keyEdges3, List.getD_eq_getElem?_getD]
  | val l i vl pre po wr =>
    rw [hk _ rfl]
    simp [NodeV3.value, isLeaf, enumL, sOf, keyOf, typeOf, vidOf, hkl, List.getD_eq_getElem?_getD]


theorem rec_pairs_ext (vs : List NodeS3) (n : Nat) (hw : (rec vs n).v.wf) (k : List Nat) (kid : NKid)
    (m : List Nat) (hs : (rec vs n).v = .ext k kid m) :
    recPairs vs n = enumL (edgesOf3 n (rec vs n)) := by
  have hle : isLE (rec vs n).v = true := by rw [hs]; rfl
  have hnib := nib_pairs vs n hw hle
  simp only [recPairs]
  rw [show fieldsOf (rec vs n).v = [.tag, .hpl, .hpf, .key, .ch (kidWin kid 0 true none), .mem] by rw [hs]; rfl]
  have hlen : F.len (hplenOf (rec vs n).v) F.key = (keyOf (rec vs n).v).length / 2 := by
    simp [F.len, hplenOf, hle]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, hlen]
  rw [rangeNil _ (F.len _ .tag) (fun i => gE_other vs n .tag i (by simp) (by simp) (by simp) (by simp) (by simp)),
    rangeNil _ (F.len _ .hpl) (fun i => gE_other vs n .hpl i (by simp) (by simp) (by simp) (by simp) (by simp)),
    rangeNil _ (F.len _ (.ch _)) (fun i => by rw [gE_ch]; simp [hle]),
    rangeNil _ (F.len _ .mem) (fun i => by rw [gE_mem]; simp [hs, isLeaf])]
  simp only [F.len, List.range_one, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append]
  rw [hnib]
  simp only [edgesOf3, hs, keyOf]
  rcases List.eq_nil_or_concat k with rfl | ⟨k', x, rfl⟩
  · simp [enumL, keyEdges3]
  · simp only [List.concat_eq_append] at hs ⊢
    have hk : List.map (keyP n (NodeV3.ext (k' ++ [x]) kid m)) (List.range k'.length) =
        List.map (fun i => ([n, i, k'.getD i 0, n, i + 1, EK_KEY], i)) (List.range k'.length) := by
      apply List.map_congr_left; intro i hi
      have := List.mem_range.1 hi
      simp [keyP, sOf, keyOf, List.getD_eq_getElem?_getD, List.getElem?_append_left this]
      omega
    have hkl : (keyEdges3 n k').length = k'.length := by simp [keyEdges3]
    simp only [List.length_append, List.length_singleton, List.range_succ, List.map_append, hk,
      List.dropLast_concat, List.getLast?_concat, enumL_append, enum_keyEdges, hkl]
    congr 1
    cases kid <;> simp [enumL, keyP, sOf, keyOf, isExt, xtgtOf, xtgJOf, xrvOf, xresOf, xdeadOf]

end NodeGen3
end ZkFormal.NearV3.Render
