import ZkFormal.Near.Extract.NodeEdgeBr

/-!
# ZkFormal.Near.Extract.NodePerNode — all messages of one node against its view
-/

namespace ZkFormal.Near.NodeProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Node ZkFormal.Near

def pnSend (n : Nat) (S : NodeS) (bb : Nat) : List Msg :=
  if bb = B_BYTES then emitAt (msgId K_NPRE n) 0 (S.v.ser false) ++ emitAt (msgId K_NPOST n) 0 (S.v.ser true)
  else if bb = B_PARENT then pnParS S
  else if bb = B_EDGE then (edgesOf n S).map (· ++ [0])
  else []

def pnRecv (pub : List Fp) (n : Nat) (S : NodeS) (bb : Nat) : List Msg :=
  if bb = B_DIGEST then (if n = 0 then roots0 S pub else []) ++ pnDig n S
  else if bb = B_PARENT then pnParR n S
  else if bb = B_VSLOT then pnVs n S
  else if bb = B_EDGE then ((edgesOf n S).zip S.uses).map fun (e, u) => e ++ [u]
  else []

theorem zip_fst_snd {α β : Type} (l : List (α × β)) : (l.map (·.1)).zip (l.map (·.2)) = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Node.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

theorem nodeEdgesAll (hC : NodeCtx tr s ℓ fl) {n : Nat} (hn : tr.cell T_NODE s nid = ((n : Nat) : Fp)) (hnP : n < P)
    (h0 : s = 0 ↔ n = 0) : (canonE (rowEdgesN tr pub s ℓ)).map (·.1) = edgesOf n (nodeSOf tr pub s ℓ) := by
  obtain ⟨hr0, ha0⟩ := nodeStart hL hC
  have T := typeSumNat hL hr0 ha0
  by_cases h1 : cv tr T_NODE s tl = 1
  · exact leafEdges hL hC (of_cv_one h1) hn hnP h0
  by_cases h2 : cv tr T_NODE s te = 1
  · exact extEdges hL hC (of_cv_one h2) hn hnP h0
  apply brEdges hL hC _ hn hnP h0
  have := cvb hL hr0 (x := tb1) (by simp [boolCols]); have := cvb hL hr0 (x := tb2) (by simp [boolCols])
  rw [cell_eq_cast tr T_NODE s tb1, cell_eq_cast tr T_NODE s tb2, ← natCast_add,
    show cv tr T_NODE s tb1 + cv tr T_NODE s tb2 = 1 by omega]; rfl

theorem edgeUses (hC : NodeCtx tr s ℓ fl) {n : Nat} (hn : tr.cell T_NODE s nid = ((n : Nat) : Fp)) (hnP : n < P)
    (h0 : s = 0 ↔ n = 0) :
    (edgesOf n (nodeSOf tr pub s ℓ)).zip (nodeSOf tr pub s ℓ).uses = canonE (rowEdgesN tr pub s ℓ) := by
  rw [← nodeEdgesAll hL hC hn hnP h0]
  show ((canonE (rowEdgesN tr pub s ℓ)).map (·.1)).zip ((canonE (rowEdgesN tr pub s ℓ)).map (·.2)) = _
  exact zip_fst_snd _

/-- Every bus, one node. -/
theorem nodeAll (hC : NodeCtx tr s ℓ fl) {n : Nat} (hn : tr.cell T_NODE s nid = ((n : Nat) : Fp)) (hnP : n < P)
    (h0 : s = 0 ↔ n = 0) (hpos : ∀ d, d < ℓ → tr.cell T_NODE (s + d) pos = ((d : Nat) : Fp)) (bb : Nat) :
    ((List.range' s ℓ).flatMap (fun r => rowT tr pub r bb true)).Perm ((pnSend n (nodeSOf tr pub s ℓ) bb).map Msg.toFp) ∧
    ((List.range' s ℓ).flatMap (fun r => rowT tr pub r bb false)).Perm
      ((pnRecv pub n (nodeSOf tr pub s ℓ) bb).map Msg.toFp) := by
  have S := nodeSOf tr pub s ℓ
  have hv : (nodeSOf tr pub s ℓ).v = nodeVOf tr s := rfl
  have hd : (nodeSOf tr pub s ℓ).depth = cv tr T_NODE s depth := rfl
  have hr : (nodeSOf tr pub s ℓ).res = cv tr T_NODE s res := rfl
  have nil : ∀ sd, (List.range' s ℓ).flatMap (fun r => rowT tr pub r bb sd) = [] → ∀ L : List Msg, L = [] →
      ((List.range' s ℓ).flatMap (fun r => rowT tr pub r bb sd)).Perm (L.map Msg.toFp) := by
    intro sd h L hL'; rw [h, hL']; exact List.Perm.refl _
  have edgeS : (List.range' s ℓ).flatMap (fun r => rowT tr pub r B_EDGE true) =
      (rowEdgesN tr pub s ℓ).map fun eu => Msg.toFp (eu.1 ++ [0]) := by
    unfold rowEdgesN; rw [List.map_flatMap]; exact flatMap_congr' (fun r _ => rowT_edgeS_N tr pub r)
  have edgeR : (List.range' s ℓ).flatMap (fun r => rowT tr pub r B_EDGE false) =
      (rowEdgesN tr pub s ℓ).map fun eu => Msg.toFp (eu.1 ++ [eu.2]) := by
    unfold rowEdgesN; rw [List.map_flatMap]; exact flatMap_congr' (fun r _ => rowT_edgeR_N tr pub r)
  by_cases b0 : bb = B_BYTES
  · subst b0
    refine ⟨?_, nil false (flatMap_eq_nil' (fun r _ => rowT_bytesR r)) _ (by simp [pnRecv, B_BYTES, B_DIGEST, B_PARENT, B_VSLOT, B_EDGE])⟩
    simp only [pnSend, if_pos rfl]
    exact nodeBytes hL hC hn hpos
  by_cases b1 : bb = B_DIGEST
  · subst b1
    refine ⟨nil true (flatMap_eq_nil' (fun r _ => rowT_digestS r)) _ (by simp [pnSend, B_BYTES, B_DIGEST, B_PARENT, B_VSLOT, B_EDGE]), ?_⟩
    simp only [pnRecv, if_pos rfl]
    exact (nodeDigPar hL hC _ hv hd hn h0).1
  by_cases b2 : bb = B_PARENT
  · subst b2
    simp only [pnSend, pnRecv, show ¬ B_PARENT = B_BYTES by decide, show ¬ B_PARENT = B_DIGEST by decide, if_false, if_true]
    refine ⟨?_, ?_⟩
    · rw [(nodeDigPar hL hC _ hv hd hn h0).2]
    · rw [nodeParR hL hC _ hv hd hr hn h0]
  by_cases b3 : bb = B_VSLOT
  · subst b3
    refine ⟨nil true (flatMap_eq_nil' (fun r _ => rowT_vslotS r)) _ (by simp [pnSend, B_BYTES, B_DIGEST, B_PARENT, B_VSLOT, B_EDGE]), ?_⟩
    simp only [pnRecv, show ¬ B_VSLOT = B_DIGEST by decide, show ¬ B_VSLOT = B_PARENT by decide, if_false, if_true]
    rw [nodeVs hL hC _ hv hn]
  by_cases b4 : bb = B_EDGE
  · subst b4
    simp only [pnSend, pnRecv, show ¬ B_EDGE = B_BYTES by decide, show ¬ B_EDGE = B_DIGEST by decide,
      show ¬ B_EDGE = B_PARENT by decide, show ¬ B_EDGE = B_VSLOT by decide, if_false, if_true]
    refine ⟨?_, ?_⟩
    · rw [edgeS, ← nodeEdgesAll hL hC hn hnP h0, List.map_map, List.map_map]
      exact (List.Perm.map _ (canonE_perm _)).symm
    · rw [edgeR, edgeUses hL hC hn hnP h0, List.map_map]
      exact (List.Perm.map _ (canonE_perm _)).symm
  have oth := fun sd => flatMap_eq_nil' (l := List.range' s ℓ) (fun r _ => rowT_other (tr := tr) (pub := pub) r bb sd
    ⟨b0, b1, b2, b3, b4⟩)
  exact ⟨nil true (oth true) _ (by simp [pnSend, b0, b2, b4]), nil false (oth false) _ (by simp [pnRecv, b1, b2, b3, b4])⟩

end ZkFormal.Near.NodeProof
