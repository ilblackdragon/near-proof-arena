import ZkFormal.NearV3.Extract.Node.EdgeBr
import ZkFormal.NearV3.Extract.Node.Digs

/-!
# ZkFormal.NearV3.Extract.Node.PerNode — all messages of one node against its view
-/

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3 ZkFormal.Near

def pnSend (n : Nat) (S : NodeS3) (bb : Nat) : List Msg :=
  if bb = B_BYTES then emitAt (msgId K_NPRE n) 0 (S.v.ser false) ++ emitAt (msgId K_NPOST n) 0 (S.v.ser true)
  else if bb = B_PARENT then pnParS S
  else if bb = B_VPARENT then pnVpar S
  else if bb = B_EDGE then (edgesOf3 n S).map (· ++ [0])
  else if bb = B_BMAP then pnBmS n S
  else if bb = B_DIGS then pnDigs S
  else if bb = B_ENT then pnEntS n S
  else if bb = B_UPB then upbOf n S fun _ => 0
  else []

def pnRecv (n : Nat) (S : NodeS3) (bb : Nat) : List Msg :=
  if bb = B_DIGEST then pnDig S
  else if bb = B_PARENT then pnParR n S
  else if bb = B_EDGE then ((edgesOf3 n S).zip S.uses).map fun (e, u) => e ++ [u]
  else if bb = B_BMAP then pnBmR n S
  else if bb = B_DUP then pnDup n S
  else if bb = B_ENT then pnEntR S
  else if bb = B_UPB then upbOf n S fun p => S.mU.getD p 0
  else []

theorem zip_fst_snd {α β : Type} (l : List (α × β)) : (l.map (·.1)).zip (l.map (·.2)) = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal NodeV3.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

theorem nodeEdgesAll (hC : NodeCtx tr s ℓ fl) {n : Nat} (hn : tr.cell T_NODE s nid = ((n : Nat) : Fp)) (hnP : n < P) :
    (canonE (rowEdgesN tr pub s ℓ)).map (·.1) = edgesOf3 n (nodeSOf tr pub s ℓ) := by
  obtain ⟨hr0, ha0⟩ := nodeStart hL hC
  have T := typeSumNat hL hr0 ha0
  by_cases h1 : cv tr T_NODE s tl = 1
  · exact leafEdges hL hC (of_cv_one h1) hn hnP
  by_cases h2 : cv tr T_NODE s te = 1
  · exact extEdges hL hC (of_cv_one h2) hn hnP
  apply brEdges hL hC _ hn hnP
  have := cvb hL hr0 (x := tb1) (by simp [boolCols]); have := cvb hL hr0 (x := tb2) (by simp [boolCols])
  rw [cell_eq_cast tr T_NODE s tb1, cell_eq_cast tr T_NODE s tb2, ← natCast_add,
    show cv tr T_NODE s tb1 + cv tr T_NODE s tb2 = 1 by omega]; rfl

theorem edgeUses (hC : NodeCtx tr s ℓ fl) {n : Nat} (hn : tr.cell T_NODE s nid = ((n : Nat) : Fp)) (hnP : n < P) :
    (edgesOf3 n (nodeSOf tr pub s ℓ)).zip (nodeSOf tr pub s ℓ).uses = canonE (rowEdgesN tr pub s ℓ) := by
  rw [← nodeEdgesAll hL hC hn hnP]
  show ((canonE (rowEdgesN tr pub s ℓ)).map (·.1)).zip ((canonE (rowEdgesN tr pub s ℓ)).map (·.2)) = _
  exact zip_fst_snd _

omit hL in
theorem rowsB_getD (tr : Trace Fp) (x r n d : Nat) (hd : d < n) : (rowsB tr x r n).getD d 0 = cv tr T_NODE (r + d) x := by
  unfold rowsB; rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hd]; rfl

/-- `UPB` provider messages of one record (`u = 0` sent, `mU` received). -/
theorem nodeUpb (hC : NodeCtx tr s ℓ fl) {n : Nat} (hn : tr.cell T_NODE s nid = ((n : Nat) : Fp))
    (hpos : ∀ d, d < ℓ → tr.cell T_NODE (s + d) pos = ((d : Nat) : Fp)) (sd : Bool) :
    (List.range' s ℓ).flatMap (fun r => rowT tr pub r B_UPB sd) =
      (upbOf n (nodeSOf tr pub s ℓ) (fun p => if sd then 0 else (nodeSOf tr pub s ℓ).mU.getD p 0)).map Msg.toFp := by
  obtain ⟨S1, S2⟩ := nodeSer hL hC
  have hl : ((nodeSOf tr pub s ℓ).v.ser false).length = ℓ := by
    show ((nodeVOf tr s).ser false).length = ℓ; rw [← S1, rowsB_length]
  unfold upbOf
  rw [hl, List.range'_eq_map_range, List.flatMap_map, List.map_map, map_eq_flatMap]
  apply flatMap_congr'; intro d hd; rw [List.mem_range] at hd
  have hnid : tr.cell T_NODE (s + d) nid = ((n : Nat) : Fp) := by rw [segConst hL hC (by simp [nodeConst]) hd, hn]
  have hlen : tr.cell T_NODE (s + d) len = ((ℓ : Nat) : Fp) := by
    rw [segConst hL hC (by simp [nodeConst]) hd, lenCell hL hC]
  have hdep : tr.cell T_NODE (s + d) depth = ((cv tr T_NODE s depth : Nat) : Fp) := by
    rw [segConst hL hC (by simp [nodeConst]) hd, cast_cv]
  have hpb : ((nodeSOf tr pub s ℓ).v.ser true).getD d 0 = cv tr T_NODE (s + d) pb := by
    show ((nodeVOf tr s).ser true).getD d 0 = _; rw [← S2, rowsB_getD _ _ _ _ _ hd]
  have hcid : (nodeSOf tr pub s ℓ).ucid.getD d 0 = cv tr T_NODE (s + d) cid := rowsB_getD _ _ _ _ _ hd
  have hmU : (nodeSOf tr pub s ℓ).mU.getD d 0 = cv tr T_NODE (s + d) NodeV3.mU := rowsB_getD _ _ _ _ _ hd
  have hdS : (nodeSOf tr pub s ℓ).depth = cv tr T_NODE s depth := rfl
  cases sd
  · rw [rowT_upbR, segAct hL hC hd, gate_one]
    simp only [Function.comp, Msg.toFp, upbV, List.map_cons, List.map_nil, Bool.false_eq_true, if_false, hpb, hcid,
      hmU, hdS, hnid, hlen, hdep, hpos d hd, ← natCast_eq, toFp_msgId, cast_cv]
  · rw [rowT_upbS, segAct hL hC hd, gate_one]
    simp only [Function.comp, Msg.toFp, upbV, List.map_cons, List.map_nil, if_true, hpb, hcid,
      hdS, hnid, hlen, hdep, hpos d hd, ← natCast_eq, toFp_msgId, cast_cv]
    rfl

set_option maxHeartbeats 1000000 in
/-- Every bus, one node. -/
theorem nodeAll (hC : NodeCtx tr s ℓ fl) {n : Nat} (hn : tr.cell T_NODE s nid = ((n : Nat) : Fp)) (hnP : n < P)
    (hpos : ∀ d, d < ℓ → tr.cell T_NODE (s + d) pos = ((d : Nat) : Fp)) (bb : Nat) :
    ((List.range' s ℓ).flatMap (fun r => rowT tr pub r bb true)).Perm ((pnSend n (nodeSOf tr pub s ℓ) bb).map Msg.toFp) ∧
    ((List.range' s ℓ).flatMap (fun r => rowT tr pub r bb false)).Perm
      ((pnRecv n (nodeSOf tr pub s ℓ) bb).map Msg.toFp) := by
  have hv : (nodeSOf tr pub s ℓ).v = nodeVOf tr s := rfl
  have ht : (nodeSOf tr pub s ℓ).tau = cv tr T_NODE s tau := rfl
  have hd : (nodeSOf tr pub s ℓ).depth = cv tr T_NODE s depth := rfl
  have hr : (nodeSOf tr pub s ℓ).res = cv tr T_NODE s res := rfl
  have hub : (nodeSOf tr pub s ℓ).ubm = cv tr T_NODE (s + brOff tr s) mBm := rfl
  have hdu : (nodeSOf tr pub s ℓ).dup = decide (cv tr T_NODE s dup = 1) := rfl
  have hhd : (nodeSOf tr pub s ℓ).hd = decide (cv tr T_NODE s NodeV3.hd = 1) := rfl
  have hre : (nodeSOf tr pub s ℓ).repE = cv tr T_NODE s repE := rfl
  have D := nodeDPVB hL hC (pub := pub) _ hv ht hd hn hub
  have nil : ∀ sd, (List.range' s ℓ).flatMap (fun r => rowT tr pub r bb sd) = [] → ∀ L : List Msg, L = [] →
      ((List.range' s ℓ).flatMap (fun r => rowT tr pub r bb sd)).Perm (L.map Msg.toFp) := by
    intro sd h L hL'; rw [h, hL']; exact List.Perm.refl _
  have edgeS : (List.range' s ℓ).flatMap (fun r => rowT tr pub r B_EDGE true) =
      (rowEdgesN tr pub s ℓ).map fun eu => Msg.toFp (eu.1 ++ [0]) := by
    unfold rowEdgesN; rw [List.map_flatMap]; exact flatMap_congr' (fun r _ => rowT_edgeS_N tr pub r)
  have edgeR : (List.range' s ℓ).flatMap (fun r => rowT tr pub r B_EDGE false) =
      (rowEdgesN tr pub s ℓ).map fun eu => Msg.toFp (eu.1 ++ [eu.2]) := by
    unfold rowEdgesN; rw [List.map_flatMap]; exact flatMap_congr' (fun r _ => rowT_edgeR_N tr pub r)
  have E := nodeEnt hL hC (pub := pub) _ hv hdu hhd hre hn hpos
  have eq : ∀ {a b' : List (List Fp)}, a = b' → a.Perm b' := fun h => h ▸ List.Perm.refl _
  have z := fun sd (f : ∀ r, rowT tr pub r bb sd = []) => flatMap_eq_nil' (l := List.range' s ℓ) (fun r _ => f r)
  unfold pnSend pnRecv
  by_cases b0 : bb = B_BYTES
  · subst b0
    refine ⟨?_, nil false (z false rowT_bytesR) _ (by simp [B_BYTES, B_DIGEST, B_PARENT, B_EDGE, B_BMAP, B_DUP, B_ENT, B_UPB])⟩
    simp only [if_pos rfl]
    exact nodeBytes hL hC hn hpos
  by_cases b1 : bb = B_DIGEST
  · subst b1
    refine ⟨nil true (z true rowT_digestS) _ (by simp [B_BYTES, B_DIGEST, B_PARENT, B_VPARENT, B_EDGE, B_BMAP, B_DIGS, B_ENT, B_UPB]), ?_⟩
    simp only [if_pos rfl]
    exact D.1
  by_cases b2 : bb = B_PARENT
  · subst b2
    simp only [show ¬ B_PARENT = B_BYTES by decide, show ¬ B_PARENT = B_DIGEST by decide, if_false, if_true]
    exact ⟨eq D.2.1, eq (nodeParR hL hC _ hv ht hd hr hn)⟩
  by_cases b3 : bb = B_VPARENT
  · subst b3
    simp only [show ¬ B_VPARENT = B_BYTES by decide, show ¬ B_VPARENT = B_DIGEST by decide,
      show ¬ B_VPARENT = B_PARENT by decide, show ¬ B_VPARENT = B_EDGE by decide, show ¬ B_VPARENT = B_BMAP by decide,
      show ¬ B_VPARENT = B_DUP by decide, show ¬ B_VPARENT = B_ENT by decide, if_false, if_true]
    exact ⟨eq D.2.2.1, nil false (z false rowT_vparentR) _ rfl⟩
  by_cases b4 : bb = B_EDGE
  · subst b4
    simp only [show ¬ B_EDGE = B_BYTES by decide, show ¬ B_EDGE = B_DIGEST by decide,
      show ¬ B_EDGE = B_PARENT by decide, show ¬ B_EDGE = B_VPARENT by decide, if_false, if_true]
    refine ⟨?_, ?_⟩
    · rw [edgeS, ← nodeEdgesAll hL hC hn hnP, List.map_map, List.map_map]
      exact (List.Perm.map _ (canonE_perm _)).symm
    · rw [edgeR, edgeUses hL hC hn hnP, List.map_map]
      exact (List.Perm.map _ (canonE_perm _)).symm
  by_cases b5 : bb = B_BMAP
  · subst b5
    simp only [show ¬ B_BMAP = B_BYTES by decide, show ¬ B_BMAP = B_DIGEST by decide,
      show ¬ B_BMAP = B_PARENT by decide, show ¬ B_BMAP = B_VPARENT by decide, show ¬ B_BMAP = B_EDGE by decide,
      if_false, if_true]
    exact ⟨eq D.2.2.2.1, eq D.2.2.2.2⟩
  by_cases b6 : bb = B_DIGS
  · subst b6
    simp only [show ¬ B_DIGS = B_BYTES by decide, show ¬ B_DIGS = B_DIGEST by decide,
      show ¬ B_DIGS = B_PARENT by decide, show ¬ B_DIGS = B_VPARENT by decide, show ¬ B_DIGS = B_EDGE by decide,
      show ¬ B_DIGS = B_BMAP by decide, show ¬ B_DIGS = B_DUP by decide, show ¬ B_DIGS = B_ENT by decide,
      if_false, if_true]
    exact ⟨nodeDigs hL hC _ hv ht, nil false (z false rowT_digsR) _ rfl⟩
  by_cases b7 : bb = B_DUP
  · subst b7
    simp only [show ¬ B_DUP = B_BYTES by decide, show ¬ B_DUP = B_DIGEST by decide,
      show ¬ B_DUP = B_PARENT by decide, show ¬ B_DUP = B_VPARENT by decide, show ¬ B_DUP = B_EDGE by decide,
      show ¬ B_DUP = B_BMAP by decide, show ¬ B_DUP = B_DIGS by decide, show ¬ B_DUP = B_ENT by decide,
      if_false, if_true]
    exact ⟨nil true (z true rowT_dupS) _ rfl, eq (nodeDup hL hC _ hdu hre hn)⟩
  by_cases b8 : bb = B_ENT
  · subst b8
    simp only [show ¬ B_ENT = B_BYTES by decide, show ¬ B_ENT = B_DIGEST by decide,
      show ¬ B_ENT = B_PARENT by decide, show ¬ B_ENT = B_VPARENT by decide, show ¬ B_ENT = B_EDGE by decide,
      show ¬ B_ENT = B_BMAP by decide, show ¬ B_ENT = B_DIGS by decide, show ¬ B_ENT = B_DUP by decide,
      if_false, if_true]
    exact ⟨eq E.1, eq E.2⟩
  by_cases b10 : bb = B_UPB
  · subst b10
    simp only [show ¬ B_UPB = B_BYTES by decide, show ¬ B_UPB = B_DIGEST by decide,
      show ¬ B_UPB = B_PARENT by decide, show ¬ B_UPB = B_VPARENT by decide, show ¬ B_UPB = B_EDGE by decide,
      show ¬ B_UPB = B_BMAP by decide, show ¬ B_UPB = B_DIGS by decide, show ¬ B_UPB = B_DUP by decide,
      show ¬ B_UPB = B_ENT by decide, if_false, if_true]
    exact ⟨eq (nodeUpb hL hC hn hpos true), eq (nodeUpb hL hC hn hpos false)⟩
  simp only [b0, b1, b2, b3, b4, b5, b6, b7, b8, b10, if_false, List.map_nil]
  by_cases b9 : bb = B_SIZE
  · subst b9
    exact ⟨nil true (nodeSize hL hC true) _ rfl, nil false (nodeSize hL hC false) _ rfl⟩
  have oth := fun sd => flatMap_eq_nil' (l := List.range' s ℓ) (fun r _ => rowT_other (tr := tr) (pub := pub) r bb sd
    ⟨b0, b1, b2, b4, b5, b6, b9, b7, b8, b3, b10⟩)
  exact ⟨nil true (oth true) _ rfl, nil false (oth false) _ rfl⟩

end ZkFormal.NearV3.NodeProof3
