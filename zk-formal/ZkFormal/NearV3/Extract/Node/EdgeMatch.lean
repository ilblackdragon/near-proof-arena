import ZkFormal.NearV3.Extract.Node.EdgeList

/-!
# ZkFormal.Near.Extract.NodeEdgeMatch — the edges a node's rows provide are `edgesOf`
-/

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3 ZkFormal.Near

def rowEdgesN (tr : Trace Fp) (pub : List Fp) (s ℓ : Nat) : List (Msg × Nat) :=
  (List.range' s ℓ).flatMap (rowEdgeN tr pub)

/-- The view of one node segment. -/
def nodeSOf (tr : Trace Fp) (pub : List Fp) (s ℓ : Nat) : NodeS :=
  ⟨nodeVOf tr s, cv tr T_NODE s depth, cv tr T_NODE s res, (canonE (rowEdgesN tr pub s ℓ)).map (·.2)⟩

def startE (tr : Trace Fp) (s : Nat) : List (Msg × Nat) :=
  if s = 0 then [([0, 0, SYM_START, cv tr T_NODE s res, 0], cv tr T_NODE s mA)] else []

theorem keyPairs_getD (tr : Trace Fp) (s d : Nat) (hd : d < cv tr T_NODE s hplen - 1) :
    (keyPairs tr s).getD d (0, 0) = (hiN tr (s + 6 + d), loN tr (s + 6 + d)) := by
  unfold keyPairs
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range' (by omega)]
  simp

theorem keyPairs_length (tr : Trace Fp) (s : Nat) : (keyPairs tr s).length = cv tr T_NODE s hplen - 1 := by
  simp [keyPairs]

theorem keyNibs_length (tr : Trace Fp) (s : Nat) :
    (keyNibs tr s).length = (if cv tr T_NODE s odd = 1 then 1 else 0) + 2 * (cv tr T_NODE s hplen - 1) := by
  unfold keyNibs; rw [List.length_append, flatMap_pairs_length, keyPairs_length]; split <;> simp

/-- Key edges of a key: first nibble (if odd), then two per pair. -/
theorem keyEdges_nibs (tr : Trace Fp) (s n : Nat) :
    keyEdges n (keyNibs tr s) =
      (if cv tr T_NODE s odd = 1 then [[n, 0, loN tr (s + 5), n, 1]] else []) ++
      (List.range (cv tr T_NODE s hplen - 1)).flatMap fun d =>
        [[n, 2 * d + (if cv tr T_NODE s odd = 1 then 1 else 0), hiN tr (s + 6 + d), n,
            2 * d + (if cv tr T_NODE s odd = 1 then 1 else 0) + 1],
         [n, 2 * d + (if cv tr T_NODE s odd = 1 then 1 else 0) + 1, loN tr (s + 6 + d), n,
            2 * d + (if cv tr T_NODE s odd = 1 then 1 else 0) + 2]] := by
  rw [keyEdges_kE]; unfold keyNibs
  rw [kE_append, kE_pairs, keyPairs_length]
  congr 1
  · split <;> simp [kE]
  · apply flatMap_congr'; intro d hd; rw [List.mem_range] at hd
    rw [keyPairs_getD tr s d hd]
    split <;> simp <;> omega

end ZkFormal.NearV3.NodeProof3

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3 ZkFormal.Near

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal NodeV3.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

/-- The key rows of a node (field `(6, L)`), all edges normal except possibly the last low nibble. -/
theorem keyRows (hC : NodeCtx tr s ℓ fl) {L : Nat} (hm : 0 < L → (6, L) ∈ fl) (sK : 0 < L → tr.cell T_NODE (s + 6) sKEY = 1)
    {n : Nat} (hn : tr.cell T_NODE s nid = ((n : Nat) : Fp)) (hnP : n < P) :
    (List.range' (s + 6) L).flatMap (rowEdgeN tr pub) = (List.range L).flatMap fun d =>
      [([n, 2 * d + cv tr T_NODE s odd, hiN tr (s + 6 + d), n, 2 * d + cv tr T_NODE s odd + 1], cv tr T_NODE (s + 6 + d) mA)] ++
      (if d + 1 = L ∧ cv tr T_NODE s xdead = 1 then [] else
        [([n, 2 * d + cv tr T_NODE s odd + 1, loN tr (s + 6 + d),
           if d + 1 = L ∧ cv tr T_NODE s te = 1 then cv tr T_NODE s xres else n,
           if d + 1 = L ∧ cv tr T_NODE s te = 1 then 0 else 2 * d + cv tr T_NODE s odd + 2], cv tr T_NODE (s + 6 + d) mB)]) := by
  rw [List.range'_eq_map_range, List.flatMap_map]
  apply flatMap_congr'; intro d hd; rw [List.mem_range] at hd
  exact keyRowEdge hL hC (hm (by omega)) (by omega) (sK (by omega)) hd hn hnP

theorem symOf_ne (x : Nat) (h : x < 16) : x ≠ SYM_END := by unfold SYM_END; omega

end ZkFormal.NearV3.NodeProof3

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3 ZkFormal.Near

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal NodeV3.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

theorem tagRows (hC : NodeCtx tr s ℓ fl) : (List.range' (s + 0) 1).flatMap (rowEdgeN tr pub) = startE tr s := by
  simp only [List.range'_one, List.flatMap_singleton, Nat.add_zero]; rw [tagEdge hL hC]; rfl

set_option maxHeartbeats 1000000 in
theorem leafEdges (hC : NodeCtx tr s ℓ fl) (ht : tr.cell T_NODE s tl = 1) {n : Nat}
    (hn : tr.cell T_NODE s nid = ((n : Nat) : Fp)) (hnP : n < P) (h0 : s = 0 ↔ n = 0) :
    (canonE (rowEdgesN tr pub s ℓ)).map (·.1) = edgesOf n (nodeSOf tr pub s ℓ) := by
  obtain ⟨hh1, hnk, hfl, hℓ, sT, sH, sF, sK, sV, sVH, sM⟩ := leafFields hL hC ht
  have mem : ∀ p ∈ leafFL (cv tr T_NODE s hplen), p ∈ fl := fun p hp => hfl ▸ hp
  obtain ⟨hr0, ha0⟩ := nodeStart hL hC
  have hte : tr.cell T_NODE s te = 0 := typeZeros hL hC (x := tl) (y := te) (by simp) ht (by simp) (by decide)
  have G := linkGates hL hr0
  simp only at G
  have hxd : cv tr T_NODE s xdead = 0 := cv_zero (by rw [G.2.2.2.1, hte]; exact fp_zero_mul _)
  have hxl : cv tr T_NODE s xlast0 = 0 := cv_zero (by rw [G.2.2.2.2.1, hte, fp_zero_mul])
  have hcl : cv tr T_NODE s tl = 1 := cv_one ht
  have hce : cv tr T_NODE s te = 0 := cv_zero hte
  have bo := cvb hL hr0 (x := odd) (by simp [boolCols])
  -- field contributions
  have F1 := plainEdges hL hC (pub := pub) (L := 4) (mem _ (by simp [leafFL, keyFL])) (by omega) sH (by simp [states])
    (by decide) (by decide) (by decide) (by decide)
  have F5 : (List.range' (s + 5) 1).flatMap (rowEdgeN tr pub) =
      if cv tr T_NODE s odd = 1 then [([n, 0, loN tr (s + 5), n, 1], cv tr T_NODE (s + 5) mA)] else [] := by
    simp only [List.range'_one, List.flatMap_singleton]
    rw [hpfEdge hL hC (mem _ (by simp [leafFL, keyFL])) sF hn hnP, hxd, hxl]; simp
  have F6 := keyRows hL hC (pub := pub) (L := cv tr T_NODE s hplen - 1)
    (fun h => mem _ (by simp [leafFL, keyFL]; omega)) (fun h => sK (by omega)) hn hnP
  simp only [hxd, hce, show ¬ (1 : Nat) = 0 from by decide, and_false, if_false] at F6
  have FV := plainEdges hL hC (pub := pub) (L := 4) (mem _ (by simp [leafFL, keyFL])) (by omega) sV (by simp [states])
    (by decide) (by decide) (by decide) (by decide)
  have FH : (List.range' (s + (9 + cv tr T_NODE s hplen)) 32).flatMap (rowEdgeN tr pub) =
      if cv tr T_NODE s tv = 1 then
        [([n, 2 * (cv tr T_NODE s hplen - 1) + cv tr T_NODE s odd, SYM_END, n, 0], cv tr T_NODE (s + (9 + cv tr T_NODE s hplen)) mA)]
      else [] := by
    rw [winEdges hL hC (mem _ (by simp [leafFL, keyFL])) (by omega) (by rw [sVH, stOnly hL (by have := hC.bound; omega)
      (segAct hL hC (by omega)) sVH (by simp [states]) (y := sCH) (by simp [states]) (by decide)]; decide),
      vhEdge hL hC (mem _ (by simp [leafFL, keyFL])) (by omega) sVH hn hnP (fun _ => ⟨hh1, by omega⟩), if_pos hcl]
  have FM := plainEdges hL hC (pub := pub) (L := 8) (mem _ (by simp [leafFL, keyFL])) (by omega) sM (by simp [states])
    (by decide) (by decide) (by decide) (by decide)
  have R : rowEdgesN tr pub s ℓ = startE tr s ++
      ((if cv tr T_NODE s odd = 1 then [([n, 0, loN tr (s + 5), n, 1], cv tr T_NODE (s + 5) mA)] else []) ++
       (List.range (cv tr T_NODE s hplen - 1)).flatMap (fun d =>
        [([n, 2 * d + cv tr T_NODE s odd, hiN tr (s + 6 + d), n, 2 * d + cv tr T_NODE s odd + 1], cv tr T_NODE (s + 6 + d) mA),
         ([n, 2 * d + cv tr T_NODE s odd + 1, loN tr (s + 6 + d), n, 2 * d + cv tr T_NODE s odd + 2], cv tr T_NODE (s + 6 + d) mB)])) ++
      (if cv tr T_NODE s tv = 1 then
        [([n, 2 * (cv tr T_NODE s hplen - 1) + cv tr T_NODE s odd, SYM_END, n, 0], cv tr T_NODE (s + (9 + cv tr T_NODE s hplen)) mA)]
      else []) := by
    unfold rowEdgesN; rw [rowsFields hL hC, hfl]; unfold leafFL keyFL
    by_cases h1 : cv tr T_NODE s hplen = 1
    · simp only [if_pos h1, List.append_nil, List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_nil]
      rw [tagRows hL hC, F1, F5, FV, FH, FM]
      rw [h1] at F6 ⊢; simp
    · simp only [if_neg h1, List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_nil]
      rw [tagRows hL hC, F1, F5, F6, FV, FH, FM]
      simp [List.append_assoc]
  have hod : (if cv tr T_NODE s odd = 1 then 1 else 0) = cv tr T_NODE s odd := by split <;> omega
  have nb : ∀ r, s ≤ r → r < s + ℓ → hiN tr r < 16 ∧ loN tr r < 16 := fun r h1 h2 => by
    obtain ⟨a, b', -, -⟩ := nibs hL (r := r) (pub := pub) (by have := hC.bound; omega); exact ⟨a, b'⟩
  have hA : ∀ e ∈ startE tr s ++ ((if cv tr T_NODE s odd = 1 then [([n, 0, loN tr (s + 5), n, 1], cv tr T_NODE (s + 5) mA)] else []) ++
       (List.range (cv tr T_NODE s hplen - 1)).flatMap (fun d =>
        [([n, 2 * d + cv tr T_NODE s odd, hiN tr (s + 6 + d), n, 2 * d + cv tr T_NODE s odd + 1], cv tr T_NODE (s + 6 + d) mA),
         ([n, 2 * d + cv tr T_NODE s odd + 1, loN tr (s + 6 + d), n, 2 * d + cv tr T_NODE s odd + 2], cv tr T_NODE (s + 6 + d) mB)])),
      e.1.getD 2 0 ≠ SYM_END := by
    intro e he
    simp only [List.mem_append, startE] at he
    rcases he with he | he | he
    · split at he
      · simp at he; subst he; simp [SYM_START, SYM_END]
      · simp at he
    · split at he
      · simp at he; subst he; simp; have := (nb (s + 5) (by omega) (by omega)).2; unfold SYM_END; omega
      · simp at he
    · rw [List.mem_flatMap] at he
      obtain ⟨d, hd, he⟩ := he
      rw [List.mem_range] at hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · simp; have := (nb (s + 6 + d) (by omega) (by omega)).1; unfold SYM_END; omega
      · simp; have := (nb (s + 6 + d) (by omega) (by omega)).2; unfold SYM_END; omega
  have hB : ∀ e ∈ (if cv tr T_NODE s tv = 1 then
        [([n, 2 * (cv tr T_NODE s hplen - 1) + cv tr T_NODE s odd, SYM_END, n, 0], cv tr T_NODE (s + (9 + cv tr T_NODE s hplen)) mA)]
      else []), e.1.getD 2 0 = SYM_END := by
    intro e he; split at he
    · simp at he; subst he; simp
    · simp at he
  rw [R, canonE_split _ _ hA hB]
  unfold nodeSOf edgesOf nodeVOf
  simp only [if_pos hcl, keyEdges_nibs, hod, keyNibs_length]
  unfold slotOf startE
  rw [List.map_append, List.map_append, List.map_append, List.map_flatMap]
  simp only [List.append_assoc]
  congr 1
  · by_cases hs : s = 0
    · rw [if_pos hs, if_pos (h0.1 hs)]; subst hs; simp
    · rw [if_neg hs, if_neg (fun h => hs (h0.2 h))]; simp
  congr 1
  · split <;> simp
  congr 1
  by_cases htv : cv tr T_NODE s tv = 1
  · rw [if_pos htv, if_pos htv]; simp; omega
  · rw [if_neg htv, if_neg htv]; simp

end ZkFormal.NearV3.NodeProof3

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3 ZkFormal.Near

def pairsUpTo (tr : Trace Fp) (s m : Nat) : List (Nat × Nat) :=
  (List.range' 0 m).map fun d => (hiN tr (s + 6 + d), loN tr (s + 6 + d))

theorem keyNibs_split (tr : Trace Fp) (s : Nat) (h2 : 2 ≤ cv tr T_NODE s hplen) :
    keyNibs tr s = ((if cv tr T_NODE s odd = 1 then [loN tr (s + 5)] else []) ++
      (pairsUpTo tr s (cv tr T_NODE s hplen - 2)).flatMap (fun p => [p.1, p.2])) ++
      [hiN tr (s + 6 + (cv tr T_NODE s hplen - 2)), loN tr (s + 6 + (cv tr T_NODE s hplen - 2))] := by
  unfold keyNibs keyPairs pairsUpTo
  rw [show cv tr T_NODE s hplen - 1 = (cv tr T_NODE s hplen - 2) + 1 by omega, range'_succ', List.map_append,
    List.flatMap_append]
  simp [List.append_assoc]

theorem kE_single (n i0 a : Nat) : kE n i0 [a] = [[n, i0, a, n, i0 + 1]] := by simp [kE]

theorem kE_odd (n : Nat) (od a : Nat) : kE n 0 (if od = 1 then [a] else []) = if od = 1 then [[n, 0, a, n, 1]] else [] := by
  split <;> simp [kE]

theorem kE_pairsUpTo (tr : Trace Fp) (s n i0 m : Nat) :
    kE n i0 ((pairsUpTo tr s m).flatMap fun p => [p.1, p.2]) =
      (List.range m).flatMap fun d =>
        [[n, i0 + 2 * d, hiN tr (s + 6 + d), n, i0 + 2 * d + 1], [n, i0 + 2 * d + 1, loN tr (s + 6 + d), n, i0 + 2 * d + 2]] := by
  rw [kE_pairs]; unfold pairsUpTo; rw [List.length_map, List.length_range']
  apply flatMap_congr'; intro d hd; rw [List.mem_range] at hd
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range' hd]; simp

end ZkFormal.NearV3.NodeProof3

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3 ZkFormal.Near

theorem fp_one_mul' (x : Fp) : (1 : Fp) * x = x := by grind
theorem fp_sub_eq {a b' : Fp} (h : 1 * 1 * (a - b') = 0) : a = b' := by grind

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal NodeV3.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

/-- Extension-child facts read at the child window. -/
theorem extKid (hC : NodeCtx tr s ℓ fl) (ht : tr.cell T_NODE s te = 1) {o : Nat} (hm : (o, 32) ∈ fl)
    (sC : tr.cell T_NODE (s + o) sCH = 1) :
    cv tr T_NODE s xrv = cv tr T_NODE (s + o) rv ∧ cv tr T_NODE s xres = cv tr T_NODE (s + o) cres ∧
    cv tr T_NODE s xdead + cv tr T_NODE s xrv = 1 ∧ cv tr T_NODE s xlast0 = cv tr T_NODE s nokey := by
  have hoℓ : o < ℓ := by have := (hC.fields.field _ hm); simp at this; have := this.1.pos; omega
  have hr : s + o < tr.height T_NODE := by have := hC.bound; omega
  have hr0 : s < tr.height T_NODE := by omega
  have cst := fun x (hx : x ∈ nodeConst) => segConst hL hC hx hoℓ
  have G := linkGates hL hr
  simp only at G
  have G0 := linkGates hL hr0
  simp only at G0
  rw [cst te (by simp [nodeConst]), ht, sC] at G
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold cv; rw [← cst xrv (by simp [nodeConst]), fp_sub_eq G.2.2.2.2.2.1]
  · unfold cv; rw [← cst xres (by simp [nodeConst]), fp_sub_eq G.2.2.2.2.2.2.2.1]
  · have bx := isBool hL hr0 (x := xrv) (by simp [boolCols])
    unfold cv; rw [G0.2.2.2.1, ht]
    rcases bx with h | h <;> rw [h]
    · rw [show (1 : Fp) * (1 - 0) = 1 by decide, Fp.toNat_one, Fp.toNat_zero]
    · rw [show (1 : Fp) * (1 - 1) = 0 by decide, Fp.toNat_one, Fp.toNat_zero]
  · unfold cv; rw [G0.2.2.2.2.1, ht, fp_one_mul']

end ZkFormal.NearV3.NodeProof3

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3 ZkFormal.Near

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal NodeV3.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

set_option maxHeartbeats 4000000 in
theorem extEdges (hC : NodeCtx tr s ℓ fl) (ht : tr.cell T_NODE s te = 1) {n : Nat}
    (hn : tr.cell T_NODE s nid = ((n : Nat) : Fp)) (hnP : n < P) (h0 : s = 0 ↔ n = 0) :
    (canonE (rowEdgesN tr pub s ℓ)).map (·.1) = edgesOf n (nodeSOf tr pub s ℓ) := by
  obtain ⟨hh1, hnk, hfl, hℓ, sT, sH, sF, sK, sC, sM⟩ := extFields hL hC ht
  have mem : ∀ p ∈ extFL (cv tr T_NODE s hplen), p ∈ fl := fun p hp => hfl ▸ hp
  obtain ⟨hr0, ha0⟩ := nodeStart hL hC
  have htl : tr.cell T_NODE s tl = 0 := typeZeros hL hC (x := te) (y := tl) (by simp) ht (by simp) (by decide)
  have hcl : cv tr T_NODE s tl ≠ 1 := by rw [cv_zero htl]; decide
  have hce : cv tr T_NODE s te = 1 := cv_one ht
  obtain ⟨Krv, Kres, Kdead, Klast⟩ := extKid hL hC ht (mem (5 + cv tr T_NODE s hplen, 32) (by simp [extFL])) sC
  have bo := cvb hL hr0 (x := odd) (by simp [boolCols])
  have brv := cvb hL (r := s + (5 + cv tr T_NODE s hplen)) (by have := hC.bound; omega) (x := rv) (by simp [boolCols])
  have bxr := cvb hL hr0 (x := xrv) (by simp [boolCols])
  have nb : ∀ r, s ≤ r → r < s + ℓ → hiN tr r < 16 ∧ loN tr r < 16 := fun r h1 h2 => by
    obtain ⟨a, b', -, -⟩ := nibs hL (r := r) (pub := pub) (by have := hC.bound; omega); exact ⟨a, b'⟩
  -- field contributions
  have F1 := plainEdges hL hC (pub := pub) (L := 4) (mem _ (by simp [extFL, keyFL])) (by omega) sH (by simp [states])
    (by decide) (by decide) (by decide) (by decide)
  have FC : (List.range' (s + (5 + cv tr T_NODE s hplen)) 32).flatMap (rowEdgeN tr pub) = [] := by
    rw [winEdges hL hC (mem _ (by simp [extFL, keyFL])) (by omega) (by rw [sC, stOnly hL (by have := hC.bound; omega)
      (segAct hL hC (by omega)) sC (by simp [states]) (y := sVH) (by simp [states]) (by decide)]; decide),
      chEdge hL hC (mem _ (by simp [extFL, keyFL])) (by omega) sC hn hnP htl, hce]; simp
  have FM := plainEdges hL hC (pub := pub) (L := 8) (mem _ (by simp [extFL, keyFL])) (by omega) sM (by simp [states])
    (by decide) (by decide) (by decide) (by decide)
  have R : rowEdgesN tr pub s ℓ = startE tr s ++ (rowEdgeN tr pub (s + 5) ++
      (List.range' (s + 6) (cv tr T_NODE s hplen - 1)).flatMap (rowEdgeN tr pub)) := by
    unfold rowEdgesN; rw [rowsFields hL hC, hfl]; unfold extFL keyFL
    by_cases h1 : cv tr T_NODE s hplen = 1
    · simp only [if_pos h1, List.append_nil, List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_nil]
      rw [tagRows hL hC, F1, FC, FM, h1]; simp
    · simp only [if_neg h1, List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_nil]
      rw [tagRows hL hC, F1, FC, FM]
      simp [List.append_assoc]
  rw [hpfEdge hL hC (mem _ (by simp [extFL, keyFL])) sF hn hnP, Klast,
    keyRows hL hC (pub := pub) (L := cv tr T_NODE s hplen - 1)
      (fun hh => mem _ (by simp [extFL, keyFL]; omega)) (fun hh => sK (by omega)) hn hnP, hce] at R
  -- every row edge is a non-END edge
  have hA : ∀ e ∈ rowEdgesN tr pub s ℓ, e.1.getD 2 0 ≠ SYM_END := by
    rw [R]; intro e he
    simp only [List.mem_append, startE, List.mem_flatMap, List.mem_range] at he
    rcases he with he | he | ⟨d, hd, he⟩
    · split at he
      · simp at he; subst he; simp [SYM_START, SYM_END]
      · simp at he
    · split at he
      · simp at he; subst he; simp; have := (nb (s + 5) (by omega) (by omega)).2; unfold SYM_END; omega
      · simp at he
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | he
      · simp; have := (nb (s + 6 + d) (by omega) (by omega)).1; unfold SYM_END; omega
      · split at he
        · simp at he
        · simp at he; subst he; simp; have := (nb (s + 6 + d) (by omega) (by omega)).2; unfold SYM_END; omega
  rw [show rowEdgesN tr pub s ℓ = rowEdgesN tr pub s ℓ ++ [] by simp, canonE_split _ [] hA (by simp),
    List.append_nil, R]
  unfold nodeSOf edgesOf nodeVOf startE
  simp only [if_neg hcl, if_pos hce]
  rw [List.map_append, List.map_append]
  congr 1
  · by_cases hs : s = 0
    · rw [if_pos hs, if_pos (h0.1 hs)]; subst hs; simp
    · rw [if_neg hs, if_neg (fun h => hs (h0.2 h))]; simp
  by_cases h1 : cv tr T_NODE s hplen = 1
  · -- no key bytes
    have hk1 : cv tr T_NODE s nokey = 1 := cv_one (hnk.2 h1)
    rw [h1]; simp only [Nat.sub_self, List.range'_zero, List.flatMap_nil, List.append_nil]
    have hkn : keyNibs tr s = if cv tr T_NODE s odd = 1 then [loN tr (s + 5)] else [] := by
      unfold keyNibs keyPairs; rw [h1]; simp
    rw [hkn]
    unfold kidOf
    by_cases ho : cv tr T_NODE s odd = 1
    · simp only [if_pos ho, hk1, true_and]
      by_cases hv : cv tr T_NODE (s + (5 + 1)) rv = 1
      · rw [h1] at Krv Kres
        have hd0 : cv tr T_NODE s xdead = 0 := by omega
        rw [if_pos hv, hd0]; simp [Kres, keyEdges, h1, ho]
      · rw [h1] at Krv Kres
        have hd1 : cv tr T_NODE s xdead = 1 := by omega
        rw [if_neg hv, hd1]; simp [keyEdges]
    · simp [ho, keyEdges]
  · -- key bytes
    have h2 : 2 ≤ cv tr T_NODE s hplen := by omega
    have hk0 : cv tr T_NODE s nokey = 0 := by
      have := cvb hL hr0 (x := nokey) (by simp [boolCols])
      rcases Nat.lt_or_ge (cv tr T_NODE s nokey) 1 with h | h
      · omega
      · exfalso; exact h1 (hnk.1 (of_cv_one (by omega)))
    rw [keyNibs_split tr s h2]
    rw [show (cv tr T_NODE s hplen - 1) = (cv tr T_NODE s hplen - 2) + 1 by omega, List.range_succ, List.flatMap_append]
    simp only [hk0, show ¬ (0 : Nat) = 1 by decide, false_and, and_false, not_false_eq_true, and_true, if_false,
      List.flatMap_singleton]
    rw [List.dropLast_append_of_ne_nil (by simp), show [hiN tr (s + 6 + (cv tr T_NODE s hplen - 2)),
      loN tr (s + 6 + (cv tr T_NODE s hplen - 2))].dropLast = [hiN tr (s + 6 + (cv tr T_NODE s hplen - 2))] from rfl,
      List.getLast?_append, keyEdges_kE, kE_append, kE_append, kE_odd, kE_pairsUpTo, kE_single]
    have hodl : (if cv tr T_NODE s odd = 1 then [loN tr (s + 5)] else []).length = cv tr T_NODE s odd := by
      split <;> simp <;> omega
    have hpl : (List.flatMap (fun p : Nat × Nat => [p.1, p.2]) (pairsUpTo tr s (cv tr T_NODE s hplen - 2))).length =
        2 * (cv tr T_NODE s hplen - 2) := by
      rw [flatMap_pairs_length]; simp [pairsUpTo]
    simp only [List.length_append, hodl, hpl, Nat.zero_add, List.length_cons, List.length_nil,
      List.getLast?_cons_cons, List.getLast?_singleton, Option.some_or]
    rw [List.map_append, List.map_flatMap, List.map_append]
    have hK : (List.range (cv tr T_NODE s hplen - 2)).flatMap (fun d =>
        List.map (fun x : Msg × Nat => x.1)
          ([([n, 2 * d + cv tr T_NODE s odd, hiN tr (s + 6 + d), n, 2 * d + cv tr T_NODE s odd + 1],
              cv tr T_NODE (s + 6 + d) mA)] ++
            if d + 1 = cv tr T_NODE s hplen - 2 + 1 ∧ cv tr T_NODE s xdead = 1 then []
            else
              [([n, 2 * d + cv tr T_NODE s odd + 1, loN tr (s + 6 + d),
                    if d + 1 = cv tr T_NODE s hplen - 2 + 1 then cv tr T_NODE s xres else n,
                    if d + 1 = cv tr T_NODE s hplen - 2 + 1 then 0 else 2 * d + cv tr T_NODE s odd + 2],
                  cv tr T_NODE (s + 6 + d) mB)])) =
        (List.range (cv tr T_NODE s hplen - 2)).flatMap (fun d =>
          [[n, cv tr T_NODE s odd + 2 * d, hiN tr (s + 6 + d), n, cv tr T_NODE s odd + 2 * d + 1],
           [n, cv tr T_NODE s odd + 2 * d + 1, loN tr (s + 6 + d), n, cv tr T_NODE s odd + 2 * d + 2]]) := by
      apply flatMap_congr'; intro d hd; rw [List.mem_range] at hd
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      simp only [List.map_append, List.map_cons, List.map_nil, List.singleton_append, List.cons.injEq, and_true]
      refine ⟨by simp; omega, by simp; omega⟩
    rw [hK]
    simp only [List.append_assoc]
    congr 1
    · split <;> simp
    congr 1
    unfold kidOf
    by_cases hv : cv tr T_NODE (s + (5 + cv tr T_NODE s hplen)) rv = 1
    · have hd0 : cv tr T_NODE s xdead = 0 := by omega
      rw [if_pos hv, hd0]
      simp [Kres]
      omega
    · have hd1 : cv tr T_NODE s xdead = 1 := by omega
      rw [if_neg hv, hd1]
      simp
      omega

end ZkFormal.NearV3.NodeProof3
