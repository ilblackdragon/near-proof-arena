import ZkFormal.Near.Extract.NodeEdgeList

/-!
# ZkFormal.Near.Extract.NodeEdgeMatch — the edges a node's rows provide are `edgesOf`
-/

namespace ZkFormal.Near.NodeProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Node ZkFormal.Near

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

end ZkFormal.Near.NodeProof

namespace ZkFormal.Near.NodeProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Node ZkFormal.Near

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Node.table tr T_NODE pub)
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

end ZkFormal.Near.NodeProof

namespace ZkFormal.Near.NodeProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Node ZkFormal.Near

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Node.table tr T_NODE pub)
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

end ZkFormal.Near.NodeProof
