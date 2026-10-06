import ZkFormal.NearV3.Extract.Node.EdgeList

/-!
# ZkFormal.Near.Extract.NodeEdgeMatch — the edges a node's rows provide are `edgesOf`
-/

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3 ZkFormal.Near

def rowEdgesN (tr : Trace Fp) (pub : List Fp) (s ℓ : Nat) : List (Msg × Nat) :=
  (List.range' s ℓ).flatMap (rowEdgeN tr pub)

/-- The view of one node segment. -/
def nodeSOf (tr : Trace Fp) (pub : List Fp) (s ℓ : Nat) : NodeS3 :=
  ⟨nodeVOf tr s, cv tr T_NODE s tau, cv tr T_NODE s depth, cv tr T_NODE s res,
    (canonE (rowEdgesN tr pub s ℓ)).map (·.2), cv tr T_NODE (s + brOff tr s) mBm,
    decide (cv tr T_NODE s dup = 1), decide (cv tr T_NODE s hd = 1), cv tr T_NODE s repE⟩

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
    keyEdges3 n (keyNibs tr s) =
      (if cv tr T_NODE s odd = 1 then [[n, 0, loN tr (s + 5), n, 1, EK_KEY]] else []) ++
      (List.range (cv tr T_NODE s hplen - 1)).flatMap fun d =>
        [[n, 2 * d + (if cv tr T_NODE s odd = 1 then 1 else 0), hiN tr (s + 6 + d), n,
            2 * d + (if cv tr T_NODE s odd = 1 then 1 else 0) + 1, EK_KEY],
         [n, 2 * d + (if cv tr T_NODE s odd = 1 then 1 else 0) + 1, loN tr (s + 6 + d), n,
            2 * d + (if cv tr T_NODE s odd = 1 then 1 else 0) + 2, EK_KEY]] := by
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

/-- The key rows of a node (field `(6, L)`); the last low nibble of an extension goes to
`(xtgt, xtgJ)`. -/
theorem keyRows (hC : NodeCtx tr s ℓ fl) {L : Nat} (hm : 0 < L → (6, L) ∈ fl) (sK : 0 < L → tr.cell T_NODE (s + 6) sKEY = 1)
    {n : Nat} (hn : tr.cell T_NODE s nid = ((n : Nat) : Fp)) (hnP : n < P) :
    (List.range' (s + 6) L).flatMap (rowEdgeN tr pub) = (List.range L).flatMap fun d =>
      [([n, 2 * d + cv tr T_NODE s odd, hiN tr (s + 6 + d), n, 2 * d + cv tr T_NODE s odd + 1, EK_KEY],
          cv tr T_NODE (s + 6 + d) mA),
       ([n, 2 * d + cv tr T_NODE s odd + 1, loN tr (s + 6 + d),
           if d + 1 = L ∧ cv tr T_NODE s te = 1 then cv tr T_NODE s xtgt else n,
           if d + 1 = L ∧ cv tr T_NODE s te = 1 then cv tr T_NODE s xtgJ else 2 * d + cv tr T_NODE s odd + 2, EK_KEY],
          cv tr T_NODE (s + 6 + d) mB)] := by
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

theorem tagRows (hC : NodeCtx tr s ℓ fl) : (List.range' (s + 0) 1).flatMap (rowEdgeN tr pub) = [] := by
  simp only [List.range'_one, List.flatMap_singleton, Nat.add_zero]; exact tagEdge hL hC

set_option maxHeartbeats 2000000 in
theorem leafEdges (hC : NodeCtx tr s ℓ fl) (ht : tr.cell T_NODE s tl = 1) {n : Nat}
    (hn : tr.cell T_NODE s nid = ((n : Nat) : Fp)) (hnP : n < P) :
    (canonE (rowEdgesN tr pub s ℓ)).map (·.1) = edgesOf3 n (nodeSOf tr pub s ℓ) := by
  obtain ⟨hh1, hnk, hfl, hℓ, sT, sH, sF, sK, sV, sVH, sM⟩ := leafFields hL hC ht
  have mem : ∀ p ∈ leafFL (cv tr T_NODE s hplen), p ∈ fl := fun p hp => hfl ▸ hp
  obtain ⟨hr0, ha0⟩ := nodeStart hL hC
  have hte : tr.cell T_NODE s te = 0 := typeZeros hL hC (x := tl) (y := te) (by simp) ht (by simp) (by decide)
  have G := linkGates hL hr0
  simp only at G
  have hxl : cv tr T_NODE s xlast0 = 0 := cv_zero (by rw [G.2.2.2.2.2.2.2.2.2.1, hte, fp_zero_mul])
  have hcl : cv tr T_NODE s tl = 1 := cv_one ht
  have hce : cv tr T_NODE s te = 0 := cv_zero hte
  have bo := cvb hL hr0 (x := odd) (by simp [boolCols])
  -- field contributions
  have F1 := plainEdges hL hC (pub := pub) (L := 4) (mem _ (by simp [leafFL, keyFL])) (by omega) sH (by simp [states])
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have F5 : (List.range' (s + 5) 1).flatMap (rowEdgeN tr pub) =
      if cv tr T_NODE s odd = 1 then [([n, 0, loN tr (s + 5), n, 1, EK_KEY], cv tr T_NODE (s + 5) mA)] else [] := by
    simp only [List.range'_one, List.flatMap_singleton]
    rw [hpfEdge hL hC (mem _ (by simp [leafFL, keyFL])) sF hn hnP, hxl]; simp
  have F6 := keyRows hL hC (pub := pub) (L := cv tr T_NODE s hplen - 1)
    (fun h => mem _ (by simp [leafFL, keyFL]; omega)) (fun h => sK (by omega)) hn hnP
  simp only [hce, show ¬ (0 : Nat) = 1 from by decide, and_false, if_false] at F6
  have FV := plainEdges hL hC (pub := pub) (L := 4) (mem _ (by simp [leafFL, keyFL])) (by omega) sV (by simp [states])
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have FH : (List.range' (s + (9 + cv tr T_NODE s hplen)) 32).flatMap (rowEdgeN tr pub) =
      if cv tr T_NODE s tv = 1 then
        [([n, 2 * (cv tr T_NODE s hplen - 1) + cv tr T_NODE s odd, SYM_END, cv tr T_NODE s vid, 0, EK_VAL],
          cv tr T_NODE (s + (9 + cv tr T_NODE s hplen)) mA)]
      else [] := by
    rw [winEdges hL hC (mem _ (by simp [leafFL, keyFL])) (by omega) (by rw [sVH, stOnly hL (by have := hC.bound; omega)
      (segAct hL hC (by omega)) sVH (by simp [states]) (y := sCH) (by simp [states]) (by decide)]; decide),
      vhEdge hL hC (mem _ (by simp [leafFL, keyFL])) (by omega) sVH hn hnP (fun _ => ⟨hh1, by omega⟩), if_pos hcl]
  have FM := memEdges hL hC (pub := pub) (mem _ (by simp [leafFL, keyFL])) (by omega) sM hn hnP
    (fun _ => ⟨hh1, by omega⟩)
  rw [if_pos hcl] at FM
  have R : rowEdgesN tr pub s ℓ =
      ((if cv tr T_NODE s odd = 1 then [([n, 0, loN tr (s + 5), n, 1, EK_KEY], cv tr T_NODE (s + 5) mA)] else []) ++
       (List.range (cv tr T_NODE s hplen - 1)).flatMap (fun d =>
        [([n, 2 * d + cv tr T_NODE s odd, hiN tr (s + 6 + d), n, 2 * d + cv tr T_NODE s odd + 1, EK_KEY],
            cv tr T_NODE (s + 6 + d) mA),
         ([n, 2 * d + cv tr T_NODE s odd + 1, loN tr (s + 6 + d), n, 2 * d + cv tr T_NODE s odd + 2, EK_KEY],
            cv tr T_NODE (s + 6 + d) mB)])) ++
      ((if cv tr T_NODE s tv = 1 then
        [([n, 2 * (cv tr T_NODE s hplen - 1) + cv tr T_NODE s odd, SYM_END, cv tr T_NODE s vid, 0, EK_VAL],
          cv tr T_NODE (s + (9 + cv tr T_NODE s hplen)) mA)] else []) ++
       [([n, 2 * (cv tr T_NODE s hplen - 1) + cv tr T_NODE s odd, SYM_END, n,
          2 * (cv tr T_NODE s hplen - 1) + cv tr T_NODE s odd, EK_LEND],
          cv tr T_NODE (s + (41 + cv tr T_NODE s hplen)) mB)]) := by
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
  rw [R, canonE_split _ _ (by
    intro e he
    simp only [List.mem_append] at he
    rcases he with he | he
    · split at he
      · simp at he; subst he; simp; have := (nb (s + 5) (by omega) (by omega)).2; unfold SYM_END; omega
      · simp at he
    · rw [List.mem_flatMap] at he
      obtain ⟨d, hd, he⟩ := he
      rw [List.mem_range] at hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · simp; have := (nb (s + 6 + d) (by omega) (by omega)).1; unfold SYM_END; omega
      · simp; have := (nb (s + 6 + d) (by omega) (by omega)).2; unfold SYM_END; omega) (by
    intro e he
    simp only [List.mem_append] at he
    rcases he with he | he
    · split at he
      · simp at he; subst he; simp
      · simp at he
    · simp at he; subst he; simp)]
  unfold nodeSOf edgesOf3 nodeVOf
  simp only [if_pos hcl, keyEdges_nibs, hod, keyNibs_length]
  unfold slotOf
  rw [List.map_append, List.map_append, List.map_append, List.map_flatMap]
  simp only [List.append_assoc]
  congr 1
  · split <;> simp
  congr 1
  by_cases htv : cv tr T_NODE s tv = 1
  · rw [if_pos htv, if_pos htv]; simp; omega
  · rw [if_neg htv, if_neg htv]; simp; omega

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

theorem kE_single (n i0 a : Nat) : kE n i0 [a] = [[n, i0, a, n, i0 + 1, EK_KEY]] := by simp [kE]

theorem kE_odd (n : Nat) (od a : Nat) : kE n 0 (if od = 1 then [a] else []) = if od = 1 then [[n, 0, a, n, 1, EK_KEY]] else [] := by
  split <;> simp [kE]

theorem kE_pairsUpTo (tr : Trace Fp) (s n i0 m : Nat) :
    kE n i0 ((pairsUpTo tr s m).flatMap fun p => [p.1, p.2]) =
      (List.range m).flatMap fun d =>
        [[n, i0 + 2 * d, hiN tr (s + 6 + d), n, i0 + 2 * d + 1, EK_KEY],
         [n, i0 + 2 * d + 1, loN tr (s + 6 + d), n, i0 + 2 * d + 2, EK_KEY]] := by
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
    cv tr T_NODE s xdead + cv tr T_NODE s xrv = 1 ∧ cv tr T_NODE s xlast0 = cv tr T_NODE s nokey ∧
    (cv tr T_NODE s xrv = 1 → cv tr T_NODE s xtgt = cv tr T_NODE s xres ∧ cv tr T_NODE s xtgJ = 0) ∧
    (cv tr T_NODE s xdead = 1 → tr.cell T_NODE s xtgt = tr.cell T_NODE s nid ∧
      tr.cell T_NODE s xtgJ = sE.eval tr T_NODE s pub) := by
  have hoℓ : o < ℓ := by have := (hC.fields.field _ hm); simp at this; have := this.1.pos; omega
  have hr : s + o < tr.height T_NODE := by have := hC.bound; omega
  have hr0 : s < tr.height T_NODE := by omega
  have cst := fun x (hx : x ∈ nodeConst) => segConst hL hC hx hoℓ
  have G := linkGates hL hr (pub := pub)
  simp only at G
  obtain ⟨-, -, -, -, -, -, -, -, -, -, g10, -, g12, -⟩ := G
  have G0 := linkGates hL hr0 (pub := pub)
  simp only at G0
  obtain ⟨-, -, -, -, -, -, -, -, h8, h9, -, -, -, h13, h14, h15, h16, -⟩ := G0
  rw [cst te (by simp [nodeConst]), ht, sC] at g10 g12
  have bx := isBool hL hr0 (x := xrv) (by simp [boolCols])
  have bd := isBool hL hr0 (x := xdead) (by simp [boolCols])
  refine ⟨?_, ?_, ?_, ?_, fun h => ?_, fun h => ?_⟩
  · unfold cv; rw [← cst xrv (by simp [nodeConst]), fp_sub_eq g10]
  · unfold cv; rw [← cst xres (by simp [nodeConst]), fp_sub_eq g12]
  · unfold cv; rw [h8, ht]
    rcases bx with h | h <;> rw [h]
    · rw [show (1 : Fp) * (1 - 0) = 1 by decide, Fp.toNat_one, Fp.toNat_zero]
    · rw [show (1 : Fp) * (1 - 1) = 0 by decide, Fp.toNat_one, Fp.toNat_zero]
  · unfold cv; rw [h9, ht, fp_one_mul']
  · have h1 := of_cv_one h; rw [h1] at h13 h14
    exact ⟨by unfold cv; rw [show tr.cell T_NODE s xtgt = tr.cell T_NODE s xres by grind],
      by unfold cv; rw [show tr.cell T_NODE s xtgJ = 0 by grind]; rfl⟩
  · have h1 := of_cv_one h; rw [h1] at h15 h16
    exact ⟨by grind, by grind⟩

end ZkFormal.NearV3.NodeProof3

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3 ZkFormal.Near

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal NodeV3.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

set_option maxHeartbeats 4000000 in
theorem extEdges (hC : NodeCtx tr s ℓ fl) (ht : tr.cell T_NODE s te = 1) {n : Nat}
    (hn : tr.cell T_NODE s nid = ((n : Nat) : Fp)) (hnP : n < P) :
    (canonE (rowEdgesN tr pub s ℓ)).map (·.1) = edgesOf3 n (nodeSOf tr pub s ℓ) := by
  obtain ⟨hh1, hnk, hfl, hℓ, sT, sH, sF, sK, sC, sM⟩ := extFields hL hC ht
  have mem : ∀ p ∈ extFL (cv tr T_NODE s hplen), p ∈ fl := fun p hp => hfl ▸ hp
  obtain ⟨hr0, ha0⟩ := nodeStart hL hC
  have htl : tr.cell T_NODE s tl = 0 := typeZeros hL hC (x := te) (y := tl) (by simp) ht (by simp) (by decide)
  have hcl : cv tr T_NODE s tl ≠ 1 := by rw [cv_zero htl]; decide
  have hce : cv tr T_NODE s te = 1 := cv_one ht
  obtain ⟨Krv, Kres, Kdead, Klast, Ktg1, Ktg2⟩ :=
    extKid hL hC ht (pub := pub) (mem (5 + cv tr T_NODE s hplen, 32) (by simp [extFL])) sC
  have bo := cvb hL hr0 (x := odd) (by simp [boolCols])
  have brv := cvb hL (r := s + (5 + cv tr T_NODE s hplen)) (by have := hC.bound; omega) (x := rv) (by simp [boolCols])
  have bxr := cvb hL hr0 (x := xrv) (by simp [boolCols])
  have hP := hP_of hL hC
  -- the dead target
  have hsE : cv tr T_NODE s xdead = 1 → cv tr T_NODE s xtgt = n ∧
      cv tr T_NODE s xtgJ = 2 * (cv tr T_NODE s hplen - 1) + cv tr T_NODE s odd := by
    intro hd
    obtain ⟨t1, t2⟩ := Ktg2 hd
    refine ⟨by unfold cv; rw [t1]; exact cv_of_eq hn hnP, ?_⟩
    apply cv_of_eq _ (by omega)
    rw [t2]
    simp only [sE, eval_add, eval_smul, eval_sub, eval_c, eval_k]
    rw [cell_eq_cast tr T_NODE s hplen, cell_eq_cast tr T_NODE s odd,
      show cv tr T_NODE s hplen = (cv tr T_NODE s hplen - 1) + 1 by omega,
      natCast_add (cv tr T_NODE s hplen - 1) 1, natCast_add, natCast_mul]
    grind
  have nb : ∀ r, s ≤ r → r < s + ℓ → hiN tr r < 16 ∧ loN tr r < 16 := fun r h1 h2 => by
    obtain ⟨a, b', -, -⟩ := nibs hL (r := r) (pub := pub) (by have := hC.bound; omega); exact ⟨a, b'⟩
  -- field contributions
  have F1 := plainEdges hL hC (pub := pub) (L := 4) (mem _ (by simp [extFL, keyFL])) (by omega) sH (by simp [states])
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have FC : (List.range' (s + (5 + cv tr T_NODE s hplen)) 32).flatMap (rowEdgeN tr pub) = [] := by
    rw [winEdges hL hC (mem _ (by simp [extFL, keyFL])) (by omega) (by rw [sC, stOnly hL (by have := hC.bound; omega)
      (segAct hL hC (by omega)) sC (by simp [states]) (y := sVH) (by simp [states]) (by decide)]; decide),
      chEdge hL hC (mem _ (by simp [extFL, keyFL])) (by omega) sC hn hnP htl, hce]; simp
  have FM := memEdges hL hC (pub := pub) (mem _ (by simp [extFL, keyFL])) (by omega) sM hn hnP
    (fun h => absurd h hcl)
  rw [if_neg hcl] at FM
  have R : rowEdgesN tr pub s ℓ = rowEdgeN tr pub (s + 5) ++
      (List.range' (s + 6) (cv tr T_NODE s hplen - 1)).flatMap (rowEdgeN tr pub) := by
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
    simp only [List.mem_append, List.mem_flatMap, List.mem_range] at he
    rcases he with he | ⟨d, hd, he⟩
    · split at he
      · simp at he; subst he; simp; have := (nb (s + 5) (by omega) (by omega)).2; unfold SYM_END; omega
      · simp at he
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · simp; have := (nb (s + 6 + d) (by omega) (by omega)).1; unfold SYM_END; omega
      · simp; have := (nb (s + 6 + d) (by omega) (by omega)).2; unfold SYM_END; omega
  rw [show rowEdgesN tr pub s ℓ = rowEdgesN tr pub s ℓ ++ [] by simp, canonE_split _ [] hA (by simp),
    List.append_nil, R]
  unfold nodeSOf edgesOf3 nodeVOf
  simp only [if_neg hcl, if_pos hce]
  rw [List.map_append]
  have bk := cvb hL hr0 (x := nokey) (by simp [boolCols])
  by_cases h1 : cv tr T_NODE s hplen = 1
  · -- no key bytes
    have hk1 : cv tr T_NODE s nokey = 1 := cv_one (hnk.2 h1)
    rw [h1]; simp only [Nat.sub_self, List.range_zero, List.flatMap_nil, List.map_nil, List.append_nil]
    have hkn : keyNibs tr s = if cv tr T_NODE s odd = 1 then [loN tr (s + 5)] else [] := by
      unfold keyNibs keyPairs; rw [h1]; simp
    rw [hkn]
    unfold kidOf
    by_cases ho : cv tr T_NODE s odd = 1
    · simp only [if_pos ho, hk1, if_true]
      rw [h1] at Krv Kres
      by_cases hv : cv tr T_NODE (s + (5 + 1)) rv = 1
      · have hx1 : cv tr T_NODE s xrv = 1 := by omega
        obtain ⟨g1, g2⟩ := Ktg1 hx1
        rw [if_pos hv, g1, g2, Kres]; simp [keyEdges3]
      · have hd1 : cv tr T_NODE s xdead = 1 := by omega
        obtain ⟨g1, g2⟩ := hsE hd1
        rw [if_neg hv, g1, g2, h1, ho]; simp [keyEdges3]
    · rw [if_neg ho, if_neg ho]; simp [keyEdges3]
  · -- key bytes
    have h2 : 2 ≤ cv tr T_NODE s hplen := by omega
    have hk0 : cv tr T_NODE s nokey = 0 := by
      rcases Nat.lt_or_ge (cv tr T_NODE s nokey) 1 with h | h
      · omega
      · exfalso; exact h1 (hnk.1 (of_cv_one (by omega)))
    rw [keyNibs_split tr s h2]
    rw [show (cv tr T_NODE s hplen - 1) = (cv tr T_NODE s hplen - 2) + 1 by omega, List.range_succ, List.flatMap_append]
    simp only [hk0, show ¬ (0 : Nat) = 1 by decide, if_false, List.flatMap_singleton]
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
    rw [List.map_append, List.map_flatMap]
    have hK : (List.range (cv tr T_NODE s hplen - 2)).flatMap (fun d =>
        List.map (fun x : Msg × Nat => x.1)
          [([n, 2 * d + cv tr T_NODE s odd, hiN tr (s + 6 + d), n, 2 * d + cv tr T_NODE s odd + 1, EK_KEY],
              cv tr T_NODE (s + 6 + d) mA),
           ([n, 2 * d + cv tr T_NODE s odd + 1, loN tr (s + 6 + d),
                if d + 1 = cv tr T_NODE s hplen - 2 + 1 ∧ True then cv tr T_NODE s xtgt else n,
                if d + 1 = cv tr T_NODE s hplen - 2 + 1 ∧ True then cv tr T_NODE s xtgJ else 2 * d + cv tr T_NODE s odd + 2,
                EK_KEY], cv tr T_NODE (s + 6 + d) mB)]) =
        (List.range (cv tr T_NODE s hplen - 2)).flatMap (fun d =>
          [[n, cv tr T_NODE s odd + 2 * d, hiN tr (s + 6 + d), n, cv tr T_NODE s odd + 2 * d + 1, EK_KEY],
           [n, cv tr T_NODE s odd + 2 * d + 1, loN tr (s + 6 + d), n, cv tr T_NODE s odd + 2 * d + 2, EK_KEY]]) := by
      apply flatMap_congr'; intro d hd; rw [List.mem_range] at hd
      rw [if_neg (by omega), if_neg (by omega)]
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
      refine ⟨by simp; omega, by simp; omega⟩
    simp only [and_true] at hK ⊢
    rw [hK]
    simp only [List.append_assoc, and_self, if_true, List.map_cons, List.map_nil]
    congr 1
    · split <;> simp
    congr 1
    simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and]
    constructor
    · simp; omega
    unfold kidOf
    by_cases hv : cv tr T_NODE (s + (5 + cv tr T_NODE s hplen)) rv = 1
    · have hx1 : cv tr T_NODE s xrv = 1 := by omega
      obtain ⟨g1, g2⟩ := Ktg1 hx1
      rw [if_pos hv, g1, g2, Kres]
      simp; omega
    · have hd1 : cv tr T_NODE s xdead = 1 := by omega
      obtain ⟨g1, g2⟩ := hsE hd1
      rw [if_neg hv, g1, g2]
      simp; omega

end ZkFormal.NearV3.NodeProof3
