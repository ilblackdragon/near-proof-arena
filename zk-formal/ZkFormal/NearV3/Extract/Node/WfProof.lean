import ZkFormal.NearV3.Extract.Node.Main

/-!
# ZkFormal.NearV3.Extract.Node.WfProof — local well-formedness of the node view
-/

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3 ZkFormal.Near

theorem win_lt (tr : Trace Fp) (col : Nat → Nat) (r : Nat) : ∀ x ∈ win tr col r, x < P := by
  intro x hx; unfold win at hx; rw [List.mem_map] at hx; obtain ⟨i, -, rfl⟩ := hx; exact cv_lt _ _ _ _

theorem rowsB_lt (tr : Trace Fp) (c r n : Nat) : ∀ x ∈ rowsB tr c r n, x < P := by
  intro x hx; unfold rowsB at hx; rw [List.mem_map] at hx; obtain ⟨i, -, rfl⟩ := hx; exact cv_lt _ _ _ _

theorem slotOf_raw (tr : Trace Fp) (s rV rH : Nat) : ∀ x ∈ (slotOf tr s rV rH).raw, x < P := by
  unfold slotOf; split
  · intro x hx; simp only [NSlot3.raw, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (((h | h | h) | h) | h)
    · exact rowsB_lt _ _ _ _ x h
    · subst h; exact cv_lt _ _ _ _
    · subst h; exact cv_lt _ _ _ _
    · exact win_lt _ _ _ x h
    · exact win_lt _ _ _ x h
  · intro x hx; simp only [NSlot3.raw, List.mem_append] at hx
    rcases hx with h | h
    · exact rowsB_lt _ _ _ _ x h
    · exact win_lt _ _ _ x h

theorem kidOf_wf (tr : Trace Fp) (r : Nat) :
    kidOf tr r ≠ .none ∧ (kidOf tr r).wf ∧ ∀ x ∈ (kidOf tr r).raw, x < P := by
  unfold kidOf; split
  · refine ⟨by simp, ⟨win_length _ _ _, win_length _ _ _⟩, ?_⟩
    intro x hx; simp only [NKid.raw, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with ((h | h | h) | h) | h
    · subst h; exact cv_lt _ _ _ _
    · subst h; exact cv_lt _ _ _ _
    · subst h; exact cv_lt _ _ _ _
    · exact win_lt _ _ _ x h
    · exact win_lt _ _ _ x h
  · exact ⟨by simp, win_length _ _ _, fun x hx => win_lt _ _ _ x hx⟩

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal NodeV3.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

/-- A value slot (`VLEN` field at `oV`, `VH` window at `oH`) is well formed. -/
theorem slotOf_wf (hC : NodeCtx tr s ℓ fl) {oV oH : Nat} (hV : (oV, 4) ∈ fl) (sV : tr.cell T_NODE (s + oV) sVLEN = 1)
    (hH : (oH, 32) ∈ fl) (sH : tr.cell T_NODE (s + oH) sVH = 1) : (slotOf tr s (s + oV) (s + oH)).wf := by
  obtain ⟨FV, HV⟩ := fieldAt hL hC hV
  obtain ⟨FH, HH⟩ := fieldAt hL hC hH
  have inV : oV + 4 ≤ ℓ := (hC.fields.field _ hV).2
  have inH : oH + 32 ≤ ℓ := (hC.fields.field _ hH).2
  have hr0 := (nodeStart hL hC).1
  unfold slotOf; split
  · rename_i htv
    have htv3 : tr.cell T_NODE (s + oV + 3) tv = 1 := by
      rw [show s + oV + 3 = s + (oV + 3) by omega, segConst hL hC (by simp [nodeConst]) (by omega)]; exact of_cv_one htv
    obtain ⟨V1, V2⟩ := vlenVal hL FV (by omega) sV htv3
    have hvl : cv tr T_NODE (s + oV + 3) vlen = cv tr T_NODE s vlen := by
      unfold cv; rw [show s + oV + 3 = s + (oV + 3) by omega, segConst hL hC (by simp [nodeConst]) (by omega)]
    refine ⟨rowsB_length _ _ _ _, win_length _ _ _, win_length _ _ _, fun hw => ?_, V1, fun hb => by rw [V2 hb, hvl]⟩
    have hw0 : tr.cell T_NODE (s + oH) tw = 0 := by
      rw [segConst hL hC (by simp [nodeConst]) (by omega)]
      rcases isBool hL hr0 (x := tw) (by simp [boolCols]) with h | h
      · exact h
      · simp [cv_one h] at hw
    have hfs : tr.cell T_NODE (s + oH) fs = 1 := by simpa using (FH.fs 0 (by omega)).2 rfl
    unfold win; apply List.map_congr_left; intro i hi; rw [List.mem_range] at hi
    unfold cv; rw [(winLoad hL (by omega) hfs i hi).2 sH hw0]
  · exact ⟨rowsB_length _ _ _ _, win_length _ _ _⟩

theorem keyNibs_lt (hC : NodeCtx tr s ℓ fl) (hlt : tr.cell T_NODE s tl + tr.cell T_NODE s te = 1) :
    ∀ x ∈ keyNibs tr s, x < 16 := by
  have hkp := keyPart hL hC hlt
  obtain ⟨hh1, -, -⟩ := hkp
  have hℓ : 6 + cv tr T_NODE s hplen ≤ ℓ := by
    rcases (show tr.cell T_NODE s tl = 1 ∨ tr.cell T_NODE s te = 1 by
      obtain ⟨hr0, ha0⟩ := nodeStart hL hC
      rcases isBool hL hr0 (x := tl) (by simp [boolCols]) with h | h
      · rw [h] at hlt; right; grind
      · left; exact h) with h | h
    · have := (leafFields hL hC h).2.2.2.1; omega
    · have := (extFields hL hC h).2.2.2.1; omega
  have nb : ∀ r, s ≤ r → r < s + ℓ → hiN tr r < 16 ∧ loN tr r < 16 := fun r h1 h2 => by
    obtain ⟨a, b', -, -⟩ := nibs hL (r := r) (pub := pub) (by have := hC.bound; omega); exact ⟨a, b'⟩
  intro x hx
  unfold keyNibs at hx; rw [List.mem_append] at hx
  rcases hx with hx | hx
  · split at hx
    · simp at hx; subst hx; exact (nb (s + 5) (by omega) (by omega)).2
    · simp at hx
  · rw [List.mem_flatMap] at hx; obtain ⟨p, hp, hx⟩ := hx
    unfold keyPairs at hp; rw [List.mem_map] at hp; obtain ⟨m, hm, rfl⟩ := hp
    rw [List.mem_range'] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact (nb (s + 6 + m) (by omega) (by omega)).1
    · exact (nb (s + 6 + m) (by omega) (by omega)).2

set_option maxHeartbeats 1000000 in
theorem nodeV_wf (hC : NodeCtx tr s ℓ fl) : (nodeVOf tr s).wf ∧ ∀ x ∈ (nodeVOf tr s).raw, x < P := by
  obtain ⟨hr0, ha0⟩ := nodeStart hL hC
  have T := typeSumNat hL hr0 ha0
  unfold nodeVOf
  by_cases h1 : cv tr T_NODE s tl = 1
  · rw [if_pos h1]
    have hte := typeZeros hL hC (x := tl) (y := te) (by simp) (of_cv_one h1) (by simp) (by decide)
    have K := keyNibs_lt hL hC (by rw [of_cv_one h1, hte]; exact fp_add_zero' rfl)
    obtain ⟨-, -, hfl, -, -, -, -, -, sV, sVH, -⟩ := leafFields hL hC (of_cv_one h1)
    have sw := slotOf_wf hL hC (hfl ▸ (by simp [leafFL] : (5 + cv tr T_NODE s hplen, 4) ∈ leafFL _)) sV
      (hfl ▸ (by simp [leafFL] : (9 + cv tr T_NODE s hplen, 32) ∈ leafFL _)) sVH
    refine ⟨⟨K, sw, rowsB_length _ _ _ _⟩, ?_⟩
    intro x hx; simp only [NodeV3.raw, List.mem_append] at hx
    rcases hx with (h | h) | h
    · have := K x h; unfold P; omega
    · exact slotOf_raw tr _ _ _ x h
    · exact rowsB_lt _ _ _ _ x h
  rw [if_neg h1]
  by_cases h2 : cv tr T_NODE s te = 1
  · rw [if_pos h2]
    have htl0 : tr.cell T_NODE s tl = 0 := of_cv_zero (show cv tr T_NODE s tl = 0 by omega)
    have K := keyNibs_lt hL hC (by rw [of_cv_one h2, htl0]; exact fp_zero_add' rfl)
    obtain ⟨kn, kw, kr⟩ := kidOf_wf tr (s + (5 + cv tr T_NODE s hplen))
    refine ⟨⟨K, kn, kw, rowsB_length _ _ _ _⟩, ?_⟩
    intro x hx; simp only [NodeV3.raw, List.mem_append] at hx
    rcases hx with (h | h) | h
    · have := K x h; unfold P; omega
    · exact kr x h
    · exact rowsB_lt _ _ _ _ x h
  rw [if_neg h2]
  have hb : tr.cell T_NODE s tb1 + tr.cell T_NODE s tb2 = 1 := by
    have b1 := cvb hL hr0 (x := tb1) (by simp [boolCols])
    have b2 := cvb hL hr0 (x := tb2) (by simp [boolCols])
    rw [cell_eq_cast tr T_NODE s tb1, cell_eq_cast tr T_NODE s tb2, ← natCast_add,
      show cv tr T_NODE s tb1 + cv tr T_NODE s tb2 = 1 by omega]; rfl
  have kidsW : ∀ kd ∈ kidsOf tr s (brOff tr s), kd.wf ∧ ∀ x ∈ kd.raw, x < P := by
    intro kd hkd; unfold kidsOf at hkd; rw [List.mem_map] at hkd; obtain ⟨j, -, rfl⟩ := hkd
    split
    · exact ⟨(kidOf_wf tr _).2.1, (kidOf_wf tr _).2.2⟩
    · exact ⟨trivial, by simp [NKid.raw]⟩
  refine ⟨⟨by simp [kidsOf], fun sl hsl => ?_, fun kd hkd => (kidsW kd hkd).1, rowsB_length _ _ _ _⟩, ?_⟩
  · split at hsl
    · rename_i hb2
      simp at hsl; subst hsl
      have B := brFields hL hC hb
      simp only at B
      rw [← brOff_eq hL hC] at B
      obtain ⟨hfl, -, -, sVV, -⟩ := B
      have h37 : brOff tr s = 37 := by unfold brOff; rw [if_pos hb2]
      obtain ⟨sV, sH⟩ := sVV h37
      exact slotOf_wf hL hC (hfl ▸ (by simp [brFL, h37] : (1, 4) ∈ brFL (brOff tr s) (popN tr s))) sV
        (hfl ▸ (by simp [brFL, h37] : (5, 32) ∈ brFL (brOff tr s) (popN tr s))) sH
    · simp at hsl
  · intro x hx; simp only [NodeV3.raw, List.mem_append] at hx
    rcases hx with (h | h) | h
    · split at h
      · simp at h; exact slotOf_raw tr _ _ _ x h
      · simp at h
    · rw [List.mem_flatMap] at h; obtain ⟨kd, hkd, h⟩ := h; exact (kidsW kd hkd).2 x h
    · exact rowsB_lt _ _ _ _ x h

/-- `depth + 112` is a 9-bit value on the node's first row. -/
theorem depthBound (hC : NodeCtx tr s ℓ fl) : cv tr T_NODE s depth < 400 ∨ P - 112 ≤ cv tr T_NODE s depth := by
  obtain ⟨hr0, ha0⟩ := nodeStart hL hC
  have hnf : tr.cell T_NODE s nf = 1 := by have := hC.seg.2.1; rwa [one_iff] at this
  have c1 := con hL hr0 (e := .mul (c nf) (sub (.add (c depth) (k 112)) depE))
    (by simp [NodeV3.constraints, NodeV3.cRows])
  obtain ⟨-, -, hh, hl⟩ := nibs hL hr0 (pub := pub)
  have bd := cvb hL hr0 (x := dbit8) (by simp [boolCols])
  have hlt := (nibs hL hr0 (pub := pub)).1
  have llt := (nibs hL hr0 (pub := pub)).2.1
  simp only [eval_mul, eval_c, eval_sub, eval_add, eval_k, depE, eval_smul, hh, hl, hnf] at c1
  have E : tr.cell T_NODE s depth + ((112 : Nat) : Fp) =
      ((hiN tr s + 16 * loN tr s + 256 * cv tr T_NODE s dbit8 : Nat) : Fp) := by
    rw [natCast_add, natCast_add, natCast_mul, natCast_mul, cast_cv]; grind
  rw [cell_eq_cast tr T_NODE s depth, ← natCast_add] at E
  by_cases hp : cv tr T_NODE s depth + 112 < P
  · left
    have := fp_cast_eq hp (by unfold P; omega) E
    omega
  · right; omega

end ZkFormal.NearV3.NodeProof3

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3 ZkFormal.Near

theorem rowEdgeN_snd_lt (tr : Trace Fp) (pub : List Fp) (r : Nat) : ∀ eu ∈ rowEdgeN tr pub r, eu.2 < P := by
  intro eu he; unfold rowEdgeN at he; rw [List.mem_append] at he
  rcases he with he | he <;> (split at he <;> simp at he) <;> (subst he; exact cv_lt _ _ _ _)

theorem uses_lt (tr : Trace Fp) (pub : List Fp) (s ℓ : Nat) : ∀ u ∈ (nodeSOf tr pub s ℓ).uses, u < P := by
  intro u hu
  simp only [nodeSOf, List.mem_map] at hu
  obtain ⟨eu, he, rfl⟩ := hu
  have := (canonE_perm _).mem_iff.mp he
  unfold rowEdgesN at this; rw [List.mem_flatMap] at this
  obtain ⟨r, -, hr⟩ := this
  exact rowEdgeN_snd_lt tr pub r eu hr

theorem fp_mul3_z1 (a : Fp) : (1 : Fp) * 0 * a = 0 := by grind
theorem fp_mul3_z2 (a : Fp) : (1 : Fp) * a * (1 - 1) = 0 := by grind

theorem fp_mul_zero_cases {a b' : Fp} (h : a * b' = 0) (ha : a = 1) : b' = 0 := by rw [ha] at h; grind
theorem fp_sub_zero_eq {a b' : Fp} (h : a - b' = 0) : a = b' := by grind

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal NodeV3.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

theorem usesLen (hC : NodeCtx tr s ℓ fl) {n : Nat} (hn : tr.cell T_NODE s nid = ((n : Nat) : Fp)) (hnP : n < P) :
    (nodeSOf tr pub s ℓ).uses.length = (edgesOf3 n (nodeSOf tr pub s ℓ)).length := by
  rw [← nodeEdgesAll hL hC hn hnP]; simp [nodeSOf]

set_option maxHeartbeats 1000000 in
theorem resOkNode (hC : NodeCtx tr s ℓ fl) {n : Nat} (hn : tr.cell T_NODE s nid = ((n : Nat) : Fp)) (hnP : n < P) :
    (nodeSOf tr pub s ℓ).resOk n := by
  obtain ⟨hr0, ha0⟩ := nodeStart hL hC
  have T := typeSumNat hL hr0 ha0
  have G := linkGates hL hr0
  simp only at G
  obtain ⟨-, -, -, -, -, -, -, Geext, -, -, -, -, -, -, -, -, -, G1, G2, G3, -, -⟩ := G
  rw [ha0] at G1
  have resN : tr.cell T_NODE s eext = 0 → cv tr T_NODE s res = n := by
    intro he; rw [he, show (1 : Fp) - 0 = 1 by decide, fp_one_mul'] at G1
    exact cv_of_eq ((fp_sub_zero_eq G1).trans hn) hnP
  unfold NodeS3.resOk nodeSOf
  simp only
  by_cases h2 : cv tr T_NODE s te = 1
  · have ht := of_cv_one h2
    have htl : cv tr T_NODE s tl ≠ 1 := by omega
    obtain ⟨hh1, hnk, hfl, -, -, -, -, -, sC, -⟩ := extFields hL hC ht
    have hm : (5 + cv tr T_NODE s hplen, 32) ∈ fl := hfl ▸ (by simp [extFL])
    obtain ⟨Krv, Kres, Kdead, Klast, -, -⟩ := extKid hL hC ht (pub := pub) hm sC
    unfold nodeVOf; rw [if_neg htl, if_pos h2]
    have bo := cvb hL hr0 (x := odd) (by simp [boolCols])
    have bk := cvb hL hr0 (x := nokey) (by simp [boolCols])
    by_cases hee : cv tr T_NODE s nokey = 1 ∧ cv tr T_NODE s odd = 0
    · -- empty-key extension
      have hE : tr.cell T_NODE s eext = 1 := by
        rw [Geext, ht, of_cv_one hee.1, of_cv_zero hee.2]; decide
      have hk : keyNibs tr s = [] := by
        unfold keyNibs keyPairs
        rw [hnk.1 (of_cv_one hee.1), if_neg (by omega)]; simp
      rw [hk]
      unfold kidOf
      by_cases hv : cv tr T_NODE (s + (5 + cv tr T_NODE s hplen)) rv = 1
      · rw [if_pos hv]
        simp only
        have hx : tr.cell T_NODE s xrv = 1 := of_cv_one (by omega)
        rw [hE, hx, fp_one_mul', fp_one_mul'] at G3
        rw [← Kres]; unfold cv; rw [fp_sub_zero_eq G3]
      · rw [if_neg hv]
        simp only
        have hx : tr.cell T_NODE s xrv = 0 := of_cv_zero (by omega)
        rw [hE, hx, show (1 : Fp) - 0 = 1 by decide, fp_one_mul', fp_one_mul'] at G2
        exact cv_of_eq ((fp_sub_zero_eq G2).trans hn) hnP
    · have hE : tr.cell T_NODE s eext = 0 := by
        rw [Geext, ht]
        rcases isBool hL hr0 (x := nokey) (by simp [boolCols]) with hk | hk <;>
          rcases isBool hL hr0 (x := odd) (by simp [boolCols]) with ho | ho
        · rw [hk]; exact fp_mul3_z1 _
        · rw [hk]; exact fp_mul3_z1 _
        · exact absurd ⟨cv_one hk, cv_zero ho⟩ hee
        · rw [ho]; exact fp_mul3_z2 _
      have hk : keyNibs tr s ≠ [] := by
        intro h; have := congrArg List.length h; rw [keyNibs_length] at this; simp at this
        apply hee; constructor
        · have : cv tr T_NODE s hplen = 1 := by omega
          exact cv_one (hnk.2 this)
        · omega
      rcases hkk : keyNibs tr s with _ | ⟨x, rest⟩
      · exact absurd hkk hk
      · exact resN hE
  · have hE : tr.cell T_NODE s eext = 0 := by
      rw [Geext, of_cv_zero (show cv tr T_NODE s te = 0 by
        have := cvb hL hr0 (x := te) (by simp [boolCols]); omega)]; grind
    unfold nodeVOf
    by_cases h1 : cv tr T_NODE s tl = 1
    · rw [if_pos h1]; exact resN hE
    · rw [if_neg h1, if_neg h2]; exact resN hE

end ZkFormal.NearV3.NodeProof3
