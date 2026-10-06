import ZkFormal.NearV3.Extract.Node.Edge

/-!
# ZkFormal.Near.Extract.NodeSlot — the child slot of a branch window
-/

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3 ZkFormal.Near

theorem evalSumNat (tr : Trace Fp) (r : Nat) (pub : List Fp) (l : List Nat) (f : Nat → Expr) (g : Nat → Nat)
    (h : ∀ i ∈ l, (f i).eval tr T_NODE r pub = ((g i : Nat) : Fp)) :
    (sum (l.map f)).eval tr T_NODE r pub = (((l.map g).sum : Nat) : Fp) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, eval_sum_cons, List.sum_cons, natCast_add]
    rw [h a (by simp), ih (fun i hi => h i (by simp [hi]))]

theorem sum_le_len (l : List Nat) (g : Nat → Nat) (h : ∀ i ∈ l, g i ≤ 1) : (l.map g).sum ≤ l.length := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; have := h a (by simp)
                   have := ih (fun i hi => h i (by simp [hi])); omega

theorem le_sum_of_mem' {l : List Nat} {x : Nat} (h : x ∈ l) : x ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    simp only [List.mem_cons] at h; simp only [List.sum_cons]
    rcases h with rfl | h
    · omega
    · have := ih h; omega

theorem sum_eq_zero' {l : List Nat} (h : ∀ x ∈ l, x = 0) : l.sum = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.sum_cons]; rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

theorem oneHot_of_sum (J : Nat → Nat) : ∀ n, (∀ i, i < n → J i ≤ 1) → ((List.range n).map J).sum = 1 →
    ∃ i0, i0 < n ∧ J i0 = 1 ∧ ∀ i, i < n → i ≠ i0 → J i = 0
  | 0, _, h => by simp at h
  | n + 1, hb, h => by
    rw [List.range_succ, List.map_append, List.sum_append] at h
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at h
    have hn := hb n (by omega)
    by_cases hJ : J n = 1
    · refine ⟨n, by omega, hJ, fun i hi hne => ?_⟩
      have hz : ((List.range n).map J).sum = 0 := by omega
      have : ∀ x ∈ (List.range n).map J, x = 0 := by
        intro x hx; have := le_sum_of_mem' hx; omega
      exact this (J i) (List.mem_map.mpr ⟨i, List.mem_range.mpr (by omega), rfl⟩)
    · obtain ⟨i0, h1, h2, h3⟩ := oneHot_of_sum J n (fun i hi => hb i (by omega)) (by omega)
      exact ⟨i0, by omega, h2, fun i hi hne => by
        rcases Nat.lt_or_ge i n with h | h
        · exact h3 i h hne
        · have : i = n := by omega
          subst this; omega⟩

theorem sum_oneHot (J x : Nat → Nat) (n i0 : Nat) (hi0 : i0 < n) (h1 : J i0 = 1)
    (h0 : ∀ i, i < n → i ≠ i0 → J i = 0) : ((List.range n).map fun i => J i * x i).sum = x i0 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    by_cases hn : n = i0
    · subst hn
      have : ((List.range n).map fun i => J i * x i).sum = 0 := by
        have : ∀ y ∈ (List.range n).map (fun i => J i * x i), y = 0 := by
          intro y hy; rw [List.mem_map] at hy; obtain ⟨i, hi, rfl⟩ := hy
          rw [List.mem_range] at hi; rw [h0 i (by omega) (by omega)]; simp
        exact sum_eq_zero' this
      rw [this, h1]; simp
    · rw [ih (by omega) (fun i hi hne => h0 i (by omega) hne), h0 n (by omega) hn]; simp

theorem belowN_lt {tr : Trace Fp} {s j j' : Nat} (hj : j < j') (hbj : cv tr T_NODE s (bm j) = 1) :
    belowN tr s j < belowN tr s j' := by
  induction j' with
  | zero => omega
  | succ j' ih =>
    rw [belowN_succ]
    rcases Nat.lt_or_ge j j' with h | h
    · have := ih h; omega
    · have : j = j' := by omega
      subst this; omega

/-- Distinct set bits have distinct ranks. -/
theorem belowN_inj {tr : Trace Fp} {s j j' : Nat} (hbj : cv tr T_NODE s (bm j) = 1) (hbj' : cv tr T_NODE s (bm j') = 1)
    (h : belowN tr s j = belowN tr s j') : j = j' := by
  rcases Nat.lt_trichotomy j j' with hl | hl | hl
  · have := belowN_lt hl hbj; omega
  · exact hl
  · have := belowN_lt hl hbj'; omega

end ZkFormal.NearV3.NodeProof3

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3 ZkFormal.Near

theorem jj_bool {i : Nat} (hi : i < 16) : jj i ∈ boolCols := by
  unfold boolCols; simp only [List.mem_append, List.mem_map, List.mem_range]
  exact Or.inl (Or.inl (Or.inr ⟨i, hi, rfl⟩))

theorem bm_const_mem {i : Nat} (hi : i < 16) : bm i ∈ nodeConst := by
  unfold nodeConst; simp only [List.mem_append, List.mem_map, List.mem_range]; exact Or.inl (Or.inr ⟨i, hi, rfl⟩)

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal NodeV3.table tr T_NODE pub)
include hL
variable {s ℓ : Nat} {fl : List (Nat × Nat)}

/-- The slot of a branch window: the `w`-th present child. -/
theorem slotOfWin (hC : NodeCtx tr s ℓ fl) {o : Nat} (hm : (o, 32) ∈ fl) (sC : tr.cell T_NODE (s + o) sCH = 1)
    (hbr : tr.cell T_NODE s tb1 + tr.cell T_NODE s tb2 = 1) {w : Nat} (hw : tr.cell T_NODE (s + o) Node.w = ((w : Nat) : Fp))
    (hwP : w < 17) :
    ∃ j, j < 16 ∧ cv tr T_NODE s (bm j) = 1 ∧ belowN tr s j = w ∧ jIdxE.eval tr T_NODE (s + o) pub = ((j : Nat) : Fp) := by
  have hoℓ : o < ℓ := by have := (hC.fields.field _ hm); simp at this; have := this.1.pos; omega
  have hr : s + o < tr.height T_NODE := by have := hC.bound; omega
  have cst := fun x (hx : x ∈ nodeConst) => segConst hL hC hx hoℓ
  have hB : ∀ i, i < 16 → cv tr T_NODE (s + o) (bm i) = cv tr T_NODE s (bm i) := fun i hi => cvC hL hC (bm_const_mem hi) hoℓ
  obtain ⟨S1, S2, S3⟩ := (winSlot hL hr sC (pub := pub)).1 (by
    simp only [isBr, eval_add, eval_c]; rw [cst tb1 (by simp [nodeConst]), cst tb2 (by simp [nodeConst]), hbr])
  have Jb : ∀ i, i < 16 → cv tr T_NODE (s + o) (jj i) ≤ 1 := fun i hi => cvb hL hr (jj_bool hi)
  have Bb : ∀ i, i < 16 → cv tr T_NODE (s + o) (bm i) ≤ 1 := fun i hi => cvb hL hr (bm_bool hi)
  have mr : ∀ {i}, i ∈ List.range 16 → i < 16 := fun h => List.mem_range.mp h
  -- Σ jj = 1
  rw [evalSumNat tr (s + o) pub _ (fun i => c (jj i)) (fun i => cv tr T_NODE (s + o) (jj i))
    (fun i _ => by rw [eval_c, cell_eq_cast])] at S1
  have hs1 := sum_le_len (List.range 16) _ (fun i hi => Jb i (mr hi))
  rw [List.length_range] at hs1
  have N1 := fp_cast_eq (b := 1) (by unfold P; omega) (by unfold P; omega) (S1.trans rfl)
  obtain ⟨i0, hi0, hJ1, hJ0⟩ := oneHot_of_sum _ 16 Jb N1
  -- Σ jj·bm = bm i0
  rw [evalSumNat tr (s + o) pub _ (fun i => Expr.mul (c (jj i)) (c (bm i)))
    (fun i => cv tr T_NODE (s + o) (jj i) * cv tr T_NODE (s + o) (bm i))
    (fun i _ => by rw [eval_mul, eval_c, eval_c, cell_eq_cast tr T_NODE (s + o) (jj i), cell_eq_cast tr T_NODE (s + o) (bm i),
      natCast_mul])] at S2
  rw [sum_oneHot _ _ 16 i0 hi0 hJ1 hJ0] at S2
  have hb1 : cv tr T_NODE (s + o) (bm i0) = 1 :=
    fp_cast_eq (b := 1) (by have := Bb i0 hi0; unfold P; omega) (by unfold P; omega) (S2.trans rfl)
  -- belowE = belowN i0
  have hbe : ∀ i, (sum ((List.range i).map fun i' => c (bm i'))).eval tr T_NODE (s + o) pub =
      ((belowN tr (s + o) i : Nat) : Fp) := fun i =>
    evalSumNat tr (s + o) pub _ (fun i' => c (bm i')) _ (fun i' _ => by rw [eval_c, cell_eq_cast])
  simp only [belowE] at S3
  rw [evalSumNat tr (s + o) pub _ _ (fun i => cv tr T_NODE (s + o) (jj i) * belowN tr (s + o) i)
    (fun i _ => by rw [eval_mul, eval_c, hbe, cell_eq_cast tr T_NODE (s + o) (jj i), natCast_mul])] at S3
  rw [sum_oneHot _ _ 16 i0 hi0 hJ1 hJ0, hw] at S3
  have hbl : belowN tr (s + o) i0 ≤ 16 := by
    have := sum_le_len (List.range i0) (fun i => cv tr T_NODE (s + o) (bm i)) (fun i hi => Bb i (by
      have := List.mem_range.mp hi; omega))
    unfold belowN; rw [List.length_range] at this; omega
  have N3 := fp_cast_eq (by unfold P; omega) (by unfold P; omega) S3
  have hbs : belowN tr (s + o) i0 = belowN tr s i0 := by
    unfold belowN; congr 1; apply List.map_congr_left; intro i hi; exact hB i (by have := List.mem_range.mp hi; omega)
  -- jIdx = i0
  refine ⟨i0, hi0, by rw [← hB i0 hi0]; exact hb1, by rw [← hbs]; exact N3, ?_⟩
  simp only [jIdxE]
  rw [evalSumNat tr (s + o) pub _ _ (fun i => cv tr T_NODE (s + o) (jj i) * i)
    (fun i _ => by rw [eval_smul, eval_c, cell_eq_cast tr T_NODE (s + o) (jj i), ← natCast_mul, Nat.mul_comm])]
  rw [sum_oneHot _ _ 16 i0 hi0 hJ1 hJ0]

end ZkFormal.NearV3.NodeProof3
