import ZkFormal.NearV3.Extract.WalkProof

/-!
# ZkFormal.NearV3.Extract.WalkProof2 — the `walkV3` view: rows, traffic, `walk3_view`
-/

namespace ZkFormal.NearV3.WalkProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.WalkV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- Row mode as a natural. -/
def modeOf (tr : Trace Fp) (tt q : Nat) : Nat :=
  if tr.cell tt q mS = 1 then 0 else if tr.cell tt q mK = 1 then 1 else if tr.cell tt q mB = 1 then 2 else 3

def edgeAt (tr : Trace Fp) (tt q : Nat) : Msg :=
  [nN, nI, nib, nN2, nI2, ek].map fun x => (tr.cell tt q x).toNat

def bmAt (tr : Trace Fp) (tt q : Nat) : Nat := bitsVal (fun b => cv tr tt q (bmb b)) 0 16

def stepAt (tr : Trace Fp) (tt q : Nat) : WStep3 :=
  ⟨modeOf tr tt q, (tr.cell tt q sym).toNat, edgeAt tr tt q, (tr.cell tt q u).toNat, bmAt tr tt q,
    (tr.cell tt q hv).toNat, (tr.cell tt q ub).toNat⟩

def walkOfSeg (tr : Trace Fp) (tt : Nat) (p : Nat × Nat) : WalkR :=
  ⟨(tr.cell tt p.1 w).toNat, (tr.cell tt p.1 tau).toNat, (List.range p.2).map fun j => stepAt tr tt (p.1 + j)⟩

/-- One-hot modes on an active row. -/
theorem modes_cases (hL : TableLocal WalkV3.table tr tt pub) {q : Nat} (hq : q < tr.height tt)
    (ha : tr.cell tt q act = 1) :
    (tr.cell tt q mS = 1 ∧ tr.cell tt q mK = 0 ∧ tr.cell tt q mB = 0 ∧ tr.cell tt q mD = 0) ∨
    (tr.cell tt q mS = 0 ∧ tr.cell tt q mK = 1 ∧ tr.cell tt q mB = 0 ∧ tr.cell tt q mD = 0) ∨
    (tr.cell tt q mS = 0 ∧ tr.cell tt q mK = 0 ∧ tr.cell tt q mB = 1 ∧ tr.cell tt q mD = 0) ∨
    (tr.cell tt q mS = 0 ∧ tr.cell tt q mK = 0 ∧ tr.cell tt q mB = 0 ∧ tr.cell tt q mD = 1) := by
  have hm := (rowFacts hL hq).2.1
  rw [ha] at hm
  rcases isBool hL hq bc_mS with h1 | h1 <;> rcases isBool hL hq bc_mK with h2 | h2 <;>
    rcases isBool hL hq bc_mB with h3 | h3 <;> rcases isBool hL hq bc_mD with h4 | h4 <;>
    rw [h1, h2, h3, h4] at hm <;> first | (exfalso; revert hm; decide) | simp [h1, h2, h3, h4]

theorem modeOf_le (q : Nat) : modeOf tr tt q ≤ 3 := by
  unfold modeOf
  by_cases h1 : tr.cell tt q mS = 1
  · simp [h1]
  · by_cases h2 : tr.cell tt q mK = 1
    · simp [h1, h2]
    · by_cases h3 : tr.cell tt q mB = 1 <;> simp [h1, h2, h3]

theorem mode0 {q : Nat} (h : modeOf tr tt q = 0) : tr.cell tt q mS = 1 := by
  unfold modeOf at h
  by_cases h1 : tr.cell tt q mS = 1
  · exact h1
  · by_cases h2 : tr.cell tt q mK = 1
    · simp [h1, h2] at h
    · by_cases h3 : tr.cell tt q mB = 1 <;> simp [h1, h2, h3] at h

theorem sum_le_len {α : Type} : ∀ (l : List α) (f : α → Nat), (∀ x ∈ l, f x ≤ 1) → (l.map f).sum ≤ l.length
  | [], _, _ => by simp
  | a :: l, f, h => by
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := h a (by simp); have := sum_le_len l f (fun x hx => h x (by simp [hx])); omega

theorem toNat01 {a : Fp} (h : a = 0 ∨ a = 1) : a.toNat ≤ 1 := by
  rcases h with rfl | rfl <;> decide

theorem toNat_ne {a b : Fp} (h : a ≠ b) : a.toNat ≠ b.toNat := by
  intro e; apply h; rw [← Fp.ofNat_toNat a, ← Fp.ofNat_toNat b, e]

/-- `StepOk` of an active row. -/
theorem stepOk (hL : TableLocal WalkV3.table tr tt pub) {q : Nat} (hq : q < tr.height tt)
    (ha : tr.cell tt q act = 1) (isL : Bool) (hwe : tr.cell tt q we = if isL then 1 else 0) :
    StepOk (stepAt tr tt q) isL := by
  obtain ⟨hS, hK, hB, hsum, hidx, hbit⟩ := modeFacts hL hq
  have hrf := rowFacts hL hq
  have t0 : (0 : Fp).toNat = 0 := rfl
  have t1 : (1 : Fp).toNat = 1 := rfl
  refine ⟨?_, by simp [stepAt, edgeAt], fun hm => ?_, fun hm => ?_, fun hm => ?_, fun hl => ?_⟩
  · exact modeOf_le q
  · have hs1 : tr.cell tt q mS = 1 := mode0 hm
    obtain ⟨hn, hk0, hk1⟩ := hS hs1
    refine ⟨by simp [stepAt, edgeAt, hn], fun hl => ?_, fun hl => ?_⟩
    · subst hl; simp at hwe
      have := hk0 hwe
      have : tr.cell tt q ek = 0 ∨ tr.cell tt q ek = 1 := by grind
      rcases this with h | h <;> simp [stepAt, edgeAt, h, t0, t1, EK_DOWN, EK_KEY]
    · subst hl; simp at hwe
      have := hk1 hwe
      simp only [stepAt, edgeAt, List.map_cons, List.map_nil, List.getD_eq_getElem?_getD]
      simp [this, EK_VAL, natCast_eq, Fp.toNat_ofNat, P]
  · have hk1 : tr.cell tt q mK = 1 ∧ tr.cell tt q mS = 0 := by
      change modeOf tr tt q = 1 at hm
      rcases modes_cases hL hq ha with h | h | h | h <;> simp [modeOf, h] at hm ⊢ <;> exact h.2.1
    obtain ⟨he, hinv⟩ := hK hk1.1
    refine ⟨?_, ?_⟩
    · have : tr.cell tt q ek = (EK_KEY : Nat) ∨ tr.cell tt q ek = (EK_LEND : Nat) := by
        have := he; grind
      rcases this with h | h <;> simp [stepAt, edgeAt, h, EK_KEY, EK_LEND, natCast_eq, Fp.toNat_ofNat, P]
    · have hne : tr.cell tt q nib ≠ tr.cell tt q sym := by
        intro e; rw [e] at hinv; grind
      simpa [stepAt, edgeAt] using toNat_ne hne
  · have hb1 : tr.cell tt q mB = 1 ∧ tr.cell tt q mS = 0 ∧ tr.cell tt q mK = 0 := by
      change modeOf tr tt q = 2 at hm
      rcases modes_cases hL hq ha with h | h | h | h <;> simp [modeOf, h] at hm ⊢ <;> exact ⟨h.2.2.1, h.1, h.2.1⟩
    obtain ⟨hn0, hhv⟩ := hB hb1.1
    have hbits : ∀ b, b < 16 → cv tr tt q (bmb b) ≤ 1 := fun b hb => cv_bool (isBool hL hq (bc_bmb b hb))
    refine ⟨by simp [stepAt, edgeAt, hn0, t0], ?_, toNat01 (isBool hL hq bc_hv), fun hl => ?_, fun hl => ?_⟩
    · simpa [stepAt, bmAt] using bitsVal_lt _ 0 16 (fun b hb => by simpa using hbits b hb)
    · subst hl; simp at hwe; simp [stepAt, hhv hwe, t0]
    · subst hl; simp at hwe
      rw [hb1.1, hwe] at hsum hidx
      have hsel : ∀ j, j < 16 → (c (sel j)).eval tr tt q pub = ((cv tr tt q (sel j) : Nat) : Fp) :=
        fun j _ => by simp [cell_eq_cast]
      rw [selSum, evsum 16 _ _ hsel] at hsum
      have hs1 : ((List.range 16).map fun j => cv tr tt q (sel j)).sum = 1 := by
        have hle : ((List.range 16).map fun j => cv tr tt q (sel j)).sum ≤ 16 := by
          have := sum_le_len (List.range 16) (fun j => cv tr tt q (sel j)) (fun j hj =>
            cv_bool (isBool hL hq (bc_sel j (List.mem_range.1 hj))))
          simpa using this
        apply ofNat_inj (by unfold P; omega) (by unfold P; omega)
        rw [hsum]; grind
      obtain ⟨j0, hj0, hsel0, hsidx, hsbit⟩ := onehot 16 (fun j => cv tr tt q (sel j))
        (fun j hj => cv_bool (isBool hL hq (bc_sel j hj))) hs1
      have hidx' : ∀ j, j < 16 → (smul j (c (sel j))).eval tr tt q pub = ((j * cv tr tt q (sel j) : Nat) : Fp) :=
        fun j _ => by simp [cell_eq_cast, natCast_mul]
      rw [selIdx, evsum 16 _ _ hidx', hsidx] at hidx
      have hsym : tr.cell tt q sym = ((j0 : Nat) : Fp) := by grind
      have hbit' : ∀ j, j < 16 → (Expr.mul (c (sel j)) (c (bmb j))).eval tr tt q pub =
          ((cv tr tt q (sel j) * cv tr tt q (bmb j) : Nat) : Fp) := fun j _ => by simp [cell_eq_cast, natCast_mul]
      rw [selBit, evsum 16 _ _ hbit', hsbit (fun j => cv tr tt q (bmb j))] at hbit
      have hb0 : cv tr tt q (bmb j0) = 0 := by
        have := hbits j0 hj0
        apply ofNat_inj (by unfold P; omega) (by unfold P; omega)
        rw [hbit]; rfl
      have hsymN : (tr.cell tt q sym).toNat = j0 := by
        rw [hsym, toNat_natCast, Nat.mod_eq_of_lt (by unfold P; omega)]
      refine ⟨by simp [stepAt, hsymN, hj0], ?_⟩
      simp only [stepAt, bmAt, hsymN]
      rw [bitsVal_bit _ 16 j0 (fun i hi => hbits i hi) hj0, hb0]
  · subst hl; simp at hwe
    have := (hrf.2.2.2 hwe).2.1
    simp [stepAt, this, natCast_eq, Fp.toNat_ofNat, SYM_END, P]

/-! ## Row traffic -/

theorem multNat1 (x : Nat) (q : Nat) :
    Interaction.multNat.go tr tt q pub [c x] 0 = if tr.cell tt q x = 1 then 1 else 0 := by
  simp only [Interaction.multNat.go, eval_c]
  by_cases h : tr.cell tt q x = 1 <;> simp [h]

theorem multNatSK (q : Nat) :
    Interaction.multNat.go tr tt q pub [.add (c mS) (c mK)] 0 =
      if tr.cell tt q mS + tr.cell tt q mK = 1 then 1 else 0 := by
  simp only [Interaction.multNat.go, eval_add, eval_c]
  by_cases h : tr.cell tt q mS + tr.cell tt q mK = 1 <;> simp [h]

def cellsE (tr : Trace Fp) (tt q : Nat) (uu : Fp) : List Fp :=
  [tr.cell tt q nN, tr.cell tt q nI, tr.cell tt q nib, tr.cell tt q nN2, tr.cell tt q nI2, tr.cell tt q ek, uu]

def cellsB (tr : Trace Fp) (tt q : Nat) (pub : List Fp) (uu : Fp) : List Fp :=
  [tr.cell tt q nN, bmE.eval tr tt q pub, tr.cell tt q hv, uu]

theorem rowT (q : Nat) (b : Nat) (sd : Bool) :
    rowTraffic WalkV3.interactions tr tt q pub b sd =
      (if b = B_KEYNIB ∧ sd = false ∧ tr.cell tt q gK = 1 then
        [[tr.cell tt q w, tr.cell tt q t, tr.cell tt q sym, tr.cell tt q we]] else []) ++
      (if b = B_EDGE ∧ sd = false ∧ tr.cell tt q mS + tr.cell tt q mK = 1 then
        [cellsE tr tt q (tr.cell tt q u)] else []) ++
      (if b = B_EDGE ∧ sd = true ∧ tr.cell tt q mS + tr.cell tt q mK = 1 then
        [cellsE tr tt q (tr.cell tt q u + 1)] else []) ++
      (if b = B_BMAP ∧ sd = false ∧ tr.cell tt q mB = 1 then [cellsB tr tt q pub (tr.cell tt q ub)] else []) ++
      (if b = B_BMAP ∧ sd = true ∧ tr.cell tt q mB = 1 then [cellsB tr tt q pub (tr.cell tt q ub + 1)] else []) ++
      (if b = B_FINAL ∧ sd = true ∧ tr.cell tt q we = 1 then
        [[tr.cell tt q w, tr.cell tt q tau, tr.cell tt q fk, tr.cell tt q kk]] else []) := by
  simp only [rowTraffic, WalkV3.interactions, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    Dsl.recv, Dsl.send, Interaction.multNat, multNat1, multNatSK, Interaction.msgVal, WalkV3.edge, WalkV3.bmap,
    List.map_cons, List.map_nil, eval_c, eval_add, eval_k, cellsE, cellsB, List.append_assoc]
  have ap : ∀ {a b c d : List (List Fp)}, a = b → c = d → a ++ c = b ++ d := by
    intro a b c d h1 h2; rw [h1, h2]
  refine ap ?_ (ap ?_ (ap ?_ (ap ?_ (ap ?_ ?_)))) <;> (split <;> split <;> simp_all [eq_comm]) <;> grind

end ZkFormal.NearV3.WalkProof

namespace ZkFormal.NearV3.WalkProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.WalkV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem filter_map_fm {α β : Type} (q : α → Bool) (f : α → β) :
    ∀ l : List α, (l.filter q).map f = l.flatMap fun a => if q a then [f a] else []
  | [] => rfl
  | a :: l => by
    by_cases h : q a = true
    · simp [List.filter_cons, h, filter_map_fm q f l]
    · simp [List.filter_cons, h, filter_map_fm q f l]

theorem sk_iff (hL : TableLocal WalkV3.table tr tt pub) {q : Nat} (hq : q < tr.height tt)
    (ha : tr.cell tt q act = 1) :
    (tr.cell tt q mS + tr.cell tt q mK = 1 ↔ modeOf tr tt q ≤ 1) ∧ (tr.cell tt q mB = 1 ↔ modeOf tr tt q = 2) ∧
    (modeOf tr tt q = 0 ↔ tr.cell tt q mS = 1) := by
  rcases modes_cases hL hq ha with h | h | h | h <;> simp [modeOf, h] <;> grind

theorem cellsE_eq (q : Nat) (uu : Nat) :
    Msg.toFp ((stepAt tr tt q).edgeMsg uu) = cellsE tr tt q (Fp.ofNat uu) := by
  simp [Msg.toFp, WStep3.edgeMsg, stepAt, edgeAt, cellsE, Fp.ofNat_toNat]

theorem cellsB_eq (hL : TableLocal WalkV3.table tr tt pub) {q : Nat} (hq : q < tr.height tt) (uu : Nat) :
    Msg.toFp ((stepAt tr tt q).bmapMsg uu) = cellsB tr tt q pub (Fp.ofNat uu) := by
  have hb : (bmE).eval tr tt q pub = ((bmAt tr tt q : Nat) : Fp) := by
    unfold bmE bmAt
    exact eval_bits tr tt q pub bmb 0 16 (fun b hb => isBool hL hq (by simpa using bc_bmb b (by omega)))
  simp [Msg.toFp, WStep3.bmapMsg, stepAt, edgeAt, cellsB, Fp.ofNat_toNat, hb, natCast_eq]

theorem ite01 (p : Prop) [Decidable p] : (Fp.ofNat (if p then 1 else 0)) = (if p then 1 else 0 : Fp) := by
  split <;> rfl

theorem cellsE_eq' (q : Nat) :
    cellsE tr tt q (tr.cell tt q u) = Msg.toFp ((stepAt tr tt q).edgeMsg (stepAt tr tt q).u) := by
  rw [cellsE_eq]; simp [stepAt, Fp.ofNat_toNat]

theorem cellsE_eq1 (q : Nat) :
    cellsE tr tt q (tr.cell tt q u + 1) = Msg.toFp ((stepAt tr tt q).edgeMsg ((stepAt tr tt q).u + 1)) := by
  rw [cellsE_eq]; simp only [stepAt]; congr 1
  rw [← natCast_eq, natCast_add, natCast_eq (tr.cell tt q u).toNat, Fp.ofNat_toNat]; rfl

theorem cellsB_eq' (hL : TableLocal WalkV3.table tr tt pub) {q : Nat} (hq : q < tr.height tt) :
    cellsB tr tt q pub (tr.cell tt q ub) = Msg.toFp ((stepAt tr tt q).bmapMsg (stepAt tr tt q).ub) := by
  rw [cellsB_eq hL hq]; simp [stepAt, Fp.ofNat_toNat]

theorem cellsB_eq1 (hL : TableLocal WalkV3.table tr tt pub) {q : Nat} (hq : q < tr.height tt) :
    cellsB tr tt q pub (tr.cell tt q ub + 1) = Msg.toFp ((stepAt tr tt q).bmapMsg ((stepAt tr tt q).ub + 1)) := by
  rw [cellsB_eq hL hq]; simp only [stepAt]; congr 1
  rw [← natCast_eq, natCast_add, natCast_eq (tr.cell tt q ub).toNat, Fp.ofNat_toNat]; rfl

theorem segRecv (hL : TableLocal WalkV3.table tr tt pub) {s ℓ : Nat}
    (hseg : IsSeg (isOne tr tt act) (isOne tr tt ws) (isOne tr tt we) s ℓ) (hH : s + ℓ ≤ tr.height tt)
    (b : Nat) :
    (List.range' s ℓ).flatMap (fun q => rowTraffic WalkV3.interactions tr tt q pub b false) =
      (walkRecvs3 [walkOfSeg tr tt (s, ℓ)] b).map Msg.toFp := by
  obtain ⟨h2, hrow, -, -, -, -⟩ := segInfo hL hseg hH
  have hdKE : B_KEYNIB ≠ B_EDGE := by decide
  have hdKB : B_KEYNIB ≠ B_BMAP := by decide
  have hdEB : B_EDGE ≠ B_BMAP := by decide
  by_cases hE : b = B_EDGE
  · subst hE
    simp only [walkRecvs3, ite_true, walkOfSeg, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      filter_map_fm, List.flatMap_map, List.map_flatMap]
    rw [List.range'_eq_map_range, List.flatMap_map]
    apply flatMap_congr'
    intro j hj
    have hj' := List.mem_range.1 hj
    have ha := (hrow j hj').1
    rw [rowT]
    simp only [hdKE.symm, hdEB, false_and, if_false, List.nil_append, List.append_nil, true_and,
      Bool.false_eq_true, and_false, and_true]
    by_cases hm : modeOf tr tt (s + j) ≤ 1
    · rw [if_pos ((sk_iff hL (by omega) ha).1.2 hm), cellsE_eq']
      have hm' : (stepAt tr tt (s + j)).mode ≤ 1 := hm
      simp [hm']
    · rw [if_neg (fun h => hm ((sk_iff hL (by omega) ha).1.1 h))]
      have hm' : ¬ (stepAt tr tt (s + j)).mode ≤ 1 := hm
      simp [hm']
  · by_cases hB : b = B_BMAP
    · subst hB
      simp only [walkRecvs3, if_neg hdEB.symm, ite_true, walkOfSeg, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, filter_map_fm, List.flatMap_map, List.map_flatMap]
      rw [List.range'_eq_map_range, List.flatMap_map]
      apply flatMap_congr'
      intro j hj
      have hj' := List.mem_range.1 hj
      have ha := (hrow j hj').1
      rw [rowT]
      simp only [hdKB.symm, hdEB.symm, false_and, if_false, List.nil_append, List.append_nil, true_and,
        Bool.false_eq_true, and_false, and_true]
      by_cases hm : modeOf tr tt (s + j) = 2
      · rw [if_pos ((sk_iff hL (by omega) ha).2.1.2 hm), cellsB_eq' hL (by omega)]
        have hm' : (stepAt tr tt (s + j)).mode = 2 := hm
        simp [hm']
      · rw [if_neg (fun h => hm ((sk_iff hL (by omega) ha).2.1.1 h))]
        have hm' : ¬ (stepAt tr tt (s + j)).mode = 2 := hm
        simp [hm']
    · by_cases hK : b = B_KEYNIB
      · subst hK
        simp only [walkRecvs3, if_neg hdKE, if_neg hdKB, ite_true, walkOfSeg,
          List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_map, List.length_range]
        have hs : List.range' s ℓ = [s] ++ List.range' (s + 1) (ℓ - 1) := by
          rw [show ℓ = 1 + (ℓ - 1) by omega, ← List.range'_append_1]; simp
        rw [hs, List.flatMap_append]
        have h0 := hrow 0 (by omega)
        rw [Nat.add_zero] at h0
        rw [List.flatMap_singleton, rowT, h0.2.2.2.2.1]
        simp only [if_pos rfl, fp_zero_ne_one, and_false, if_false, hdKE, hdKB, false_and, List.nil_append,
          List.append_nil]
        rw [flatMap_range'_single _ (fun j => [tr.cell tt (s + 1 + j) w, tr.cell tt (s + 1 + j) t,
          tr.cell tt (s + 1 + j) sym, tr.cell tt (s + 1 + j) we]) (s + 1) (ℓ - 1) (fun j hj => by
            have := hrow (j + 1) (by have := h2; omega)
            rw [show s + (j + 1) = s + 1 + j by omega] at this
            rw [rowT, this.2.2.2.2.1, if_neg (Nat.succ_ne_zero j)]; simp [hdKE, hdKB])]
        simp only [List.map_map]
        apply List.map_congr_left; intro j hj
        rw [List.mem_range] at hj
        have := hrow (j + 1) (by omega)
        rw [show s + (j + 1) = s + 1 + j by omega] at this
        obtain ⟨-, hr, -, hw, -, ht⟩ := this
        simp only [Function.comp, Msg.toFp, List.map_cons, List.map_nil, WalkR.step, List.getD_eq_getElem?_getD,
          List.getElem?_map, List.getElem?_range (show j + 1 < ℓ by omega), Option.map_some, Option.getD_some,
          stepAt, Fp.ofNat_toNat]
        rw [hr, hw, ht (by omega), ite01]
        simp [show j + 1 - 1 = j by omega, show s + (j + 1) = s + 1 + j by omega, natCast_eq,
          show (j + 1 + 1 = ℓ) ↔ (j + 2 = ℓ) by omega]
      · rw [flatMap_range'_nil _ _ _ (fun j _ => by rw [rowT]; simp [hE, hB, hK])]
        simp [walkRecvs3, hE, hB, hK]

end ZkFormal.NearV3.WalkProof

namespace ZkFormal.NearV3.WalkProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.WalkV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem segSend (hL : TableLocal WalkV3.table tr tt pub) {s ℓ : Nat}
    (hseg : IsSeg (isOne tr tt act) (isOne tr tt ws) (isOne tr tt we) s ℓ) (hH : s + ℓ ≤ tr.height tt)
    (b : Nat) :
    (List.range' s ℓ).flatMap (fun q => rowTraffic WalkV3.interactions tr tt q pub b true) =
      (walkSends3 [walkOfSeg tr tt (s, ℓ)] b).map Msg.toFp := by
  obtain ⟨h2, hrow, -, -, -, -⟩ := segInfo hL hseg hH
  have hdFE : B_FINAL ≠ B_EDGE := by decide
  have hdFB : B_FINAL ≠ B_BMAP := by decide
  have hdEB : B_EDGE ≠ B_BMAP := by decide
  have hdKE : B_KEYNIB ≠ B_EDGE := by decide
  have hdKB : B_KEYNIB ≠ B_BMAP := by decide
  have hdKF : B_KEYNIB ≠ B_FINAL := by decide
  by_cases hE : b = B_EDGE
  · subst hE
    simp only [walkSends3, ite_true, walkOfSeg, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      filter_map_fm, List.flatMap_map, List.map_flatMap]
    rw [List.range'_eq_map_range, List.flatMap_map]
    apply flatMap_congr'
    intro j hj
    have hj' := List.mem_range.1 hj
    have ha := (hrow j hj').1
    rw [rowT]
    simp only [hdKE.symm, hdEB, hdFE.symm, false_and, if_false, List.nil_append, List.append_nil, true_and,
      Bool.false_eq_true, and_false, and_true]
    by_cases hm : modeOf tr tt (s + j) ≤ 1
    · rw [if_pos ((sk_iff hL (by omega) ha).1.2 hm), cellsE_eq1]
      have hm' : (stepAt tr tt (s + j)).mode ≤ 1 := hm
      simp [hm']
    · rw [if_neg (fun h => hm ((sk_iff hL (by omega) ha).1.1 h))]
      have hm' : ¬ (stepAt tr tt (s + j)).mode ≤ 1 := hm
      simp [hm']
  · by_cases hB : b = B_BMAP
    · subst hB
      simp only [walkSends3, if_neg hdEB.symm, ite_true, walkOfSeg, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, filter_map_fm, List.flatMap_map, List.map_flatMap]
      rw [List.range'_eq_map_range, List.flatMap_map]
      apply flatMap_congr'
      intro j hj
      have hj' := List.mem_range.1 hj
      have ha := (hrow j hj').1
      rw [rowT]
      simp only [hdKB.symm, hdEB.symm, hdFB.symm, false_and, if_false, List.nil_append, List.append_nil, true_and,
        Bool.false_eq_true, and_false, and_true]
      by_cases hm : modeOf tr tt (s + j) = 2
      · rw [if_pos ((sk_iff hL (by omega) ha).2.1.2 hm), cellsB_eq1 hL (by omega)]
        have hm' : (stepAt tr tt (s + j)).mode = 2 := hm
        simp [hm']
      · rw [if_neg (fun h => hm ((sk_iff hL (by omega) ha).2.1.1 h))]
        have hm' : ¬ (stepAt tr tt (s + j)).mode = 2 := hm
        simp [hm']
    · by_cases hF : b = B_FINAL
      · subst hF
        simp only [walkSends3, if_neg hdFE, if_neg hdFB, ite_true, walkOfSeg,
          List.map_cons, List.map_nil, List.length_map, List.length_range]
        have hs : List.range' s ℓ = List.range' s (ℓ - 1) ++ [s + (ℓ - 1)] := by
          have := range'_succ' s (ℓ - 1); rwa [Nat.sub_add_cancel (by omega : 1 ≤ ℓ)] at this
        rw [hs, List.flatMap_append, flatMap_range'_nil _ s (ℓ - 1) (fun j (hj : j < ℓ - 1) => by
          rw [rowT, (hrow j (by omega)).2.2.2.1, if_neg (show ¬ j + 1 = ℓ by omega)]
          simp [hdKF.symm, hdFE, hdFB])]
        have hl := hrow (ℓ - 1) (by omega)
        have hq : s + (ℓ - 1) < tr.height tt := by omega
        have hwe : tr.cell tt (s + (ℓ - 1)) we = 1 := by rw [hl.2.2.2.1, if_pos (by omega)]
        obtain ⟨-, -, hfk, hkk⟩ := (rowFacts hL hq).2.2.2 hwe
        rw [List.flatMap_singleton, rowT]
        simp only [hdKF.symm, hdFE, hdFB, false_and, if_false, List.nil_append, true_and, hwe, if_true,
          and_self, List.append_nil]
        simp only [Msg.toFp, List.map_cons, List.map_nil, WalkR.fk, WalkR.k, WalkR.last, WalkR.step,
          List.getD_eq_getElem?_getD, List.length_map, List.length_range,
          List.getElem?_map, List.getElem?_range (show ℓ - 1 < ℓ by omega), Option.map_some,
          Option.getD_some, Fp.ofNat_toNat, hfk, hkk]
        rw [hl.2.1, hl.2.2.1]
        have ha := hl.1
        have o0 : Fp.ofNat 0 = 0 := rfl
        have o1 : Fp.ofNat 1 = 1 := rfl
        rcases modes_cases hL hq ha with h | h | h | h <;>
          simp [stepAt, modeOf, h, FK_VAL, FK_ABS, edgeAt, Fp.ofNat_toNat, o0, o1] <;> grind
      · rw [flatMap_range'_nil _ _ _ (fun j _ => by rw [rowT]; simp [hE, hB, hF])]
        simp [walkSends3, hE, hB, hF]

end ZkFormal.NearV3.WalkProof

namespace ZkFormal.NearV3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near WalkProof

theorem walkSends3_flat (ws : List WalkR) (b : Nat) :
    walkSends3 ws b = ws.flatMap fun w => walkSends3 [w] b := by
  unfold walkSends3; split
  · simp
  · split
    · simp
    · split
      · simp [map_eq_flatMap]
      · simp

theorem walkRecvs3_flat (ws : List WalkR) (b : Nat) :
    walkRecvs3 ws b = ws.flatMap fun w => walkRecvs3 [w] b := by
  unfold walkRecvs3; split
  · simp
  · split
    · simp
    · split <;> simp

/-- **The `walkV3` view.** -/
theorem walk3_view : WalkV3ViewStmt := by
  intro tr pub tt hL
  obtain ⟨segs, hc, hend, hall, hpad⟩ := segments_of (segFacts hL) height_pos
  have hH : ∀ p ∈ segs, p.1 + p.2 ≤ tr.height tt := fun p hp => by
    have := seg_le_end segs 0 hc p hp; omega
  have hpadT : ∀ b sd, ∀ q, segEnd 0 segs ≤ q → q < tr.height tt →
      rowTraffic WalkV3.interactions tr tt q pub b sd = [] := by
    intro b sd q h1 h2
    have h0 := zero_of_not_one hL h2 bc_act (hpad q h1 h2)
    have hm := (rowFacts hL h2).2.1
    rw [h0] at hm
    have hz : ∀ x ∈ [WalkV3.mS, WalkV3.mK, WalkV3.mB, WalkV3.mD], tr.cell tt q x = 0 := by
      have b1 := isBool hL h2 bc_mS; have b2 := isBool hL h2 bc_mK
      have b3 := isBool hL h2 bc_mB; have b4 := isBool hL h2 bc_mD
      intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases b1 with h1 | h1 <;> rcases b2 with h2 | h2 <;> rcases b3 with h3 | h3 <;>
        rcases b4 with h4 | h4 <;> rw [h1, h2, h3, h4] at hm <;>
        first | (exfalso; revert hm; decide) | (rcases hx with rfl | rfl | rfl | rfl <;> assumption)
    have hw : tr.cell tt q WalkV3.we = 0 := by
      rcases isBool hL h2 bc_we with h | h
      · exact h
      · have := ((rowFacts hL h2).2.2.2 h).1; rw [h0] at this; exact absurd this (by decide)
    have hg : tr.cell tt q WalkV3.gK = 0 := by
      rw [(rowFacts hL h2).1, h0]
      rcases isBool hL h2 bc_ws with h | h
      · rw [h]; grind
      · have := ((rowFacts hL h2).2.2.1 h).1; rw [h0] at this; exact absurd this (by decide)
    rw [rowT]
    simp [hz WalkV3.mS (by simp), hz WalkV3.mK (by simp), hz WalkV3.mB (by simp), hw, hg,
      show (0 : Fp) + 0 = 0 by grind]
  refine ⟨segs.map (walkOfSeg tr tt), ⟨?_, ?_, ?_, ?_, ?_⟩, fun b m => ⟨?_, ?_⟩⟩
  · intro wv hw
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hw
    obtain ⟨h2, -⟩ := segInfo hL (hall p hp) (hH p hp)
    simp [walkOfSeg]; omega
  · intro wv hw
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hw
    refine ⟨Fp.toNat_lt _, Fp.toNat_lt _, fun st hst => ?_⟩
    simp only [walkOfSeg, List.mem_map, List.mem_range] at hst
    obtain ⟨j, -, rfl⟩ := hst
    refine ⟨Fp.toNat_lt _, Fp.toNat_lt _, Fp.toNat_lt _, fun x hx => ?_⟩
    simp only [stepAt, edgeAt, List.mem_map] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact Fp.toNat_lt _
  · intro wv hw i hi
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hw
    obtain ⟨h2, hrow, -⟩ := segInfo hL (hall p hp) (hH p hp)
    simp only [walkOfSeg, List.length_map, List.length_range] at hi ⊢
    simp only [List.getElem_map, List.getElem_range]
    apply stepOk hL (by have := hH p hp; omega) (hrow i hi).1
    rw [(hrow i hi).2.2.2.1]
    by_cases h : i + 1 = p.2 <;> simp [h]
  · intro wv hw
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hw
    obtain ⟨h2, -, hS, hI, hsym, -⟩ := segInfo hL (hall p hp) (hH p hp)
    simp only [walkOfSeg, WalkR.step, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (show 0 < p.2 by omega), Option.map_some, Option.getD_some, Nat.add_zero]
    refine ⟨by simp [stepAt, modeOf, hS], by simp [stepAt, hsym, natCast_eq, Fp.toNat_ofNat, SYM_START, P], ?_⟩
    simp [stepAt, edgeAt, hI]
  · intro wv hw i hi
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hw
    obtain ⟨-, hrow, -, -, -, hch⟩ := segInfo hL (hall p hp) (hH p hp)
    simp only [walkOfSeg, List.length_map, List.length_range] at hi
    have hc := hch i hi
    have hq : p.1 + i < tr.height tt := by have := hH p hp; omega
    simp only [walkOfSeg, WalkR.step, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hi, List.getElem?_range (show i < p.2 by omega), Option.map_some, Option.getD_some]
    have e : p.1 + (i + 1) = p.1 + i + 1 := by omega
    rw [e]
    refine ⟨fun hm => ?_, fun hm => ?_⟩
    · have hs1 := mode0 hm
      obtain ⟨hN, hI, hD⟩ := hc.1 hs1
      refine ⟨by simp [stepAt, edgeAt, hN, hI], ?_⟩
      intro h3
      have : tr.cell tt (p.1 + i + 1) WalkV3.mD = 1 := by
        change modeOf tr tt (p.1 + i + 1) = 3 at h3
        unfold modeOf at h3
        rcases modes_cases (q := p.1 + i + 1) hL (by have := hH p hp; omega)
          (by have := (hrow (i + 1) hi).1; rwa [e] at this) with
          h | h | h | h <;> simp [h] at h3 <;> exact h.2.2.2
      rw [hD] at this; exact absurd this (by decide)
    · have hs0 : tr.cell tt (p.1 + i) WalkV3.mS = 0 := by
        rcases isBool hL hq bc_mS with h | h
        · exact h
        · exact absurd (by simp [stepAt, modeOf, h]) hm
      have hD := hc.2 hs0
      have ha1 := (hrow (i + 1) hi).1; rw [e] at ha1
      rcases modes_cases (q := p.1 + i + 1) hL (by have := hH p hp; omega) ha1 with h | h | h | h <;>
        simp [stepAt, modeOf, h] at hD ⊢
  · simp only [walkTraffic3]
    rw [tableBusCount_eq, flatMap_rows_segs _ segs _ hc hend (hpadT b true),
      flatMap_segs segs _ _ (fun p hp => segSend hL (hall p hp) (hH p hp) b), walkSends3_flat]
    simp [List.map_flatMap, walkOfSeg, List.flatMap_map]
  · simp only [walkTraffic3]
    rw [tableBusCount_eq, flatMap_rows_segs _ segs _ hc hend (hpadT b false),
      flatMap_segs segs _ _ (fun p hp => segRecv hL (hall p hp) (hH p hp) b), walkRecvs3_flat]
    simp [List.map_flatMap, walkOfSeg, List.flatMap_map]

end ZkFormal.NearV3
