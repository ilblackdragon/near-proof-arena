import ZkFormal.NearV3.Render.Ups.CompactExtract.PlanRows
import ZkFormal.NearV3.Extract.Ups.WalkRows
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows
section
variable {C D : URow} (ok : RowOk C D) (hC : ∀ x, C x < P) (hD : ∀ x, D x < P)
include ok hC hD

theorem wbBits (hk : C wt1 + C wt2 = 1) : ∀ i, i < 16 → C (wb i) ≤ 1 := by
  intro i hi
  have h := fact ok (e := Expr.mul (.add (c wt1) (c wt2)) (Dsl.bool (c (wb i)))) (memBool (by
    unfold cBool; simp only [List.mem_append, List.mem_map, List.mem_range]
    exact Or.inl (Or.inr ⟨i, hi, rfl⟩)))
  uev_simp
  have e : Fp.ofNat (C wt1) + Fp.ofNat (C wt2) = 1 := by
    rw [ofNat_add', hk]; rfl
  rw [e] at h
  exact le1 (nat01 (hC _) (by grind))

/-- The bitmap register of `W1`/`W2` on an absent-at-branch row. -/
theorem wbmBits (hk : C wt1 + C wt2 = 1) (hB : C mB = 1) :
    C wbm = ((List.range 16).map fun i => 2 ^ i * C (wb i)).sum := by
  have W := wbBits ok hC hD hk
  have c19 := fact ok (e := mul3 (.add (c wt1) (c wt2)) (c mB) (sub (c wbm) wbE)) (memWalk (by simp [cWalk]))
  simp only [wbE, Dsl.bits, Dsl.sum, Dsl.smul, Dsl.mul3, Dsl.sub, Dsl.c, uev, Expr.evalWith, uEnv, List.range_succ,
    List.range_zero, List.map_cons, List.map_nil, List.nil_append, List.cons_append, if_false,
    Bool.false_eq_true] at c19
  have g : Fp.ofNat (C wt1) + Fp.ofNat (C wt2) = 1 := by rw [ofNat_add', hk]; rfl
  have e : Fp.ofNat (C mB) = 1 := by rw [hB]; rfl
  rw [g, e] at c19
  simp only [Nat.zero_add, cast_ofNat] at c19
  have c : ((C wbm : Nat) : Fp) + -(((((List.range 16).map fun i => 2 ^ i * C (wb i)).sum : Nat)) : Fp) = 0 := by
    simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil, List.nil_append,
      List.sum_append, List.sum_cons, List.sum_nil, natCast_add, natCast_mul]
    grind
  apply natv (hC _) _ (addNegZero c)
  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil, List.nil_append,
      List.sum_append, List.sum_cons, List.sum_nil]
  have := W 0 (by omega); have := W 1 (by omega); have := W 2 (by omega); have := W 3 (by omega)
  have := W 4 (by omega); have := W 5 (by omega); have := W 6 (by omega); have := W 7 (by omega)
  have := W 8 (by omega); have := W 9 (by omega); have := W 10 (by omega); have := W 11 (by omega)
  have := W 12 (by omega); have := W 13 (by omega); have := W 14 (by omega); have := W 15 (by omega)
  rw [P_lit]; omega

theorem walkModes (hw : C wk = 1) : C mS ≤ 1 ∧ C mK ≤ 1 ∧ C mB ≤ 1 ∧ C mS + C mK + C mB ≤ 1 ∧ C hv ≤ 1 := by
  have b' := fun {x} (hx : x ∈ rowBools) => rowBool ok hC hx
  have bmS := le1 (b' (x := mS) (by simp [rowBools]))
  have bmK := le1 (b' (x := mK) (by simp [rowBools]))
  have bmB := le1 (b' (x := mB) (by simp [rowBools]))
  have hmd := fact ok (e := Dsl.bool mDE) (memBool (by simp [cBool]))
  simp only [mDE] at hmd
  uev_simp
  simp only [cast_ofNat] at *
  rw [hw] at hmd
  have hY : ((C mS + C mK + C mB : Nat) : Fp) = 0 ∨ ((C mS + C mK + C mB : Nat) : Fp) = 1 := by
    rw [natCast_add, natCast_add]
    rcases mul_eq_zero'.mp hmd with h | h
    · right; rw [cast1] at h; grind
    · left; rw [cast1] at h; grind
  have hsum : C mS + C mK + C mB ≤ 1 := by
    rcases hY with h | h
    · have := natv (by have := P_gt; omega) (by have := P_gt; omega) (h.trans cast0.symm); omega
    · have := natv (by have := P_gt; omega) (by have := P_gt; omega) (h.trans cast1.symm); omega
  refine ⟨bmS, bmK, bmB, hsum, ?_⟩
  have h := fact ok (e := .mul (c wk) (Dsl.bool (c hv))) (memBool (by simp [cBool]))
  uev_simp
  simp only [hw] at h
  have e : Fp.ofNat 1 = 1 := rfl
  rw [e] at h
  exact le1 (nat01 (hC _) (by grind))

theorem walkRow {i : Nat} (K : WRowK C i) (hDb : D mS ≤ 1 ∧ D mK ≤ 1 ∧ D mB ≤ 1) : WalkRowF C D i := by
  have Ksf := K.sf; have K1 := K.w1; have K2 := K.w2; have K3 := K.w3; have Kl := K.lt
  have M := walkModes ok hC hD K.wk
  have a := fun x => hC x
  have d := fun x => hD x
  simp only [P_lit] at a d
  have := a nib; have := a ek; have := a nN; have := a nI; have := a nI2; have := a nN2; have := a tau
  have := a N0; have := a inv; have := a wbm; have := a hv
  have := d nN; have := d nI
  refine ⟨M, fun h => ?_, fun h => ?_, fun h h' => ?_, fun h h' => ?_, fun h => ?_, fun h => ?_⟩
  · -- W0
    subst h
    have c1 := factN ok hC hD (e := .mul (c sf) (not (c mS))) (memWalk (by simp [cWalk]))
    have c2 := factN ok hC hD (e := .mul (c sf) (c nN)) (memWalk (by simp [cWalk]))
    have c3 := factN ok hC hD (e := .mul (c sf) (sub (c nI) (c tau))) (memWalk (by simp [cWalk]))
    have c4 := factN ok hC hD (e := .mul (c sf) (c nI2)) (memWalk (by simp [cWalk]))
    have c5 := factN ok hC hD (e := .mul (c sf) (sub (c ek) (k EK_DOWN))) (memWalk (by simp [cWalk]))
    have c6 := factN ok hC hD (e := .mul (c sf) (sub (c nN2) (c N0))) (memWalk (by simp [cWalk]))
    nev_simp at c1 c2 c3 c4 c5 c6
    simp only [Ksf, ite_true] at c1 c2 c3 c4 c5 c6
    simp [EK_DOWN] at c1 c2 c3 c4 c5 c6 ⊢
    omega
  · -- a step: the symbol, the edge kind
    have c7 := factN ok hC hD (e := .mul (c mS) (sub (c nib) symE)) (memWalk (by simp [cWalk]))
    have c8 := fact ok (e := .mul (mul3 (.add (c wt1) (c wt2)) (c mS) (c ek)) (sub (c ek) (k 1)))
      (memWalk (by simp [cWalk]))
    have ek01 : (i = 1 ∨ i = 2) → C ek = 0 ∨ C ek = 1 := by
      intro hi
      uev_simp
      have e : Fp.ofNat (C wt1) + Fp.ofNat (C wt2) = 1 := by
        rw [ofNat_add', show C wt1 + C wt2 = 1 by rcases hi with rfl | rfl <;> simp [K1, K2]]; rfl
      rw [e, h] at c8
      have e1 : Fp.ofNat 1 = 1 := rfl
      rw [e1] at c8
      exact nat01 (hC _) (by grind)
    have c9 := factN ok hC hD (e := mul3 (c wt3) (c mS) (sub (c ek) (k EK_VAL))) (memWalk (by simp [cWalk]))
    have c5 := factN ok hC hD (e := .mul (c sf) (sub (c ek) (k EK_DOWN))) (memWalk (by simp [cWalk]))
    simp only [symE] at c7
    nev_simp at c5 c7 c9
    simp only [h, Ksf, K1, K2, K3] at c5 c7 c9
    refine ⟨?_, fun hi => ?_, fun hi => ?_⟩
    · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;>
        simp [wsym, SYM_START, SYM_END] at c7 ⊢ <;> omega
    · rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
      · simp [EK_DOWN] at c5 ⊢; omega
      · exact ek01 (Or.inl rfl)
      · exact ek01 (Or.inr rfl)
    · subst hi; simp [EK_VAL] at c9 ⊢; omega
  · -- after a step
    have c10 := factN ok hC hD (e := mul3 (.add (c sf) (.add (c wt1) (c wt2))) (c mS) (sub (n nN) (c nN2)))
      (memWalk (by simp [cWalk]))
    have c11 := factN ok hC hD (e := mul3 (.add (c sf) (.add (c wt1) (c wt2))) (c mS) (sub (n nI) (c nI2)))
      (memWalk (by simp [cWalk]))
    have c12 := factN ok hC hD (e := mul3 (.add (c sf) (.add (c wt1) (c wt2))) (c mS)
      (sub (k 1) (.add (n mS) (.add (n mK) (n mB))))) (memWalk (by simp [cWalk]))
    nev_simp at c10 c11 c12
    simp only [h', Ksf, K1, K2] at c10 c11 c12
    have := hDb.1; have := hDb.2.1; have := hDb.2.2
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl <;> simp at c10 c11 c12 <;> omega
  · -- after an absent terminal or a drain
    have c13 := factN ok hC hD (e := mul3 (.add (c mK) (.add (c mB) mDE)) (.add (c wt1) (c wt2))
      (.add (n mS) (.add (n mK) (n mB)))) (memWalk (by simp [cWalk]))
    simp only [mDE] at c13
    nev_simp at c13
    simp only [h', K.wk, K1, K2] at c13
    have := hDb.1; have := hDb.2.1; have := hDb.2.2
    have m := M
    rcases (show C mK = 0 ∧ C mB = 0 ∨ C mK = 1 ∧ C mB = 0 ∨ C mK = 0 ∧ C mB = 1 by omega) with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
    rcases (show i = 1 ∨ i = 2 from h) with rfl | rfl <;> simp [e1, e2] at c13 <;> omega
  · -- absent by key
    have c14 := factN ok hC hD (e := mul3 (c mK) (sub (c ek) (k EK_KEY)) (sub (c ek) (k EK_LEND)))
      (memWalk (by simp [cWalk]))
    have c15 := factN ok hC hD (e := .mul (c mK) (sub (.mul (sub symE (c nib)) (c inv)) (k 1)))
      (memWalk (by simp [cWalk]))
    simp only [symE] at c15
    nev_simp at c14 c15
    simp only [h, Ksf, K2, K3] at c14 c15
    refine ⟨?_, fun hne => ?_⟩
    · simp [EK_KEY, EK_LEND] at c14 ⊢
      have hd := Nat.dvd_of_mod_eq_zero c14
      rcases euclid (P_lit ▸ p_prime) hd with h1 | h1 <;> omega
    · rw [hne] at c15
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;>
        simp [wsym, SYM_START, SYM_END] at c15
  · -- absent at a branch
    have c16 := factN ok hC hD (e := .mul (c mB) (c nI)) (memWalk (by simp [cWalk]))
    have c17 := factN ok hC hD (e := mul3 (c wt1) (c mB) (c (wb 0))) (memWalk (by simp [cWalk]))
    have c18 := factN ok hC hD (e := mul3 (c wt2) (c mB) (c (wb 15))) (memWalk (by simp [cWalk]))
    have c20 := factN ok hC hD (e := mul3 (c wt3) (c mB) (c hv)) (memWalk (by simp [cWalk]))
    nev_simp at c16 c17 c18 c20
    simp only [h, K1, K2, K3] at c16 c17 c18 c20
    refine ⟨by simp at c16; omega, fun hi => by subst hi; simp at c20; omega, fun hi => ?_⟩
    have hk : C wt1 + C wt2 = 1 := by rcases hi with rfl | rfl <;> simp [K1, K2]
    have W := wbBits ok hC hD hk
    have w0 := W 0 (by omega); have w1 := W 1 (by omega); have w2 := W 2 (by omega); have w3 := W 3 (by omega)
    have w4 := W 4 (by omega); have w5 := W 5 (by omega); have w6 := W 6 (by omega); have w7 := W 7 (by omega)
    have w8 := W 8 (by omega); have w9 := W 9 (by omega); have w10 := W 10 (by omega); have w11 := W 11 (by omega)
    have w12 := W 12 (by omega); have w13 := W 13 (by omega); have w14 := W 14 (by omega); have w15 := W 15 (by omega)
    simp only [wb] at w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 c17 c18
    have hS := wbmBits ok hC hD hk h
    rcases hi with rfl | rfl <;> simp [wsym, SYM_START, SYM_END] at c17 c18 ⊢ <;>
      simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil, List.nil_append,
        List.sum_append, List.sum_cons, List.sum_nil, wb] at hS <;> constructor <;> omega

/-- **Levels** of the walk: `W1` is at level 0; a step enters a new record iff it lands on
position 0, and the level advances; a lookup row's record is the path record of its level. -/
theorem walkLev {i : Nat} (K : WRowK C i) (h1 : 1 ≤ i) :
    C lv0 ≤ 1 ∧ C lv1 ≤ 1 ∧ C lv2 ≤ 1 ∧ C enter ≤ 1 ∧
    (i = 1 → C lv0 = 1 ∧ C lv1 = 0 ∧ C lv2 = 0) ∧
    ((i = 1 ∨ i = 2) → C mS = 1 → (C enter = 1 → C nI2 = 0) ∧ (C enter = 0 → C nN2 = C nN) ∧
      (D lv0 + C lv0 * C enter) % P = C lv0 ∧ (D lv1 + C lv1 * C enter) % P = (C lv1 + C lv0 * C enter) % P ∧
      (D lv2 + C lv2 * C enter) % P = (C lv2 + C lv1 * C enter) % P) ∧
    (C mS + C mK + C mB = 1 → C lv0 + C lv1 + C lv2 = 1 →
      C nN = C lv0 * C N0 + C lv1 * C N1 + C lv2 * C N2) := by
  have bw := fun {x} (hx : Expr.mul (c wk) (Dsl.bool (c x)) ∈ cBool) => by
    have h := fact ok (e := Expr.mul (c wk) (Dsl.bool (c x))) (memBool hx)
    uev_simp
    simp only [K.wk] at h
    have e : Fp.ofNat 1 = 1 := rfl
    rw [e] at h
    exact le1 (nat01 (hC x) (by grind))
  have b0 : C lv0 ≤ 1 := bw (by simp [cBool]); have b1 : C lv1 ≤ 1 := bw (by simp [cBool])
  have b2 : C lv2 ≤ 1 := bw (by simp [cBool]); have be : C enter ≤ 1 := bw (by simp [cBool])
  have Ksf := K.sf; have K1 := K.w1; have K2 := K.w2; have K3 := K.w3; have Kl := K.lt
  have a := fun x => hC x
  have d := fun x => hD x
  simp only [P_lit] at a d ⊢
  have := a nN; have := a nN2; have := a nI2; have := a N0; have := a N1; have := a N2
  have := d lv0; have := d lv1; have := d lv2
  refine ⟨b0, b1, b2, be, fun hi => ?_, fun hi hs => ?_, fun hl hv => ?_⟩
  · subst hi
    have f1 := factN ok hC hD (e := .mul (c wt1) (not (c lv0))) (memWalk (by simp [cWalk]))
    have f2 := factN ok hC hD (e := .mul (c wt1) (c lv1)) (memWalk (by simp [cWalk]))
    have f3 := factN ok hC hD (e := .mul (c wt1) (c lv2)) (memWalk (by simp [cWalk]))
    nev_simp at f1 f2 f3
    simp only [K1] at f1 f2 f3
    simp at f1 f2 f3
    omega
  · have hk : C wt1 + C wt2 = 1 := by rcases hi with rfl | rfl <;> simp [K1, K2]
    have f1 := factN ok hC hD (e := mul3 (.add (c wt1) (c wt2)) (c mS) (.mul (c enter) (c nI2))) (memWalk (by simp [cWalk]))
    have f2 := factN ok hC hD (e := .mul (mul3 (.add (c wt1) (c wt2)) (c mS) (not (c enter))) (sub (c nN2) (c nN)))
      (memWalk (by simp [cWalk]))
    have f3 := factN ok hC hD (e := mul3 (.add (c wt1) (c wt2)) (c mS) (sub (n lv0) (sub (c lv0) (.mul (c lv0) (c enter)))))
      (memWalk (by simp [cWalk]))
    have f4 := factN ok hC hD (e := mul3 (.add (c wt1) (c wt2)) (c mS)
      (sub (n lv1) (.add (sub (c lv1) (.mul (c lv1) (c enter))) (.mul (c lv0) (c enter))))) (memWalk (by simp [cWalk]))
    have f5 := factN ok hC hD (e := mul3 (.add (c wt1) (c wt2)) (c mS)
      (sub (n lv2) (.add (sub (c lv2) (.mul (c lv2) (c enter))) (.mul (c lv1) (c enter))))) (memWalk (by simp [cWalk]))
    nev_simp at f1 f2 f3 f4 f5
    have e1 : (C wt1 + C wt2) % 2013265921 = 1 := by rw [hk]
    simp only [e1, hs, Nat.one_mul, Nat.mod_mod] at f1 f2 f3 f4 f5
    rcases (show C enter = 0 ∨ C enter = 1 by omega) with he | he <;> simp [he] at f1 f2 f3 f4 f5 ⊢ <;>
      rcases (show C lv0 = 0 ∨ C lv0 = 1 by omega) with h0 | h0 <;>
      rcases (show C lv1 = 0 ∨ C lv1 = 1 by omega) with h1' | h1' <;>
      rcases (show C lv2 = 0 ∨ C lv2 = 1 by omega) with h2 | h2 <;> simp [h0, h1', h2] at f3 f4 f5 ⊢ <;> omega
  · have hw : C wt1 + C wt2 + C wt3 = 1 := by
      rcases (show i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl <;> simp [K1, K2, K3]
    have f := factN ok hC hD (e := mul3 (.add (c wt1) (.add (c wt2) (c wt3))) (.add (c mS) (.add (c mK) (c mB)))
      (sub (c nN) (sum [.mul (c lv0) (c N0), .mul (c lv1) (c N1), .mul (c lv2) (c N2)]))) (memWalk (by simp [cWalk]))
    nev_simp at f
    have e1 : (C wt1 + (C wt2 + C wt3) % 2013265921) % 2013265921 = 1 := by rw [Nat.add_mod_mod]; omega
    have e2 : (C mS + (C mK + C mB) % 2013265921) % 2013265921 = 1 := by rw [Nat.add_mod_mod]; omega
    simp only [e1, e2, Nat.one_mul, Nat.mod_mod] at f
    rcases (show C lv0 = 1 ∧ C lv1 = 0 ∧ C lv2 = 0 ∨ C lv0 = 0 ∧ C lv1 = 1 ∧ C lv2 = 0 ∨
        C lv0 = 0 ∧ C lv1 = 0 ∧ C lv2 = 1 by omega) with ⟨h0, h1', h2⟩ | ⟨h0, h1', h2⟩ | ⟨h0, h1', h2⟩ <;>
      simp [h0, h1', h2] at f ⊢ <;> omega

/-- **The terminal row** `t* = si + 1` and the case selector. -/
theorem walkTerm {i : Nat} (K : WRowK C i) (h1 : 1 ≤ i) {ci ti di si : Nat} (i1 : ci < 11) (i2 : ti < 3)
    (i3 : di < 3) (i4 : si < 3)
    (hcs : ∀ m, m < 11 → C (17 + m) = if m = ci then 1 else 0)
    (hti : ∀ m, m < 3 → C (34 + m) = if m = ti then 1 else 0)
    (hdd : ∀ m, m < 3 → C (28 + m) = if m = di then 1 else 0)
    (hts : ∀ m, m < 3 → C (31 + m) = if m = si then 1 else 0) :
    C trm = (if si + 1 = i then 1 else 0) ∧
    (i = 1 → 1 ≤ si → C mS = 1) ∧ (i = 2 → si = 2 → C mS = 1) ∧
    (si + 1 = i → C mS = 1 → i = 3) ∧
    (si + 1 = i → C nI = ti ∧ C lv0 = (if di = 0 then 1 else 0) ∧ C lv1 = (if di = 1 then 1 else 0) ∧
      C lv2 = (if di = 2 then 1 else 0)) ∧
    (si + 1 = i → C mS = (if ci ≤ 1 then 1 else 0) ∧ C mB = (if ci = 2 ∨ ci = 3 then 1 else 0) ∧
      C mK = (if 4 ≤ ci then 1 else 0)) ∧
    (si + 1 = i → C mK = 1 → (ci = 4 → C ek = EK_LEND) ∧ (ci ≠ 4 → C ek = EK_KEY ∧ C nib = C tX)) ∧
    (i = 3 → C pres = C mS ∧ C vid = C mS * C nN2) := by
  have Ksf := K.sf; have K1 := K.w1; have K2 := K.w2; have K3 := K.w3; have Kl := K.lt
  have M := walkModes ok hC hD K.wk
  have s1 : C ts1 = if 0 = si then 1 else 0 := hts 0 (by omega)
  have s2 : C ts2 = if 1 = si then 1 else 0 := hts 1 (by omega)
  have s3 : C ts3 = if 2 = si then 1 else 0 := hts 2 (by omega)
  have j1 : C ti1 = if 1 = ti then 1 else 0 := hti 1 (by omega)
  have j2 : C ti2 = if 2 = ti then 1 else 0 := hti 2 (by omega)
  have d0 : C dd0 = if 0 = di then 1 else 0 := hdd 0 (by omega)
  have d1 : C dd1 = if 1 = di then 1 else 0 := hdd 1 (by omega)
  have d2 : C dd2 = if 2 = di then 1 else 0 := hdd 2 (by omega)
  have g0 : C cLP = if 0 = ci then 1 else 0 := hcs 0 (by omega)
  have g1 : C cBR = if 1 = ci then 1 else 0 := hcs 1 (by omega)
  have g2 : C cBV = if 2 = ci then 1 else 0 := hcs 2 (by omega)
  have g3 : C cBI = if 3 = ci then 1 else 0 := hcs 3 (by omega)
  have g4 : C cLSa = if 4 = ci then 1 else 0 := hcs 4 (by omega)
  have g5 : C cLSb = if 5 = ci then 1 else 0 := hcs 5 (by omega)
  have g6 : C cLSc = if 6 = ci then 1 else 0 := hcs 6 (by omega)
  have g7 : C cESl0 = if 7 = ci then 1 else 0 := hcs 7 (by omega)
  have g8 : C cESl1 = if 8 = ci then 1 else 0 := hcs 8 (by omega)
  have g9 : C cESn0 = if 9 = ci then 1 else 0 := hcs 9 (by omega)
  have g10 : C cESn1 = if 10 = ci then 1 else 0 := hcs 10 (by omega)
  have bw := fun {x} (hx : Expr.mul (c wk) (Dsl.bool (c x)) ∈ cBool) => by
    have h := fact ok (e := Expr.mul (c wk) (Dsl.bool (c x))) (memBool hx)
    uev_simp
    simp only [K.wk] at h
    have e : Fp.ofNat 1 = 1 := rfl
    rw [e] at h
    exact le1 (nat01 (hC x) (by grind))
  have bl0 : C lv0 ≤ 1 := bw (by simp [cBool]); have bl1 : C lv1 ≤ 1 := bw (by simp [cBool])
  have bl2 : C lv2 ≤ 1 := bw (by simp [cBool])
  have a := fun x => hC x
  simp only [P_lit] at a
  have := a trm; have := a nI; have := a nib; have := a tX; have := a ek; have := a pres; have := a vid
  have := a nN2
  -- the terminal flag
  have t0 := factN ok hC hD (e := .mul (c wk) (sub (c trm) trmE)) (memWalk (by simp [cWalk]))
  simp only [trmE] at t0
  nev_simp at t0
  simp only [K.wk, K1, K2, K3, s1, s2, s3] at t0
  have htrm : C trm = (if si + 1 = i then 1 else 0) := by
    rcases (show i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl <;>
    rcases (show si = 0 ∨ si = 1 ∨ si = 2 by omega) with rfl | rfl | rfl <;> simp at t0 ⊢ <;> omega
  refine ⟨htrm, fun hi hs => ?_, fun hi hs => ?_, fun hi hm => ?_, fun hi => ?_, fun hi => ?_, fun hi hk => ?_,
    fun hi => ?_⟩
  · subst hi
    have f := factN ok hC hD (e := mul3 (c wt1) (.add (c ts2) (c ts3)) (not (c mS))) (memWalk (by simp [cWalk]))
    nev_simp at f
    simp only [K1, s2, s3] at f
    rcases (show si = 1 ∨ si = 2 by omega) with rfl | rfl <;> simp at f <;> omega
  · subst hi hs
    have f := factN ok hC hD (e := mul3 (c wt2) (c ts3) (not (c mS))) (memWalk (by simp [cWalk]))
    nev_simp at f
    simp only [K2, s3] at f
    simp at f; omega
  · have f := factN ok hC hD (e := mul3 (c trm) (c mS) (not (c wt3))) (memWalk (by simp [cWalk]))
    nev_simp at f
    simp only [htrm, hm, K3, if_pos hi] at f
    by_cases h3 : i = 3
    · exact h3
    · simp [h3] at f
  · have hT : C wt1 * C ts1 + C wt2 * C ts2 + C wt3 * C ts3 = 1 := by
      rw [K1, K2, K3, s1, s2, s3]
      rcases (show si = 0 ∨ si = 1 ∨ si = 2 by omega) with rfl | rfl | rfl <;> subst hi <;> simp
    have f1 := factN ok hC hD (e := .mul trmE (sub (c nI) tIE)) (memWalk (by simp [cWalk]))
    have f2 := factN ok hC hD (e := .mul trmE (sub (c dd0) (c lv0))) (memWalk (by simp [cWalk]))
    have f3 := factN ok hC hD (e := .mul trmE (sub (c dd1) (c lv1))) (memWalk (by simp [cWalk]))
    have f4 := factN ok hC hD (e := .mul trmE (sub (c dd2) (c lv2))) (memWalk (by simp [cWalk]))
    simp only [trmE, tIE] at f1 f2 f3 f4
    nev_simp at f1 f2 f3 f4
    simp only [K1, K2, K3, s1, s2, s3, j1, j2, d0, d1, d2] at f1 f2 f3 f4
    rcases (show si = 0 ∨ si = 1 ∨ si = 2 by omega) with rfl | rfl | rfl <;> subst hi <;>
    rcases (show ti = 0 ∨ ti = 1 ∨ ti = 2 by omega) with rfl | rfl | rfl <;>
    rcases (show di = 0 ∨ di = 1 ∨ di = 2 by omega) with rfl | rfl | rfl <;> simp at f1 f2 f3 f4 ⊢ <;> omega
  · have f1 := factN ok hC hD (e := .mul trmE (sub (c mS) (.add (c cLP) (c cBR)))) (memWalk (by simp [cWalk]))
    have f2 := factN ok hC hD (e := .mul trmE (sub (c mB) (.add (c cBI) (c cBV)))) (memWalk (by simp [cWalk]))
    have f3 := factN ok hC hD (e := .mul trmE (sub (c mK) splitE)) (memWalk (by simp [cWalk]))
    simp only [trmE, splitE, sumc, List.map_cons, List.map_nil] at f1 f2 f3
    nev_simp at f1 f2 f3
    simp only [K1, K2, K3, s1, s2, s3, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10] at f1 f2 f3
    have hT : (if si + 1 = i then 1 else 0) = 1 := by rw [if_pos hi]
    rcases (show si = 0 ∨ si = 1 ∨ si = 2 by omega) with rfl | rfl | rfl <;> subst hi <;>
    rcases (show ci = 0 ∨ ci = 1 ∨ ci = 2 ∨ ci = 3 ∨ ci = 4 ∨ ci = 5 ∨ ci = 6 ∨ ci = 7 ∨ ci = 8 ∨ ci = 9 ∨ ci = 10 by omega)
      with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at f1 f2 f3 ⊢ <;> omega
  · have f1 := factN ok hC hD (e := .mul (mul3 (c trm) (c mK) (not (c cLSa))) (sub (c nib) (c tX))) (memWalk (by simp [cWalk]))
    have f2 := factN ok hC hD (e := .mul (mul3 (c trm) (c mK) (c cLSa)) (sub (c ek) (k EK_LEND))) (memWalk (by simp [cWalk]))
    have f3 := factN ok hC hD (e := .mul (mul3 (c trm) (c mK) (not (c cLSa))) (sub (c ek) (k EK_KEY))) (memWalk (by simp [cWalk]))
    nev_simp at f1 f2 f3
    simp only [htrm, if_pos hi, hk, g4, EK_LEND, EK_KEY] at f1 f2 f3 ⊢
    refine ⟨fun h4 => ?_, fun h4 => ?_⟩
    · subst h4; simp at f2; omega
    · simp [show ¬ (4 = ci) by omega] at f1 f3; omega
  · subst hi
    have f1 := factN ok hC hD (e := .mul (c wt3) (sub (c pres) (c mS))) (memWalk (by simp [cWalk]))
    have f2 := factN ok hC hD (e := .mul (c wt3) (sub (c vid) (.mul (c mS) (c nN2)))) (memWalk (by simp [cWalk]))
    nev_simp at f1 f2
    simp only [K3] at f1 f2
    have := M.1
    rcases (show C mS = 0 ∨ C mS = 1 by omega) with h0 | h0 <;> simp [h0] at f1 f2 ⊢ <;> omega

end

end ZkFormal.NearV3.Render.UpsRelay.Extract
