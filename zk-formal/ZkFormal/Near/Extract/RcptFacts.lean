import ZkFormal.Near.Extract.RcptView
import ZkFormal.Near.Extract.Segments
import ZkFormal.Near.Extract.BusCount
import ZkFormal.Near.Tables.Rcpt

/-!
# ZkFormal.Near.Extract.RcptFacts — row facts of the `rcpt` table (control)

Each lemma reads a few constraints of `Tables/Rcpt/Fields.lean` on one row
(and the next row): booleans, one-hot field states, field bookkeeping
(`idx fs fe`), field lengths and successions, receipt boundaries and the
receipt constants.
-/

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt

variable {tr : Trace Fp} {pub : List Fp}

theorem con (hL : TableLocal Rcpt.table tr T_RCPT pub) {r : Nat} (hq : r < tr.height T_RCPT)
    {e : Expr} (he : e ∈ Rcpt.constraints) : e.eval tr T_RCPT r pub = 0 :=
  hL.constr r hq e he

theorem nxt {r : Nat} (h : r + 1 < tr.height T_RCPT) : (r + 1) % tr.height T_RCPT = r + 1 :=
  Nat.mod_eq_of_lt h

theorem mem_st {e : Expr} (h : e ∈ cStates) : e ∈ Rcpt.constraints := by
  unfold Rcpt.constraints; simp [h]
theorem mem_em {e : Expr} (h : e ∈ cEmit) : e ∈ Rcpt.constraints := by
  unfold Rcpt.constraints; simp [h]
theorem mem_rg {e : Expr} (h : e ∈ cRegs) : e ∈ Rcpt.constraints := by
  unfold Rcpt.constraints; simp [h]
theorem mem_ch {e : Expr} (h : e ∈ cChars) : e ∈ Rcpt.constraints := by
  unfold Rcpt.constraints; simp [h]
theorem mem_ky {e : Expr} (h : e ∈ cKey) : e ∈ Rcpt.constraints := by
  unfold Rcpt.constraints; simp [h]
theorem mem_gs {e : Expr} (h : e ∈ cGas) : e ∈ Rcpt.constraints := by
  unfold Rcpt.constraints; simp [h]
theorem mem_dp {e : Expr} (h : e ∈ cDep) : e ∈ Rcpt.constraints := by
  unfold Rcpt.constraints; simp [h]
theorem mem_cl {e : Expr} (h : e ∈ cClaim) : e ∈ Rcpt.constraints := by
  unfold Rcpt.constraints; simp [h]
theorem mem_en {e : Expr} (h : e ∈ cEnd) : e ∈ Rcpt.constraints := by
  unfold Rcpt.constraints; simp [h]

/-- Boolean columns of `cStates`. -/
def boolCols : List Nat :=
  [act, rf, rl, lastR, fs, fe, kz, gKA, r1, lo8, lo4, kt, Rcpt.hr, ge, big, gDg] ++ states ++ (List.range 66).map xb

/-! ## Sums of booleans -/

def fsum (f : Nat → Fp) : List Nat → Fp
  | [] => 0
  | x :: l => f x + fsum f l

theorem eval_sum_map_c (tr : Trace Fp) (t q : Nat) (pub : List Fp) (l : List Nat) :
    (sum (l.map c)).eval tr t q pub = fsum (tr.cell t q) l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [fsum, ih]

theorem fsum_bool (f : Nat → Fp) (l : List Nat) (hb : ∀ x ∈ l, f x = 0 ∨ f x = 1) :
    fsum f l = ((l.countP (fun x => decide (f x = 1)) : Nat) : Fp) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [fsum, List.countP_cons]
    rw [ih (fun y hy => hb y (by simp [hy]))]
    rcases hb x (by simp) with h | h
    · rw [h]; simp [fp_zero_ne_one]; grind
    · rw [h]; simp; rw [natCast_add]; grind

theorem two_le_countP {α : Type} [DecidableEq α] (p : α → Bool) :
    ∀ (l : List α) (x y : α), x ∈ l → y ∈ l → x ≠ y → p x = true → p y = true → 2 ≤ l.countP p := by
  intro l
  induction l with
  | nil => intro x y hx; simp at hx
  | cons a l ih =>
    intro x y hx hy hne hpx hpy
    rw [List.countP_cons]
    by_cases hax : a = x
    · subst hax
      have hy' : y ∈ l := by rcases List.mem_cons.mp hy with h | h; exact absurd h.symm hne; exact h
      have := List.countP_pos_iff.mpr ⟨y, hy', hpy⟩
      rw [if_pos hpx]; omega
    · by_cases hay : a = y
      · subst hay
        have hx' : x ∈ l := by rcases List.mem_cons.mp hx with h | h; exact absurd h.symm hax; exact h
        have := List.countP_pos_iff.mpr ⟨x, hx', hpx⟩
        rw [if_pos hpy]; omega
      · have hx' : x ∈ l := by rcases List.mem_cons.mp hx with h | h; exact absurd h.symm hax; exact h
        have hy' : y ∈ l := by rcases List.mem_cons.mp hy with h | h; exact absurd h.symm hay; exact h
        have := ih x y hx' hy' hne hpx hpy
        split <;> omega

/-- One-hot: a boolean list with sum `a ∈ {0,1}` and one entry `1`. -/
theorem oneHot_of (f : Nat → Fp) (l : List Nat) (hlen : l.length < P) (a : Fp)
    (hb : ∀ x ∈ l, f x = 0 ∨ f x = 1) (ha : a = 0 ∨ a = 1) (hs : fsum f l = a)
    {x : Nat} (hx : x ∈ l) (h1 : f x = 1) : a = 1 ∧ ∀ y ∈ l, y ≠ x → f y = 0 := by
  rw [fsum_bool f l hb] at hs
  have hle : l.countP (fun x => decide (f x = 1)) ≤ l.length := List.countP_le_length
  have hpos : 1 ≤ l.countP (fun x => decide (f x = 1)) :=
    List.countP_pos_iff.mpr ⟨x, hx, by simp [h1]⟩
  have hone : l.countP (fun x => decide (f x = 1)) = 1 := by
    rcases ha with ha | ha
    · rw [ha] at hs
      have := ofNat_inj (a := l.countP (fun x => decide (f x = 1))) (b := 0) (by omega) (by unfold P; omega) (by rw [hs]; rfl)
      omega
    · rw [ha] at hs
      exact ofNat_inj (by omega) (by unfold P; omega) (by rw [hs]; rfl)
  refine ⟨?_, fun y hy hne => ?_⟩
  · rw [← hs, hone]; rfl
  · rcases hb y hy with h | h
    · exact h
    · have := two_le_countP (fun x => decide (f x = 1)) l x y hx hy (Ne.symm hne) (by simp [h1]) (by simp [h])
      omega

variable (hL : TableLocal Rcpt.table tr T_RCPT pub)
include hL

theorem height_le : tr.height T_RCPT ≤ 2 ^ 18 := by
  have := hL.log_le; unfold Trace.height; exact Nat.pow_le_pow_right (by omega) this

theorem height_ge : 2 ≤ tr.height T_RCPT := by
  have := hL.log_ge; unfold Trace.height
  calc 2 = 2 ^ 1 := rfl
    _ ≤ _ := Nat.pow_le_pow_right (by omega) this

theorem isBool {r : Nat} (hq : r < tr.height T_RCPT) {x : Nat} (hx : x ∈ boolCols) :
    tr.cell T_RCPT r x = 0 ∨ tr.cell T_RCPT r x = 1 := by
  have := con hL hq (e := Dsl.bool (c x)) (mem_st (by
    unfold cStates; simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (List.mem_map_of_mem (f := fun x => Dsl.bool (c x)) (show x ∈ boolCols from hx))))))))))
  simp only [eval_bool, eval_c] at this
  exact bool_cases this

theorem bool01 {r x : Nat} (hq : r < tr.height T_RCPT) (hx : x ∈ boolCols) (h : ¬ tr.cell T_RCPT r x = 1) :
    tr.cell T_RCPT r x = 0 := (isBool hL hq hx).resolve_right h

theorem states_bool {r : Nat} (hq : r < tr.height T_RCPT) :
    ∀ x ∈ states, tr.cell T_RCPT r x = 0 ∨ tr.cell T_RCPT r x = 1 :=
  fun x hx => isBool hL hq (by unfold boolCols; simp only [List.mem_append]; exact Or.inl (Or.inr hx))

theorem sumStates {r : Nat} (hq : r < tr.height T_RCPT) :
    fsum (tr.cell T_RCPT r) states = tr.cell T_RCPT r act := by
  have := con hL hq (e := sub (sum (states.map c)) (c act)) (mem_st (by simp [cStates]))
  simp only [eval_sub, eval_c, eval_sum_map_c] at this
  grind

/-- **One-hot field states.** -/
theorem oneHot {r : Nat} (hq : r < tr.height T_RCPT) {x : Nat} (hx : x ∈ states)
    (h1 : tr.cell T_RCPT r x = 1) :
    tr.cell T_RCPT r act = 1 ∧ ∀ y ∈ states, y ≠ x → tr.cell T_RCPT r y = 0 :=
  oneHot_of _ states (by decide) _ (states_bool hL hq) (isBool hL hq (by simp [boolCols]))
    (sumStates hL hq) hx h1

/-- An inactive row has no state. -/
theorem noState {r : Nat} (hq : r < tr.height T_RCPT) (ha : tr.cell T_RCPT r act = 0) :
    ∀ x ∈ states, tr.cell T_RCPT r x = 0 := by
  intro x hx
  rcases states_bool hL hq x hx with h | h
  · exact h
  · have := (oneHot hL hq hx h).1; rw [ha] at this; exact absurd this fp_zero_ne_one

/-! ## Field bookkeeping -/

/-- Inside a field: same state, `idx + 1`, not a field start, active. -/
theorem inField {r : Nat} (hq : r + 1 < tr.height T_RCPT) (ha : tr.cell T_RCPT r act = 1)
    (he : tr.cell T_RCPT r fe = 0) :
    (∀ x ∈ states, tr.cell T_RCPT (r + 1) x = tr.cell T_RCPT r x) ∧
    tr.cell T_RCPT (r + 1) idx = tr.cell T_RCPT r idx + 1 ∧ tr.cell T_RCPT (r + 1) fs = 0 ∧
    tr.cell T_RCPT (r + 1) act = 1 := by
  have hq' : r < tr.height T_RCPT := by omega
  have h1 := con hL hq' (e := mul3 (c act) (Dsl.not (c fe)) (sub (n idx) (.add (c idx) (k 1))))
    (mem_st (by simp [cStates]))
  have h2 := con hL hq' (e := mul3 (c act) (Dsl.not (c fe)) (n fs)) (mem_st (by simp [cStates]))
  simp only [eval_mul3, eval_c, eval_not, eval_n, eval_sub, eval_add, eval_k, nxt hq] at h1 h2
  rw [ha, he] at h1 h2
  have hst : ∀ x ∈ states, tr.cell T_RCPT (r + 1) x = tr.cell T_RCPT r x := by
    intro x hx
    have h3 := con hL hq' (e := mul3 (c act) (Dsl.not (c fe)) (sub (n x) (c x)))
      (mem_st (by
        unfold cStates; simp only [List.mem_append]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (List.mem_map_of_mem hx))))))))
    simp only [eval_mul3, eval_c, eval_not, eval_n, eval_sub, nxt hq] at h3
    rw [ha, he] at h3; grind
  refine ⟨hst, by grind, by grind, ?_⟩
  have e1 := sumStates hL hq
  have e2 := sumStates hL hq'
  have : fsum (tr.cell T_RCPT (r + 1)) states = fsum (tr.cell T_RCPT r) states := by
    have gen : ∀ l : List Nat, (∀ x ∈ l, tr.cell T_RCPT (r + 1) x = tr.cell T_RCPT r x) →
        fsum (tr.cell T_RCPT (r + 1)) l = fsum (tr.cell T_RCPT r) l := by
      intro l; induction l with
      | nil => intro _; rfl
      | cons x l ih => intro h; simp only [fsum]; rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]
    exact gen states hst
  rw [← e1, this, e2, ha]

/-- After a field end that is not a receipt end: new field starts. -/
theorem afterField {r : Nat} (hq : r + 1 < tr.height T_RCPT) (he : tr.cell T_RCPT r fe = 1)
    (hl : tr.cell T_RCPT r rl = 0) :
    tr.cell T_RCPT (r + 1) idx = 0 ∧ tr.cell T_RCPT (r + 1) fs = 1 := by
  have hq' : r < tr.height T_RCPT := by omega
  have h1 := con hL hq' (e := mul3 (c fe) (Dsl.not (c rl)) (n idx)) (mem_st (by simp [cStates]))
  have h2 := con hL hq' (e := mul3 (c fe) (Dsl.not (c rl)) (Dsl.not (n fs))) (mem_st (by simp [cStates]))
  simp only [eval_mul3, eval_c, eval_not, eval_n, nxt hq] at h1 h2
  rw [he, hl] at h1 h2
  exact ⟨by grind, by grind⟩

/-- Field lengths: at a field end, `idx` is the field's last index. -/
theorem fieldEnd {r : Nat} (hq : r < tr.height T_RCPT) (he : tr.cell T_RCPT r fe = 1)
    {x : Nat} {e : Expr} (hx : (x, e) ∈ lastIdx) (h1 : tr.cell T_RCPT r x = 1) :
    tr.cell T_RCPT r idx = e.eval tr T_RCPT r pub := by
  have h := con hL hq (e := mul3 (c fe) (c x) (sub (c idx) e)) (mem_st (by
    unfold cStates; simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inr
      (List.mem_map_of_mem (f := fun (p : Nat × Expr) => mul3 (c fe) (c p.1) (sub (c idx) p.2)) hx))))))
  simp only [eval_mul3, eval_c, eval_sub] at h
  rw [he, h1] at h; grind

/-- Field successions. -/
theorem fieldSucc {r : Nat} (hq : r + 1 < tr.height T_RCPT) (he : tr.cell T_RCPT r fe = 1)
    {x x' : Nat} {g : Expr} (hx : (x, x', g) ∈ Rcpt.succ) (h1 : tr.cell T_RCPT r x = 1)
    (hg : g.eval tr T_RCPT r pub = 1) : tr.cell T_RCPT (r + 1) x' = 1 := by
  have hq' : r < tr.height T_RCPT := by omega
  have h := con hL hq' (e := .mul (mul3 (c fe) (c x) g) (Dsl.not (n x'))) (mem_st (by
    unfold cStates; simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inr
      (List.mem_map_of_mem (f := fun (p : Nat × Nat × Expr) => Expr.mul (mul3 (c fe) (c p.1) p.2.2)
        (Dsl.not (n p.2.1))) hx)))))
  simp only [eval_mul, eval_mul3, eval_c, eval_not, eval_n, nxt hq] at h
  rw [he, h1, hg] at h; grind

/-! ## First and last rows, padding -/

theorem row0 (h0 : 0 < tr.height T_RCPT) :
    tr.cell T_RCPT 0 sCL = 1 ∧ tr.cell T_RCPT 0 fs = 1 ∧ tr.cell T_RCPT 0 idx = 0 ∧
    tr.cell T_RCPT 0 act = 1 := by
  have h1 := con hL h0 (e := .mul .isFirst (Dsl.not (c sCL))) (mem_st (by simp [cStates]))
  have h2 := con hL h0 (e := .mul .isFirst (Dsl.not (c fs))) (mem_st (by simp [cStates]))
  have h3 := con hL h0 (e := .mul .isFirst (c idx)) (mem_st (by simp [cStates]))
  simp only [eval_mul, eval_c, eval_not, eval_isFirst, if_true] at h1 h2 h3
  have hs : tr.cell T_RCPT 0 sCL = 1 := by grind
  exact ⟨hs, by grind, by grind, (oneHot hL h0 (by simp [states]) hs).1⟩

theorem lastRow (h0 : 0 < tr.height T_RCPT) : tr.cell T_RCPT (tr.height T_RCPT - 1) act = 0 := by
  have h1 := con hL (by omega : tr.height T_RCPT - 1 < _) (e := .mul .isLast (c act))
    (mem_st (by simp [cStates]))
  simp only [eval_mul, eval_c, eval_isLast,
    if_pos (show tr.height T_RCPT - 1 + 1 = tr.height T_RCPT by omega)] at h1
  grind

theorem pad {r : Nat} (hq : r + 1 < tr.height T_RCPT) (ha : tr.cell T_RCPT r act = 0) :
    tr.cell T_RCPT (r + 1) act = 0 := by
  have h1 := con hL (by omega : r < _) (e := mul3 .isTransition (Dsl.not (c act)) (n act))
    (mem_st (by simp [cStates]))
  simp only [eval_mul3, eval_c, eval_not, eval_n, eval_isTransition, nxt hq,
    if_neg (show ¬ r + 1 = tr.height T_RCPT by omega)] at h1
  rw [ha] at h1; grind

/-- An active row is not the last row. -/
theorem act_lt {r : Nat} (hq : r < tr.height T_RCPT) (ha : tr.cell T_RCPT r act = 1) :
    r + 1 < tr.height T_RCPT := by
  rcases Nat.lt_or_ge (r + 1) (tr.height T_RCPT) with h | h
  · exact h
  · have : r = tr.height T_RCPT - 1 := by omega
    subst this; rw [lastRow hL (by omega)] at ha; exact absurd ha fp_zero_ne_one

/-! ## Receipt boundaries -/

theorem bounds {r : Nat} (hq : r < tr.height T_RCPT) :
    tr.cell T_RCPT r rl = tr.cell T_RCPT r fe *
      (tr.cell T_RCPT r sXRZ + tr.cell T_RCPT r sXLH * (1 - tr.cell T_RCPT r Rcpt.hr)) ∧
    (tr.cell T_RCPT r rf = 1 → tr.cell T_RCPT r sPL = 1 ∧ tr.cell T_RCPT r fs = 1) ∧
    (tr.cell T_RCPT r sPL = 1 → tr.cell T_RCPT r fs = 1 → tr.cell T_RCPT r rf = 1) ∧
    (tr.cell T_RCPT r Rcpt.hr = 1 → tr.cell T_RCPT r ge = 1) := by
  have h1 := con hL hq (e := sub (c rl) (.mul (c fe) (.add (c sXRZ) (.mul (c sXLH) (Dsl.not (c Rcpt.hr))))))
    (mem_st (by simp [cStates]))
  have h2 := con hL hq (e := .mul (c rf) (Dsl.not (c sPL))) (mem_st (by simp [cStates]))
  have h3 := con hL hq (e := .mul (c rf) (Dsl.not (c fs))) (mem_st (by simp [cStates]))
  have h4 := con hL hq (e := mul3 (c sPL) (c fs) (Dsl.not (c rf))) (mem_st (by simp [cStates]))
  have h5 := con hL hq (e := .mul (c Rcpt.hr) (Dsl.not (c ge))) (mem_st (by simp [cStates]))
  simp only [eval_mul, eval_mul3, eval_c, eval_not, eval_sub, eval_add] at h1 h2 h3 h4 h5
  refine ⟨by grind, fun h => ?_, fun h h' => ?_, fun h => ?_⟩
  · rw [h] at h2 h3; exact ⟨by grind, by grind⟩
  · rw [h, h'] at h4; grind
  · rw [h] at h5; grind

theorem lastR_eq {r : Nat} (hq : r + 1 < tr.height T_RCPT) :
    tr.cell T_RCPT r lastR = tr.cell T_RCPT r rl * (1 - tr.cell T_RCPT (r + 1) act) := by
  have h1 := con hL (by omega : r < _) (e := sub (c lastR) (.mul (c rl) (Dsl.not (n act))))
    (mem_st (by simp [cStates]))
  simp only [eval_mul, eval_c, eval_not, eval_sub, eval_n, nxt hq] at h1
  grind

/-- After the claim rows: the first receipt. -/
theorem firstRcpt {r : Nat} (hq : r + 1 < tr.height T_RCPT) (he : tr.cell T_RCPT r fe = 1)
    (hc : tr.cell T_RCPT r sCL = 1) :
    tr.cell T_RCPT (r + 1) Rcpt.r = 0 ∧ tr.cell T_RCPT (r + 1) o = 12 ∧ tr.cell T_RCPT (r + 1) o2 = 4 ∧
    tr.cell T_RCPT (r + 1) rcnt = 0 := by
  have hq' : r < tr.height T_RCPT := by omega
  have h1 := con hL hq' (e := mul3 (c fe) (c sCL) (n Rcpt.r)) (mem_st (by simp [cStates]))
  have h2 := con hL hq' (e := mul3 (c fe) (c sCL) (sub (n o) (k 12))) (mem_st (by simp [cStates]))
  have h3 := con hL hq' (e := mul3 (c fe) (c sCL) (sub (n o2) (k 4))) (mem_st (by simp [cStates]))
  have h4 := con hL hq' (e := mul3 (c fe) (c sCL) (n rcnt)) (mem_st (by simp [cStates]))
  simp only [eval_mul3, eval_c, eval_n, eval_sub, eval_k, nxt hq] at h1 h2 h3 h4
  rw [he, hc] at h1 h2 h3 h4
  exact ⟨by grind, by grind, by grind, by grind⟩

/-- After a receipt end: the next receipt (if any). -/
theorem nextRcpt {r : Nat} (hq : r + 1 < tr.height T_RCPT) (hl : tr.cell T_RCPT r rl = 1)
    (ha : tr.cell T_RCPT (r + 1) act = 1) :
    tr.cell T_RCPT (r + 1) rf = 1 ∧
    tr.cell T_RCPT (r + 1) Rcpt.r = tr.cell T_RCPT r Rcpt.r + 1 ∧
    tr.cell T_RCPT (r + 1) o = tr.cell T_RCPT r oEnd ∧ tr.cell T_RCPT (r + 1) o2 = tr.cell T_RCPT r o2End ∧
    tr.cell T_RCPT (r + 1) rcnt = tr.cell T_RCPT r rcnt + tr.cell T_RCPT r Rcpt.hr := by
  have hq' : r < tr.height T_RCPT := by omega
  have h0 := con hL hq' (e := mul3 (c rl) (n act) (Dsl.not (n rf))) (mem_st (by simp [cStates]))
  have h1 := con hL hq' (e := mul3 (c rl) (n act) (sub (n Rcpt.r) (.add (c Rcpt.r) (k 1))))
    (mem_st (by simp [cStates]))
  have h2 := con hL hq' (e := mul3 (c rl) (n act) (sub (n o) (c oEnd))) (mem_st (by simp [cStates]))
  have h3 := con hL hq' (e := mul3 (c rl) (n act) (sub (n o2) (c o2End))) (mem_st (by simp [cStates]))
  have h4 := con hL hq' (e := mul3 (c rl) (n act) (sub (n rcnt) (.add (c rcnt) (c Rcpt.hr))))
    (mem_st (by simp [cStates]))
  simp only [eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_k, nxt hq] at h0 h1 h2 h3 h4
  rw [hl, ha] at h0 h1 h2 h3 h4
  exact ⟨by grind, by grind, by grind, by grind, by grind⟩

/-- Receipt sizes (on receipt rows). -/
theorem sizes {r : Nat} (hq : r < tr.height T_RCPT) (ha : tr.cell T_RCPT r act = 1)
    (hc : tr.cell T_RCPT r sCL = 0) :
    tr.cell T_RCPT r oEnd = tr.cell T_RCPT r o + ((123 : Nat) + (tr.cell T_RCPT r Lp +
      (tr.cell T_RCPT r Lv + (tr.cell T_RCPT r Ls + ((32 : Nat) * tr.cell T_RCPT r kt + 0))))) ∧
    tr.cell T_RCPT r o2End = tr.cell T_RCPT r o2 + tr.cell T_RCPT r Rcpt.hr *
      ((129 : Nat) + ((2 : Nat) * tr.cell T_RCPT r Ls + ((32 : Nat) * tr.cell T_RCPT r kt + 0))) := by
  have h1 := con hL hq (e := .mul rowE (sub (c oEnd) (.add (c o) (.add (k 123) varE))))
    (mem_st (by simp [cStates]))
  have h2 := con hL hq (e := .mul rowE (sub (c o2End)
      (.add (c o2) (.mul (c Rcpt.hr) (sum [k 129, smul 2 (c Ls), smul 32 (c kt)])))))
    (mem_st (by simp [cStates]))
  simp only [rowE, varE, eval_mul, eval_c, eval_sub, eval_add, eval_k, eval_smul, eval_sum_cons,
    eval_sum_nil] at h1 h2
  rw [ha, hc] at h1 h2
  exact ⟨by grind, by grind⟩

/-- Receipt constants are kept inside a receipt. -/
theorem rconst {r : Nat} (hq : r + 1 < tr.height T_RCPT) (ha : tr.cell T_RCPT r act = 1)
    (hc : tr.cell T_RCPT r sCL = 0) (hl : tr.cell T_RCPT r rl = 0) :
    ∀ x ∈ rconsts, tr.cell T_RCPT (r + 1) x = tr.cell T_RCPT r x := by
  intro x hx
  have h := con hL (by omega : r < _) (e := mul3 rowE (Dsl.not (c rl)) (sub (n x) (c x))) (mem_st (by
    unfold cStates; simp only [List.mem_append]; exact Or.inr (List.mem_map_of_mem hx)))
  simp only [rowE, eval_mul3, eval_c, eval_not, eval_sub, eval_n, nxt hq] at h
  rw [ha, hc, hl] at h; grind

end ZkFormal.Near.RcptProof

namespace ZkFormal.Near.RcptProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt
variable {tr : Trace Fp} {pub : List Fp}

theorem rf_idx (hL : TableLocal Rcpt.table tr T_RCPT pub) {r : Nat} (hq : r < tr.height T_RCPT)
    (h : tr.cell T_RCPT r rf = 1) : tr.cell T_RCPT r idx = 0 := by
  have h1 := con hL hq (e := .mul (c rf) (c idx)) (mem_st (by simp [cStates]))
  simp only [eval_mul, eval_c] at h1
  rw [h] at h1; grind

/-- `rl` at a row in state `x`. -/
theorem rl_at (hL : TableLocal Rcpt.table tr T_RCPT pub) {r x : Nat} (hq : r < tr.height T_RCPT)
    (hx : x ∈ states) (h1 : tr.cell T_RCPT r x = 1) :
    tr.cell T_RCPT r rl = tr.cell T_RCPT r fe *
      ((if x = sXRZ then 1 else 0) + (if x = sXLH then 1 else 0) * (1 - tr.cell T_RCPT r Rcpt.hr)) := by
  have hb := (bounds hL hq).1
  have oh := (oneHot hL hq hx h1).2
  have e1 : tr.cell T_RCPT r sXRZ = if x = sXRZ then 1 else 0 := by
    split
    · rename_i h; subst h; exact h1
    · rename_i h; exact oh sXRZ (by simp [states]) (Ne.symm h)
  have e2 : tr.cell T_RCPT r sXLH = if x = sXLH then 1 else 0 := by
    split
    · rename_i h; subst h; exact h1
    · rename_i h; exact oh sXLH (by simp [states]) (Ne.symm h)
  rw [hb, e1, e2]

end ZkFormal.Near.RcptProof
