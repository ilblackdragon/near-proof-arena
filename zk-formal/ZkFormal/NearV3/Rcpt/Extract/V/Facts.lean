import ZkFormal.NearV3.Rcpt.Extract.RcptView
import ZkFormal.Near.Extract.Segments
import ZkFormal.Near.Extract.BusCount

/-!
# ZkFormal.NearV3.Rcpt.Extract.V.Facts — row facts of the `rcpt` table (control)

Each lemma reads a few constraints of `Tables/Rcpt/Fields.lean` on one row
(and the next row): booleans, one-hot field states, field bookkeeping
(`idx fs fe`), field lengths and successions, receipt boundaries and the
receipt constants.
-/

namespace ZkFormal.NearV3.RcptV3Proof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.RcptV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem con (hL : TableLocal RcptV3.table tr tt pub) {r : Nat} (hq : r < tr.height tt)
    {e : Expr} (he : e ∈ RcptV3.constraints) : e.eval tr tt r pub = 0 :=
  hL.constr r hq e he

theorem nxt {r : Nat} (h : r + 1 < tr.height tt) : (r + 1) % tr.height tt = r + 1 :=
  Nat.mod_eq_of_lt h

theorem mem_st {e : Expr} (h : e ∈ cStates) : e ∈ RcptV3.constraints := by
  unfold RcptV3.constraints; simp [h]
theorem mem_em {e : Expr} (h : e ∈ cEmit) : e ∈ RcptV3.constraints := by
  unfold RcptV3.constraints; simp [h]
theorem mem_rg {e : Expr} (h : e ∈ cRegs) : e ∈ RcptV3.constraints := by
  unfold RcptV3.constraints; simp [h]
theorem mem_ch {e : Expr} (h : e ∈ cChars) : e ∈ RcptV3.constraints := by
  unfold RcptV3.constraints; simp [h]
theorem mem_ky {e : Expr} (h : e ∈ cKey) : e ∈ RcptV3.constraints := by
  unfold RcptV3.constraints; simp [h]
theorem mem_gs {e : Expr} (h : e ∈ cGas) : e ∈ RcptV3.constraints := by
  unfold RcptV3.constraints; simp [h]
theorem mem_dp {e : Expr} (h : e ∈ cDep) : e ∈ RcptV3.constraints := by
  unfold RcptV3.constraints; simp [h]
theorem mem_sy {e : Expr} (h : e ∈ cSys) : e ∈ RcptV3.constraints := by
  unfold RcptV3.constraints; simp [h]
theorem mem_ro {e : Expr} (h : e ∈ cRoute) : e ∈ RcptV3.constraints := by
  unfold RcptV3.constraints; simp [h]
theorem mem_en {e : Expr} (h : e ∈ cEnd) : e ∈ RcptV3.constraints := by
  unfold RcptV3.constraints; simp [h]


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

variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

theorem height_le : tr.height tt ≤ 2 ^ 22 := by
  have := hL.log_le; unfold Trace.height; exact Nat.pow_le_pow_right (by omega) this

theorem height_ge : 2 ≤ tr.height tt := by
  have := hL.log_ge; unfold Trace.height
  calc 2 = 2 ^ 1 := rfl
    _ ≤ _ := Nat.pow_le_pow_right (by omega) this

theorem isBool {r : Nat} (hq : r < tr.height tt) {x : Nat} (hx : x ∈ boolCols) :
    tr.cell tt r x = 0 ∨ tr.cell tt r x = 1 := by
  have hm := List.mem_map_of_mem (f := fun x => Dsl.bool (c x)) hx
  have := con hL hq (e := Dsl.bool (c x)) (mem_st (by
    unfold cStates; simp only [List.mem_append, hm, true_or]))
  simp only [eval_bool, eval_c] at this
  exact bool_cases this

theorem bool01 {r x : Nat} (hq : r < tr.height tt) (hx : x ∈ boolCols) (h : ¬ tr.cell tt r x = 1) :
    tr.cell tt r x = 0 := (isBool hL hq hx).resolve_right h

theorem states_bool {r : Nat} (hq : r < tr.height tt) :
    ∀ x ∈ states, tr.cell tt r x = 0 ∨ tr.cell tt r x = 1 :=
  fun x hx => isBool hL hq (by unfold boolCols; simp only [List.mem_append, hx, true_or, or_true])

theorem sumStates {r : Nat} (hq : r < tr.height tt) :
    fsum (tr.cell tt r) states = tr.cell tt r act := by
  have := con hL hq (e := sub (sum (states.map c)) (c act)) (mem_st (by simp [cStates]))
  simp only [eval_sub, eval_c, eval_sum_map_c] at this
  grind

/-- **One-hot field states.** -/
theorem oneHot {r : Nat} (hq : r < tr.height tt) {x : Nat} (hx : x ∈ states)
    (h1 : tr.cell tt r x = 1) :
    tr.cell tt r act = 1 ∧ ∀ y ∈ states, y ≠ x → tr.cell tt r y = 0 :=
  oneHot_of _ states (by decide) _ (states_bool hL hq) (isBool hL hq (by simp [boolCols]))
    (sumStates hL hq) hx h1

/-- An inactive row has no state. -/
theorem noState {r : Nat} (hq : r < tr.height tt) (ha : tr.cell tt r act = 0) :
    ∀ x ∈ states, tr.cell tt r x = 0 := by
  intro x hx
  rcases states_bool hL hq x hx with h | h
  · exact h
  · have := (oneHot hL hq hx h).1; rw [ha] at this; exact absurd this fp_zero_ne_one

/-! ## Field bookkeeping -/

/-- Inside a field: same state, `idx + 1`, not a field start, active. -/
theorem inField {r : Nat} (hq : r + 1 < tr.height tt) (ha : tr.cell tt r act = 1)
    (he : tr.cell tt r fe = 0) :
    (∀ x ∈ states, tr.cell tt (r + 1) x = tr.cell tt r x) ∧
    tr.cell tt (r + 1) idx = tr.cell tt r idx + 1 ∧ tr.cell tt (r + 1) fs = 0 ∧
    tr.cell tt (r + 1) act = 1 := by
  have hq' : r < tr.height tt := by omega
  have h1 := con hL hq' (e := mul3 (c act) (Dsl.not (c fe)) (sub (n idx) (.add (c idx) (k 1))))
    (mem_st (by simp [cStates]))
  have h2 := con hL hq' (e := mul3 (c act) (Dsl.not (c fe)) (n fs)) (mem_st (by simp [cStates]))
  simp only [eval_mul3, eval_c, eval_not, eval_n, eval_sub, eval_add, eval_k, nxt hq] at h1 h2
  rw [ha, he] at h1 h2
  have hst : ∀ x ∈ states, tr.cell tt (r + 1) x = tr.cell tt r x := by
    intro x hx
    have h3 := con hL hq' (e := mul3 (c act) (Dsl.not (c fe)) (sub (n x) (c x)))
      (mem_st (by
        have hm := List.mem_map_of_mem (f := fun s => mul3 (c act) (Dsl.not (c fe)) (sub (n s) (c s))) hx
        unfold cStates; simp only [List.mem_append, hm, true_or, or_true]))
    simp only [eval_mul3, eval_c, eval_not, eval_n, eval_sub, nxt hq] at h3
    rw [ha, he] at h3; grind
  refine ⟨hst, by grind, by grind, ?_⟩
  have e1 := sumStates hL hq
  have e2 := sumStates hL hq'
  have : fsum (tr.cell tt (r + 1)) states = fsum (tr.cell tt r) states := by
    have gen : ∀ l : List Nat, (∀ x ∈ l, tr.cell tt (r + 1) x = tr.cell tt r x) →
        fsum (tr.cell tt (r + 1)) l = fsum (tr.cell tt r) l := by
      intro l; induction l with
      | nil => intro _; rfl
      | cons x l ih => intro h; simp only [fsum]; rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]
    exact gen states hst
  rw [← e1, this, e2, ha]

/-- After a field end, an active row starts a new field. -/
theorem afterField {r : Nat} (hq : r + 1 < tr.height tt) (he : tr.cell tt r fe = 1)
    (ha : tr.cell tt (r + 1) act = 1) :
    tr.cell tt (r + 1) idx = 0 ∧ tr.cell tt (r + 1) fs = 1 := by
  have hq' : r < tr.height tt := by omega
  have h1 := con hL hq' (e := mul3 (c fe) (n act) (n idx)) (mem_st (by simp [cStates]))
  have h2 := con hL hq' (e := mul3 (c fe) (n act) (Dsl.not (n fs))) (mem_st (by simp [cStates]))
  simp only [eval_mul3, eval_c, eval_not, eval_n, nxt hq] at h1 h2
  rw [he, ha] at h1 h2
  exact ⟨by grind, by grind⟩

/-- Field lengths: at a field end, `idx` is the field's last index. -/
theorem fieldEnd {r : Nat} (hq : r < tr.height tt) (he : tr.cell tt r fe = 1)
    {x : Nat} {e : Expr} (hx : (x, e) ∈ lastIdx) (h1 : tr.cell tt r x = 1) :
    tr.cell tt r idx = e.eval tr tt r pub := by
  have hm := List.mem_map_of_mem (f := fun (p : Nat × Expr) => mul3 (c fe) (c p.1) (sub (c idx) p.2)) hx
  have h := con hL hq (e := mul3 (c fe) (c x) (sub (c idx) e)) (mem_st (by
    unfold cStates; simp only [List.mem_append, hm, true_or, or_true]))
  simp only [eval_mul3, eval_c, eval_sub] at h
  rw [he, h1] at h; grind

/-- Field successions. -/
theorem fieldSucc {r : Nat} (hq : r + 1 < tr.height tt) (he : tr.cell tt r fe = 1)
    {x x' : Nat} {g : Expr} (hx : (x, x', g) ∈ RcptV3.succ) (h1 : tr.cell tt r x = 1)
    (hg : g.eval tr tt r pub = 1) : tr.cell tt (r + 1) x' = 1 := by
  have hq' : r < tr.height tt := by omega
  have hm := List.mem_map_of_mem (f := fun (p : Nat × Nat × Expr) => Expr.mul (mul3 (c fe) (c p.1) p.2.2)
        (Dsl.not (n p.2.1))) hx
  have h := con hL hq' (e := .mul (mul3 (c fe) (c x) g) (Dsl.not (n x'))) (mem_st (by
    unfold cStates; simp only [List.mem_append, hm, true_or, or_true]))
  simp only [eval_mul, eval_mul3, eval_c, eval_not, eval_n, nxt hq] at h
  rw [he, h1, hg] at h; grind

/-! ## First and last rows, padding -/

theorem row0 (h0 : 0 < tr.height tt) :
    tr.cell tt 0 sCL = 1 ∧ tr.cell tt 0 fs = 1 ∧ tr.cell tt 0 idx = 0 ∧
    tr.cell tt 0 act = 1 := by
  have h1 := con hL h0 (e := .mul .isFirst (Dsl.not (c sCL))) (mem_st (by simp [cStates]))
  have h2 := con hL h0 (e := .mul .isFirst (Dsl.not (c fs))) (mem_st (by simp [cStates]))
  have h3 := con hL h0 (e := .mul .isFirst (c idx)) (mem_st (by simp [cStates]))
  simp only [eval_mul, eval_c, eval_not, eval_isFirst, if_true] at h1 h2 h3
  have hs : tr.cell tt 0 sCL = 1 := by grind
  exact ⟨hs, by grind, by grind, (oneHot hL h0 (by simp [states]) hs).1⟩

theorem lastRow (h0 : 0 < tr.height tt) : tr.cell tt (tr.height tt - 1) act = 0 := by
  have h1 := con hL (by omega : tr.height tt - 1 < _) (e := .mul .isLast (c act))
    (mem_st (by simp [cStates]))
  simp only [eval_mul, eval_c, eval_isLast,
    if_pos (show tr.height tt - 1 + 1 = tr.height tt by omega)] at h1
  grind

theorem pad {r : Nat} (hq : r + 1 < tr.height tt) (ha : tr.cell tt r act = 0) :
    tr.cell tt (r + 1) act = 0 := by
  have h1 := con hL (by omega : r < _) (e := mul3 .isTransition (Dsl.not (c act)) (n act))
    (mem_st (by simp [cStates]))
  simp only [eval_mul3, eval_c, eval_not, eval_n, eval_isTransition, nxt hq,
    if_neg (show ¬ r + 1 = tr.height tt by omega)] at h1
  rw [ha] at h1; grind

/-- An active row is not the last row. -/
theorem act_lt {r : Nat} (hq : r < tr.height tt) (ha : tr.cell tt r act = 1) :
    r + 1 < tr.height tt := by
  rcases Nat.lt_or_ge (r + 1) (tr.height tt) with h | h
  · exact h
  · have : r = tr.height tt - 1 := by omega
    subst this; rw [lastRow hL (by omega)] at ha; exact absurd ha fp_zero_ne_one

/-! ## Receipt boundaries -/

theorem bounds {r : Nat} (hq : r < tr.height tt) :
    tr.cell tt r rl = tr.cell tt r fe *
      (tr.cell tt r sXRZ + tr.cell tt r sXLH * (1 - tr.cell tt r RcptV3.hr)) ∧
    (tr.cell tt r rf = 1 → tr.cell tt r sPL = 1 ∧ tr.cell tt r fs = 1) ∧
    (tr.cell tt r sPL = 1 → tr.cell tt r fs = 1 → tr.cell tt r rf = 1) ∧
    (tr.cell tt r RcptV3.hr = 1 → tr.cell tt r ge = 1) := by
  have h1 := con hL hq (e := sub (c rl) (.mul (c fe) (.add (c sXRZ) (.mul (c sXLH) (Dsl.not (c RcptV3.hr))))))
    (mem_st (by simp [cStates]))
  have h2 := con hL hq (e := .mul (c rf) (Dsl.not (c sPL))) (mem_st (by simp [cStates]))
  have h3 := con hL hq (e := .mul (c rf) (Dsl.not (c fs))) (mem_st (by simp [cStates]))
  have h4 := con hL hq (e := mul3 (c sPL) (c fs) (Dsl.not (c rf))) (mem_st (by simp [cStates]))
  have h5 := con hL hq (e := .mul (c RcptV3.hr) (Dsl.not (c ge))) (mem_st (by simp [cStates]))
  simp only [eval_mul, eval_mul3, eval_c, eval_not, eval_sub, eval_add] at h1 h2 h3 h4 h5
  refine ⟨by grind, fun h => ?_, fun h h' => ?_, fun h => ?_⟩
  · rw [h] at h2 h3; exact ⟨by grind, by grind⟩
  · rw [h, h'] at h4; grind
  · rw [h] at h5; grind

/-- The last row of a list (`le`) and of the active part (`lastR`). -/
theorem le_eq {r : Nat} (hq : r + 1 < tr.height tt) :
    tr.cell tt r le = (tr.cell tt r rl + tr.cell tt r sCL * tr.cell tt r fe) * (1 - tr.cell tt (r + 1) rf) ∧
    tr.cell tt r lastR = tr.cell tt r le * (1 - tr.cell tt (r + 1) act) := by
  have h1 := con hL (by omega : r < _) (e := sub (c le) (.mul brkE (Dsl.not (n rf))))
    (mem_st (by simp [cStates]))
  have h2 := con hL (by omega : r < _) (e := sub (c lastR) (.mul (c le) (Dsl.not (n act))))
    (mem_st (by simp [cStates]))
  simp only [brkE, lhEnd, eval_mul, eval_add, eval_c, eval_not, eval_sub, eval_n, nxt hq] at h1 h2
  exact ⟨by grind, by grind⟩

/-- After a header or a receipt: a receipt or a header. -/
theorem brkNext {r : Nat} (hq : r + 1 < tr.height tt)
    (hb : tr.cell tt r rl + tr.cell tt r sCL * tr.cell tt r fe = 1) (ha : tr.cell tt (r + 1) act = 1) :
    tr.cell tt (r + 1) sPL + tr.cell tt (r + 1) sCL = 1 := by
  have h1 := con hL (by omega : r < _) (e := mul3 brkE (n act) (Dsl.not (.add (n sPL) (n sCL))))
    (mem_st (by simp [cStates]))
  simp only [brkE, lhEnd, eval_mul3, eval_mul, eval_add, eval_c, eval_not, eval_n, nxt hq] at h1
  rw [hb, ha] at h1; grind

/-- First row: list `0`, receipt `0`, body position `8`, zero tokens. -/
theorem first0 (h0 : 0 < tr.height tt) :
    tr.cell tt 0 j = 0 ∧ tr.cell tt 0 RcptV3.r = 0 ∧ tr.cell tt 0 o2 = 8 := by
  have h1 := con hL h0 (e := .mul .isFirst (c j)) (mem_st (by simp [cStates]))
  have h2 := con hL h0 (e := .mul .isFirst (c RcptV3.r)) (mem_st (by simp [cStates]))
  have h3 := con hL h0 (e := .mul .isFirst (sub (c o2) (k 8))) (mem_st (by simp [cStates]))
  simp only [eval_mul, eval_c, eval_sub, eval_k, eval_isFirst, if_true] at h1 h2 h3
  exact ⟨by grind, by grind, by grind⟩

/-- Header rows: no receipt yet, `RC(j)` length 12, no body bytes; the header loads `n_j`. -/
theorem hdrRow {r : Nat} (hq : r < tr.height tt) (hc : tr.cell tt r sCL = 1) :
    tr.cell tt r cj = 0 ∧ tr.cell tt r oEnd = 12 ∧ tr.cell tt r o2End = tr.cell tt r o2 ∧
    (tr.cell tt r fs = 1 → tr.cell tt r nj = tr.cell tt r (reg 8) + 256 * tr.cell tt r (reg 9) ∧
      tr.cell tt r (reg 10) = 0 ∧ tr.cell tt r (reg 11) = 0) := by
  have h1 := con hL hq (e := .mul (c sCL) (c cj)) (mem_st (by simp [cStates]))
  have h2 := con hL hq (e := .mul (c sCL) (sub (c oEnd) (k 12))) (mem_st (by simp [cStates]))
  have h3 := con hL hq (e := .mul (c sCL) (sub (c o2End) (c o2))) (mem_st (by simp [cStates]))
  have h4 := con hL hq (e := mul3 (c sCL) (c fs) (sub (c nj) (.add (c (reg 8)) (smul 256 (c (reg 9))))))
    (mem_st (by simp [cStates]))
  have h5 := con hL hq (e := mul3 (c sCL) (c fs) (c (reg 10))) (mem_st (by simp [cStates]))
  have h6 := con hL hq (e := mul3 (c sCL) (c fs) (c (reg 11))) (mem_st (by simp [cStates]))
  simp only [eval_mul, eval_mul3, eval_c, eval_sub, eval_add, eval_k, eval_smul] at h1 h2 h3 h4 h5 h6
  rw [hc] at h1 h2 h3 h4 h5 h6
  refine ⟨by grind, by grind, by grind, fun hf => ?_⟩
  rw [hf] at h4 h5 h6
  exact ⟨by grind, by grind, by grind⟩

/-- Header rows carry `r` and `o2`. -/
theorem hdrCarry {r : Nat} (hq : r + 1 < tr.height tt) (hc : tr.cell tt r sCL = 1)
    (he : tr.cell tt r fe = 0) :
    tr.cell tt (r + 1) RcptV3.r = tr.cell tt r RcptV3.r ∧ tr.cell tt (r + 1) o2 = tr.cell tt r o2 := by
  have h1 := con hL (by omega : r < _) (e := mul3 (c sCL) (Dsl.not (c fe)) (sub (n RcptV3.r) (c RcptV3.r)))
    (mem_st (by simp [cStates]))
  have h2 := con hL (by omega : r < _) (e := mul3 (c sCL) (Dsl.not (c fe)) (sub (n o2) (c o2)))
    (mem_st (by simp [cStates]))
  simp only [eval_mul3, eval_c, eval_not, eval_sub, eval_n, nxt hq] at h1 h2
  rw [hc, he] at h1 h2
  exact ⟨by grind, by grind⟩

/-- After a header's or a receipt's last row (`brk`): `r` counts receipts; a following
receipt continues the list's count and offsets; the body position is carried. -/
theorem brkStep {r : Nat} (hq : r + 1 < tr.height tt)
    (hb : tr.cell tt r rl + tr.cell tt r sCL * tr.cell tt r fe = 1) (ha : tr.cell tt (r + 1) act = 1) :
    tr.cell tt (r + 1) RcptV3.r = tr.cell tt r RcptV3.r + tr.cell tt r rl ∧
    (tr.cell tt (r + 1) rf = 1 → tr.cell tt (r + 1) cj = tr.cell tt r cj + 1 ∧
      tr.cell tt (r + 1) o = tr.cell tt r oEnd) ∧
    tr.cell tt (r + 1) o2 = tr.cell tt r o2End := by
  have h1 := con hL (by omega : r < _) (e := .mul (n act) (.mul brkE (sub (n RcptV3.r) (.add (c RcptV3.r) (c rl)))))
    (mem_st (by simp [cStates]))
  have h2 := con hL (by omega : r < _) (e := .mul (n rf) (.mul brkE (sub (n cj) (.add (c cj) (k 1)))))
    (mem_st (by simp [cStates]))
  have h3 := con hL (by omega : r < _) (e := .mul (n rf) (.mul brkE (sub (n o) (c oEnd))))
    (mem_st (by simp [cStates]))
  have h4 := con hL (by omega : r < _) (e := .mul (n act) (.mul (.add (c sCL) (c rl)) (sub (n o2) (c o2End))))
    (mem_st (by simp [cStates]))
  simp only [brkE, lhEnd, eval_mul, eval_add, eval_c, eval_sub, eval_n, eval_k, nxt hq] at h1 h2 h3 h4
  rw [hb, ha] at h1
  refine ⟨by grind, fun hrf => ?_, ?_⟩
  · rw [hb, hrf] at h2 h3; exact ⟨by grind, by grind⟩
  · -- `sCL + rl = 1` at a header end or a receipt end
    have : tr.cell tt r sCL + tr.cell tt r rl = 1 := by
      rcases isBool hL (r := r) (by omega) (x := fe) (by simp [boolCols]) with hf | hf
      · rw [hf] at hb
        have hrl : tr.cell tt r rl = 1 := by grind
        have hc0 : tr.cell tt r sCL = 0 := by
          have := (bounds hL (r := r) (by omega)).1; rw [hf] at this; rw [this] at hrl; grind
        grind
      · rw [hf] at hb
        rcases isBool hL (r := r) (by omega) (x := rl) (by simp [boolCols]) with h' | h'
        · rw [h'] at hb ⊢; grind
        · have := (bounds hL (r := r) (by omega)).1
          rw [h', hf] at this
          -- `rl = 1` at a field end means state XRZ / XLH, not CL
          rcases states_bool hL (r := r) (by omega) sCL (by simp [states]) with hc | hc
          · rw [hc]; grind
          · have oh := (oneHot hL (r := r) (by omega) (by simp [states]) hc).2
            rw [oh sXRZ (by simp [states]) (by decide), oh sXLH (by simp [states]) (by decide)] at this
            grind
    rw [this, ha] at h4; grind

/-- The last row of a list: the list's receipt count is `nj`; a next list follows. -/
theorem leFacts {r : Nat} (hq : r + 1 < tr.height tt) (hle : tr.cell tt r le = 1) :
    tr.cell tt r cj = tr.cell tt r nj ∧
    (tr.cell tt (r + 1) act = 1 → tr.cell tt (r + 1) j = tr.cell tt r j + 1) := by
  have h1 := con hL (by omega : r < _) (e := .mul (c le) (sub (c cj) (c nj))) (mem_st (by simp [cStates]))
  have h2 := con hL (by omega : r < _) (e := mul3 (c le) (n act) (sub (n j) (.add (c j) (k 1))))
    (mem_st (by simp [cStates]))
  simp only [eval_mul, eval_mul3, eval_c, eval_sub, eval_add, eval_n, eval_k, nxt hq] at h1 h2
  rw [hle] at h1 h2
  exact ⟨by grind, fun ha => by rw [ha] at h2; grind⟩

/-- List constants are kept inside a list. -/
theorem lconst {r : Nat} (hq : r + 1 < tr.height tt) (ha : tr.cell tt r act = 1)
    (hle : tr.cell tt r le = 0) :
    ∀ x ∈ lconsts, tr.cell tt (r + 1) x = tr.cell tt r x := by
  intro x hx
  have hm := List.mem_map_of_mem (f := fun x => mul3 (c act) (Dsl.not (c le)) (sub (n x) (c x))) hx
  have h := con hL (by omega : r < _) (e := mul3 (c act) (Dsl.not (c le)) (sub (n x) (c x))) (mem_st (by
    unfold cStates; simp only [List.mem_append, hm, true_or, or_true]))
  simp only [eval_mul3, eval_c, eval_not, eval_sub, eval_n, nxt hq] at h
  rw [ha, hle] at h; grind

/-- Receipt sizes (on receipt rows). -/
theorem sizes {r : Nat} (hq : r < tr.height tt) (ha : tr.cell tt r act = 1)
    (hc : tr.cell tt r sCL = 0) :
    tr.cell tt r oEnd = tr.cell tt r o + ((123 : Nat) + (tr.cell tt r Lp +
      (tr.cell tt r Lv + (tr.cell tt r Ls + ((32 : Nat) * tr.cell tt r kt + 0))))) ∧
    tr.cell tt r o2End = tr.cell tt r o2 + tr.cell tt r RcptV3.hr *
      ((129 : Nat) + ((2 : Nat) * tr.cell tt r Ls + ((32 : Nat) * tr.cell tt r kt + 0))) := by
  have h1 := con hL hq (e := .mul rowE (sub (c oEnd) (.add (c o) (.add (k 123) varE))))
    (mem_st (by simp [cStates]))
  have h2 := con hL hq (e := .mul rowE (sub (c o2End)
      (.add (c o2) (.mul (c RcptV3.hr) (sum [k 129, smul 2 (c Ls), smul 32 (c kt)])))))
    (mem_st (by simp [cStates]))
  simp only [rowE, varE, eval_mul, eval_c, eval_sub, eval_add, eval_k, eval_smul, eval_sum_cons,
    eval_sum_nil] at h1 h2
  rw [ha, hc] at h1 h2
  exact ⟨by grind, by grind⟩

/-- Receipt constants are kept inside a receipt. -/
theorem rconst {r : Nat} (hq : r + 1 < tr.height tt) (ha : tr.cell tt r act = 1)
    (hc : tr.cell tt r sCL = 0) (hl : tr.cell tt r rl = 0) :
    ∀ x ∈ rconsts, tr.cell tt (r + 1) x = tr.cell tt r x := by
  intro x hx
  have hm := List.mem_map_of_mem (f := fun x => mul3 rowE (Dsl.not (c rl)) (sub (n x) (c x))) hx
  have h := con hL (by omega : r < _) (e := mul3 rowE (Dsl.not (c rl)) (sub (n x) (c x))) (mem_st (by
    unfold cStates; simp only [List.mem_append, hm, true_or, or_true]))
  simp only [rowE, eval_mul3, eval_c, eval_not, eval_sub, eval_n, nxt hq] at h
  rw [ha, hc, hl] at h; grind

end ZkFormal.NearV3.RcptV3Proof

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem rf_idx (hL : TableLocal RcptV3.table tr tt pub) {r : Nat} (hq : r < tr.height tt)
    (h : tr.cell tt r rf = 1) : tr.cell tt r idx = 0 := by
  have h1 := con hL hq (e := .mul (c rf) (c idx)) (mem_st (by simp [cStates]))
  simp only [eval_mul, eval_c] at h1
  rw [h] at h1; grind

/-- `rl` at a row in state `x`. -/
theorem rl_at (hL : TableLocal RcptV3.table tr tt pub) {r x : Nat} (hq : r < tr.height tt)
    (hx : x ∈ states) (h1 : tr.cell tt r x = 1) :
    tr.cell tt r rl = tr.cell tt r fe *
      ((if x = sXRZ then 1 else 0) + (if x = sXLH then 1 else 0) * (1 - tr.cell tt r RcptV3.hr)) := by
  have hb := (bounds hL hq).1
  have oh := (oneHot hL hq hx h1).2
  have e1 : tr.cell tt r sXRZ = if x = sXRZ then 1 else 0 := by
    split
    · rename_i h; subst h; exact h1
    · rename_i h; exact oh sXRZ (by simp [states]) (Ne.symm h)
  have e2 : tr.cell tt r sXLH = if x = sXLH then 1 else 0 := by
    split
    · rename_i h; subst h; exact h1
    · rename_i h; exact oh sXLH (by simp [states]) (Ne.symm h)
  rw [hb, e1, e2]

end ZkFormal.NearV3.RcptV3Proof
