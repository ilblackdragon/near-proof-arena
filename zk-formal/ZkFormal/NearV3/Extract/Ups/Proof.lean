import ZkFormal.NearV3.Extract.Ups.Rows

/-!
# ZkFormal.NearV3.Extract.Ups.Proof — `ups_view : UpsViewStmt` (layer 1)

The active rows of `upsV3` are consecutive instance segments (`W0` … root part end,
`segments_of`); every row satisfies `URowOk` with its successor (`rowOk`); inactive rows emit
nothing (`quiet`); every interaction is pure, so a row's traffic is `uMsgs` of its cells.
-/

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

variable {tr : Trace Fp} {pub : List Fp} {t : Nat}

theorem rowC_lt (tr : Trace Fp) (t r x : Nat) : rowC tr t r x < P := cv_lt _ _ _ _

/-! ## The three selector constraints -/

section
variable (hL : TableLocal UpsV3.table tr t pub)
include hL

theorem mem_rows {e : Expr} (h : e ∈ cRows) : e ∈ UpsV3.constraints := by
  unfold UpsV3.constraints; simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))))

theorem start0 : cv tr t 0 sf = 1 := by
  have h := hL.constr 0 (by unfold Trace.height; exact Nat.two_pow_pos _)
    (.mul .isFirst (not (c sf))) (mem_rows hL (by simp [cRows]))
  simp only [Expr.eval, Expr.evalWith, rowEnv, Dsl.not, Dsl.sub, Dsl.k, Dsl.c, if_true, if_false,
    Bool.false_eq_true] at h
  rw [← ofNat_cv] at h
  exact natv (cv_lt _ _ _ _) (by have := P_gt; omega) (by rw [← cast_ofNat]; grind)

theorem padStep {r : Nat} (hr : r + 1 < tr.height t) (ha : cv tr t r act ≠ 1) : cv tr t (r + 1) act ≠ 1 := by
  have hb := (kinds (rowOk tr t pub hL (r := r) (by omega)) (rowC_lt tr t r) (rowC_lt tr t _)).1
  have h := hL.constr r (by omega) (mul3 .isTransition (not (c act)) (n act)) (mem_rows hL (by simp [cRows]))
  simp only [Expr.eval, Expr.evalWith, rowEnv, Dsl.not, Dsl.sub, Dsl.k, Dsl.c, Dsl.n, Dsl.mul3, if_true,
    if_false, Bool.false_eq_true, show ¬ (r + 1 = tr.height t) by omega, Nat.mod_eq_of_lt hr] at h
  have h0 : cv tr t r act = 0 := by simp only [rowC] at hb; omega
  rw [← ofNat_cv tr t r, ← ofNat_cv tr t (r + 1), h0] at h
  intro h1; rw [h1] at h
  exact absurd h (by decide)

theorem stopLast (hH : 0 < tr.height t) : cv tr t (tr.height t - 1) act ≠ 1 := by
  have h := hL.constr (tr.height t - 1) (by omega) (.mul .isLast (c act)) (mem_rows hL (by simp [cRows]))
  simp only [Expr.eval, Expr.evalWith, rowEnv, Dsl.c, show tr.height t - 1 + 1 = tr.height t by omega,
    if_true, if_false, Bool.false_eq_true] at h
  rw [← ofNat_cv] at h
  intro h1; rw [h1] at h; exact absurd h (by decide)

end

/-! ## Segments -/

theorem rowC_eq (tr : Trace Fp) (t r x : Nat) : rowC tr t r x = cv tr t r x := rfl

attribute [local irreducible] rowC

def actB (tr : Trace Fp) (t r : Nat) : Bool := decide (rowC tr t r act = 1)
def firstB (tr : Trace Fp) (t r : Nat) : Bool := decide (rowC tr t r sf = 1)
def lastB (tr : Trace Fp) (t r : Nat) : Bool :=
  decide (rowC tr t r qb = 1 ∧ rowC tr t r pl = 1 ∧ rowC tr t r rootP = 1)

section
variable (hL : TableLocal UpsV3.table tr t pub)
include hL

theorem okAt {r : Nat} (hr : r + 1 < tr.height t) : URowOk (rowC tr t r) (rowC tr t (r + 1)) := by
  have := rowOk tr t pub hL (r := r) (by omega); rwa [Nat.mod_eq_of_lt hr] at this

theorem segFacts : SegFacts (tr.height t) (actB tr t) (firstB tr t) (lastB tr t) := by
  have hH : 0 < tr.height t := by unfold Trace.height; exact Nat.two_pow_pos _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr h
    obtain ⟨b0, e1, e2, -⟩ := kinds (rowOk tr t pub hL (r := r) hr) (rowC_lt tr t r) (rowC_lt tr t _)
    simp only [actB, firstB, decide_eq_true_eq] at h ⊢; omega
  · intro r hr h
    obtain ⟨b0, e1, e2, -⟩ := kinds (rowOk tr t pub hL (r := r) hr) (rowC_lt tr t r) (rowC_lt tr t _)
    simp only [actB, lastB, decide_eq_true_eq] at h ⊢; omega
  · intro r hr ha hl
    obtain ⟨b0, e1, e2, bs, b1, b2, b3, bv, bq, bw, bp, t1, t2, t3, t4, t5, t6, t7, t8, -⟩ :=
      kinds (okAt hL hr) (rowC_lt tr t r) (rowC_lt tr t (r + 1))
    obtain ⟨c0, f1, f2, cs, c1, c2, c3, cv', cq, cw, -⟩ :=
      kinds (rowOk tr t pub hL (r := r + 1) hr) (rowC_lt tr t (r + 1)) (rowC_lt tr t _)
    simp only [actB, firstB, lastB, decide_eq_true_eq, decide_eq_false_iff_not] at ha hl ⊢
    have := le1 b0; have := le1 bs; have := le1 b1; have := le1 b2; have := le1 b3; have := le1 bv
    have := le1 bq; have := le1 bw; have := le1 bp
    have := le1 c0; have := le1 cs; have := le1 c1; have := le1 c2; have := le1 c3; have := le1 cv'
    have := le1 cq; have := le1 cw
    clear b0 bs b1 b2 b3 bv bq bw bp c0 cs c1 c2 c3 cv' cq cw
    have hD : rowC tr t (r + 1) wt1 = 1 ∨ rowC tr t (r + 1) wt2 = 1 ∨ rowC tr t (r + 1) wt3 = 1 ∨
        rowC tr t (r + 1) vb = 1 ∨ rowC tr t (r + 1) qb = 1 := by
      by_cases hq : rowC tr t r qb = 1
      · by_cases hp : rowC tr t r pl = 1
        · exact Or.inr (Or.inr (Or.inr (Or.inr (t8 hq hp (fun h => hl ⟨hq, hp, h⟩)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (t7 hq (by omega)))))
      · by_cases hv : rowC tr t r vb = 1
        · by_cases hp : rowC tr t r pl = 1
          · exact Or.inr (Or.inr (Or.inr (Or.inr (t6 hv hp))))
          · exact Or.inr (Or.inr (Or.inr (Or.inl (t5 hv (by omega)))))
        · by_cases h0 : rowC tr t r sf = 1
          · exact Or.inl (t1 h0)
          · by_cases h1 : rowC tr t r wt1 = 1
            · exact Or.inr (Or.inl (t2 h1))
            · by_cases h2 : rowC tr t r wt2 = 1
              · exact Or.inr (Or.inr (Or.inl (t3 h2)))
              · exact Or.inr (Or.inr (Or.inr (Or.inl (t4 (by omega)))))
    clear t1 t2 t3 t4 t5 t6 t7 t8
    omega
  · intro r hr hl ha
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, t9⟩ :=
      kinds (okAt hL hr) (rowC_lt tr t r) (rowC_lt tr t (r + 1))
    simp only [actB, firstB, lastB, decide_eq_true_eq] at hl ha ⊢
    rw [← t9 hl.1 hl.2.1 hl.2.2]; exact ha
  · intro r hr ha
    simp only [actB, decide_eq_false_iff_not] at ha ⊢
    rw [rowC_eq] at ha ⊢
    exact padStep hL hr ha
  · intro _; simp only [firstB, decide_eq_true_eq]; rw [rowC_eq]; exact start0 hL
  · intro _ ha
    simp only [actB, decide_eq_true_eq] at ha
    rw [rowC_eq] at ha
    exact absurd ha (stopLast hL hH)

end

/-! ## The view -/

def segOf (tr : Trace Fp) (t : Nat) (p : Nat × Nat) : UpsSeg :=
  ⟨(List.range p.2).map fun d => rowC tr t (p.1 + d), rowC tr t ((p.1 + p.2) % tr.height t)⟩

def viewOf (tr : Trace Fp) (t : Nat) (segs : List (Nat × Nat)) : List UpsSeg := segs.map (segOf tr t)

theorem segOf_len (tr : Trace Fp) (t : Nat) (p : Nat × Nat) : (segOf tr t p).rows.length = p.2 := by
  simp [segOf]

theorem segOf_row (tr : Trace Fp) (t : Nat) (p : Nat × Nat) {i : Nat} (hi : i < p.2) :
    (segOf tr t p).row i = rowC tr t (p.1 + i) := by
  simp [segOf, UpsSeg.row, List.getD_eq_getElem?_getD, hi]

theorem segOf_next (tr : Trace Fp) (t : Nat) (p : Nat × Nat) (hp : p.1 + p.2 ≤ tr.height t) {i : Nat}
    (hi : i < p.2) : (segOf tr t p).next i = rowC tr t ((p.1 + i + 1) % tr.height t) := by
  unfold UpsSeg.next
  rw [segOf_len]
  by_cases h : i + 1 < p.2
  · rw [if_pos h, segOf_row tr t p h, Nat.mod_eq_of_lt (by omega)]; rfl
  · rw [if_neg h, show p.1 + i + 1 = p.1 + p.2 by omega]; rfl

theorem sum_segEnd : ∀ (segs : List (Nat × Nat)) (s0 : Nat), Consec s0 segs →
    (segs.map (·.2)).sum + s0 = segEnd s0 segs
  | [], _, _ => by simp [segEnd]
  | (s, ℓ) :: rest, s0, ⟨h1, h2⟩ => by
    have := sum_segEnd rest (s0 + ℓ) h2
    simp only [List.map_cons, List.sum_cons, segEnd]; subst h1; omega

/-- Pure interactions: the trace traffic of a row is `uMsgs` of its cells. -/
theorem rowTraffic_eq (tr : Trace Fp) (t r : Nat) (pub : List Fp) (b : Nat) (sd : Bool) :
    rowTraffic UpsV3.interactions tr t r pub b sd =
      (uMsgs (rowC tr t r) (rowC tr t ((r + 1) % tr.height t)) b sd).map Msg.toFp := by
  unfold rowTraffic uMsgs
  rw [List.map_flatMap]
  have hp := interactions_pure
  rw [List.all_eq_true] at hp
  apply flatMap_congr'
  intro i hi
  have hi' := hp i hi
  simp only [Bool.and_eq_true, List.all_eq_true] at hi'
  obtain ⟨hg, hm⟩ := hi'
  unfold pureGate at hg
  split at hg
  · rename_i g hgm
    by_cases hc : i.bus = b ∧ i.send = sd
    · rw [if_pos hc, if_pos hc, List.map_replicate]
      congr 1
      · simp only [Interaction.multNat, Interaction.multNat.go, hgm, uMult, Nat.pow_zero, Nat.add_zero]
        rw [eval_pure tr t r pub g hg]
      · simp only [Interaction.msgVal, Msg.toFp, List.map_map]
        apply List.map_congr_left; intro e he
        simp only [Function.comp, Fp.ofNat_toNat]
        exact eval_pure tr t r pub e (hm e he)
    · rw [if_neg hc, if_neg hc]; rfl
  · exact absurd hg (by simp)

section
variable (hL : TableLocal UpsV3.table tr t pub)
include hL

theorem viewWf {segs : List (Nat × Nat)} (hc : Consec 0 segs) (he : segEnd 0 segs ≤ tr.height t)
    (hs : ∀ p ∈ segs, IsSeg (actB tr t) (firstB tr t) (lastB tr t) p.1 p.2) : UpsWf (viewOf tr t segs) := by
  have bound : ∀ p ∈ segs, p.1 + p.2 ≤ tr.height t := fun p hp => by
    have := seg_le_end segs 0 hc p hp; omega
  have mem : ∀ S ∈ viewOf tr t segs, ∃ p ∈ segs, S = segOf tr t p := by
    intro S hS; simp only [viewOf, List.mem_map] at hS; obtain ⟨p, hp, rfl⟩ := hS; exact ⟨p, hp, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro S hS; obtain ⟨p, hp, rfl⟩ := mem S hS
    refine ⟨fun i x => ?_, fun x => rowC_lt _ _ _ _⟩
    by_cases hi : i < p.2
    · rw [segOf_row tr t p hi]; exact rowC_lt _ _ _ _
    · simp only [UpsSeg.row, segOf, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range' ] at *
      rw [List.getElem?_eq_none (by simp; omega)]; simp only [Option.map_none, Option.getD_none]
      have := P_gt; omega
  · intro S hS i hi; obtain ⟨p, hp, rfl⟩ := mem S hS
    rw [segOf_len] at hi
    rw [segOf_row tr t p hi, segOf_next tr t p (bound p hp) hi]
    exact rowOk tr t pub hL (by have := bound p hp; omega)
  · intro S hS; obtain ⟨p, hp, rfl⟩ := mem S hS
    obtain ⟨h0, hf, -⟩ := hs p hp
    refine ⟨by rw [segOf_len]; exact h0, ?_⟩
    rw [segOf_row tr t p h0, Nat.add_zero]; simpa [firstB] using hf
  · intro S hS i hi; obtain ⟨p, hp, rfl⟩ := mem S hS
    rw [segOf_len] at hi
    obtain ⟨-, -, -, ha, -⟩ := hs p hp
    rw [segOf_row tr t p hi]; simpa [actB] using ha (p.1 + i) (by omega) (by omega)
  · intro S hS i hi; obtain ⟨p, hp, rfl⟩ := mem S hS
    rw [segOf_len] at hi ⊢
    obtain ⟨h0, -, hl, -, -, hnl⟩ := hs p hp
    rw [segOf_row tr t p hi]
    constructor
    · intro h
      rcases Nat.lt_or_ge (i + 1) p.2 with hlt | hge
      · exfalso
        have := hnl (p.1 + i) (by omega) (by omega)
        simp only [lastB, decide_eq_false_iff_not] at this
        exact this h
      · omega
    · intro h
      have : p.1 + i = p.1 + p.2 - 1 := by omega
      rw [this]; simpa [lastB] using hl
  · intro S hS; obtain ⟨p, hp, rfl⟩ := mem S hS
    obtain ⟨h0, -, hl, -⟩ := hs p hp
    have hr : p.1 + p.2 - 1 < tr.height t := by have := bound p hp; omega
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, t9⟩ :=
      kinds (rowOk tr t pub hL hr) (rowC_lt tr t _) (rowC_lt tr t _)
    simp only [lastB, decide_eq_true_eq] at hl
    have := t9 hl.1 hl.2.1 hl.2.2
    rw [show p.1 + p.2 - 1 + 1 = p.1 + p.2 by omega] at this
    exact this
  · have e := sum_segEnd segs 0 hc
    have hlog := hL.log_le
    simp only [viewOf, List.map_map]
    have : ((segs.map ((·.rows.length) ∘ segOf tr t))) = segs.map (·.2) := by
      apply List.map_congr_left; intro p _; simp [segOf_len]
    rw [this]
    have hH : tr.height t ≤ 2 ^ 22 := by
      unfold Trace.height; exact Nat.pow_le_pow_right (by decide) (by simpa [UpsV3.table, UpsV3.maxLog] using hlog)
    omega

theorem viewTraffic {segs : List (Nat × Nat)} (hc : Consec 0 segs) (he : segEnd 0 segs ≤ tr.height t)
    (hs : ∀ p ∈ segs, IsSeg (actB tr t) (firstB tr t) (lastB tr t) p.1 p.2)
    (hpad : ∀ r, segEnd 0 segs ≤ r → r < tr.height t → actB tr t r = false) :
    TableTraffic UpsV3.interactions tr t pub (upsTraffic (viewOf tr t segs)) := by
  have bound : ∀ p ∈ segs, p.1 + p.2 ≤ tr.height t := fun p hp => by
    have := seg_le_end segs 0 hc p hp; omega
  have all : ∀ sd b, (List.range (tr.height t)).flatMap (fun r => rowTraffic UpsV3.interactions tr t r pub b sd) =
      ((viewOf tr t segs).flatMap (·.msgs b sd)).map Msg.toFp := by
    intro sd b
    rw [flatMap_congr' (fun r _ => rowTraffic_eq tr t r pub b sd), ← List.map_flatMap]
    congr 1
    rw [flatMap_rows_segs (tr.height t) segs _ hc he (fun r h1 h2 => by
      have ha := hpad r h1 h2
      simp only [actB, decide_eq_false_iff_not] at ha
      have b0 := (kinds (rowOk tr t pub hL (r := r) h2) (rowC_lt tr t r) (rowC_lt tr t _)).1
      exact quiet (rowOk tr t pub hL (r := r) h2) (rowC_lt tr t r) (rowC_lt tr t _) (by omega) b sd)]
    simp only [viewOf, List.flatMap_map]
    apply flatMap_congr'; intro p hp
    simp only [UpsSeg.msgs, segOf_len]
    rw [List.range'_eq_map_range, List.flatMap_map]
    apply flatMap_congr'; intro i hi; rw [List.mem_range] at hi
    rw [segOf_row tr t p hi, segOf_next tr t p (bound p hp) hi]
  intro b m
  refine ⟨?_, ?_⟩
  · rw [tableBusCount_eq, all true b]; rfl
  · rw [tableBusCount_eq, all false b]; rfl

end

end ZkFormal.NearV3.UpsRows

namespace ZkFormal.NearV3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- Table `t` of `tr`, placed at every index. -/
def upsFocus (tr : Trace Fp) (t : Nat) : Trace Fp := ⟨fun _ => tr.log t, fun _ => tr.cell t⟩

/-- **The `upsV3` table extracts** (any table index; layer 1). -/
theorem ups_view : UpsViewStmt := by
  intro tr pub t hL
  obtain ⟨segs, hc, he, hs, hpad⟩ := segments_of (UpsRows.segFacts hL)
    (by unfold Trace.height; exact Nat.two_pow_pos _)
  exact ⟨UpsRows.viewOf tr t segs, UpsRows.viewWf hL hc he hs, UpsRows.viewTraffic hL hc he hs hpad⟩

end ZkFormal.NearV3
