import ZkFormal.NearV3.Render.Ups.CompactExtract.KindSteps
import ZkFormal.NearV3.Render.Ups.CompactExtract.NodeParts
import ZkFormal.NearV3.Extract.Ups.Proof
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows
variable {tr : Trace Fp} {pub : List Fp} {t : Nat}
section
variable (hL : TableLocal compactTable tr t pub)
include hL
theorem start0 : cv tr t 0 sf = 1 := by
  have h := hL.constr 0 (by unfold Trace.height; exact Nat.two_pow_pos _)
    (.mul .isFirst (not (c sf))) (by simp [compactTable,compactConstraints,compactRows,cRows])
  simp only [Expr.eval, Expr.evalWith, rowEnv, Dsl.not, Dsl.sub, Dsl.k, Dsl.c, if_true, if_false,
    Bool.false_eq_true] at h
  rw [← ofNat_cv] at h
  exact natv (cv_lt _ _ _ _) (by have := P_gt; omega) (by rw [← cast_ofNat]; grind)

theorem padStep {r : Nat} (hr : r + 1 < tr.height t) (ha : cv tr t r act ≠ 1) : cv tr t (r + 1) act ≠ 1 := by
  have hb := (kinds (rowOk hL (r := r) (by omega)) (rowC_lt tr t r) (rowC_lt tr t _)).1
  have h := hL.constr r (by omega) (mul3 .isTransition (not (c act)) (n act)) (by simp [compactTable,compactConstraints,compactRows,cRows])
  simp only [Expr.eval, Expr.evalWith, rowEnv, Dsl.not, Dsl.sub, Dsl.k, Dsl.c, Dsl.n, Dsl.mul3, if_true,
    if_false, Bool.false_eq_true, show ¬ (r + 1 = tr.height t) by omega, Nat.mod_eq_of_lt hr] at h
  have h0 : cv tr t r act = 0 := by simp only [rowC] at hb; omega
  rw [← ofNat_cv tr t r, ← ofNat_cv tr t (r + 1), h0] at h
  intro h1; rw [h1] at h
  exact absurd h (by decide)

theorem stopLast (hH : 0 < tr.height t) : cv tr t (tr.height t - 1) act ≠ 1 := by
  have h := hL.constr (tr.height t - 1) (by omega) (.mul .isLast (c act)) (by simp [compactTable,compactConstraints,compactRows,cRows])
  simp only [Expr.eval, Expr.evalWith, rowEnv, Dsl.c, show tr.height t - 1 + 1 = tr.height t by omega,
    if_true, if_false, Bool.false_eq_true] at h
  rw [← ofNat_cv] at h
  intro h1; rw [h1] at h; exact absurd h (by decide)

theorem okAt {r : Nat} (hr : r + 1 < tr.height t) : RowOk (rowC tr t r) (rowC tr t (r + 1)) := by
  have := rowOk hL (r := r) (by omega); rwa [Nat.mod_eq_of_lt hr] at this

theorem segFacts : SegFacts (tr.height t) (actB tr t) (firstB tr t) (lastB tr t) := by
  have hH : 0 < tr.height t := by unfold Trace.height; exact Nat.two_pow_pos _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr h
    obtain ⟨b0, e1, e2, -⟩ := kinds (rowOk hL (r := r) hr) (rowC_lt tr t r) (rowC_lt tr t _)
    simp only [actB, firstB, decide_eq_true_eq] at h ⊢; omega
  · intro r hr h
    obtain ⟨b0, e1, e2, -⟩ := kinds (rowOk hL (r := r) hr) (rowC_lt tr t r) (rowC_lt tr t _)
    simp only [actB, lastB, decide_eq_true_eq] at h ⊢; omega
  · intro r hr ha hl
    obtain ⟨b0, e1, e2, bs, b1, b2, b3, bv, bq, bw, bp, t1, t2, t3, t4, t5, t6, t7, t8, -⟩ :=
      kinds (okAt hL hr) (rowC_lt tr t r) (rowC_lt tr t (r + 1))
    obtain ⟨c0, f1, f2, cs, c1, c2, c3, cv', cq, cw, -⟩ :=
      kinds (rowOk hL (r := r + 1) hr) (rowC_lt tr t (r + 1)) (rowC_lt tr t _)
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
              · exact Or.inr (Or.inr (Or.inr (Or.inr (t4 (by omega)))))
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

theorem viewWf {segs : List (Nat × Nat)} (hc : Consec 0 segs) (he : segEnd 0 segs ≤ tr.height t)
    (hs : ∀ p ∈ segs, IsSeg (actB tr t) (firstB tr t) (lastB tr t) p.1 p.2) : Wf (viewOf tr t segs) := by
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
    exact rowOk hL (by have := bound p hp; omega)
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
      kinds (rowOk hL hr) (rowC_lt tr t _) (rowC_lt tr t _)
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
      unfold Trace.height; exact Nat.pow_le_pow_right (by decide) (by simpa [compactTable,UpsV3.table, UpsV3.maxLog] using hlog)
    omega

/-- An arbitrary satisfying compact physical table yields the compact segment
view, covering all active rows with canonical local equations. -/
theorem physical_view : ∃segs,
    Consec 0 segs ∧ segEnd 0 segs≤tr.height t ∧
    (∀p∈segs,IsSeg (actB tr t) (firstB tr t) (lastB tr t) p.1 p.2) ∧
    (∀r,segEnd 0 segs≤r → r<tr.height t → actB tr t r=false) ∧
    Wf (viewOf tr t segs) := by
  have hh : 0<tr.height t := by unfold Trace.height; exact Nat.two_pow_pos _
  obtain ⟨segs,hc,he,hs,hpad⟩:=segments_of (segFacts hL) hh
  exact ⟨segs,hc,he,hs,hpad,viewWf hL hc he hs⟩
end
end ZkFormal.NearV3.Render.UpsRelay.Extract
