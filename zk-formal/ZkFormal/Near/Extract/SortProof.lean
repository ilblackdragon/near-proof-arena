import ZkFormal.Near.Extract.SmallViews
import ZkFormal.Near.Extract.Segments
import ZkFormal.Near.Extract.BusCount

/-!
# ZkFormal.Near.Extract.SortProof — `SortViewStmt`

Pilot of the table-view extractions: constraint facts per row, segment
decomposition, view, traffic, and the ordering fact.
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace SortProof

variable {tr : Trace Fp} {pub : List Fp}

/-- Constraint `e` of the sort table holds on row `r`. -/
theorem con (hL : TableLocal Sort.table tr T_SORT pub) {r : Nat} (hr : r < tr.height T_SORT)
    {e : Expr} (he : e ∈ Sort.constraints) : e.eval tr T_SORT r pub = 0 :=
  hL.constr r hr e he

end SortProof

end ZkFormal.Near

namespace ZkFormal.Near.SortProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Sort

variable {tr : Trace Fp} {pub : List Fp}


theorem nxt {tr : Trace Fp} {r : Nat} (h : r + 1 < tr.height T_SORT) :
    (r + 1) % tr.height T_SORT = r + 1 := Nat.mod_eq_of_lt h

theorem mem_bool {x : Nat} (hx : x ∈ [act, sf, sl, ft, cin, cout] ++ (List.range 8).map dbit) :
    Dsl.bool (c x) ∈ Sort.constraints := by
  unfold Sort.constraints
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hx))

theorem isBool (hL : TableLocal Sort.table tr T_SORT pub) {r : Nat} (hr : r < tr.height T_SORT)
    {x : Nat} (hx : x ∈ [act, sf, sl, ft, cin, cout] ++ (List.range 8).map dbit) :
    tr.cell T_SORT r x = 0 ∨ tr.cell T_SORT r x = 1 := by
  have := con hL hr (mem_bool hx)
  simp only [eval_bool, eval_c] at this
  exact bool_cases this

/-- `a · b = 0` facts: `prod2 hL hr he` with `e = a * b` -/
theorem zero2 (hL : TableLocal Sort.table tr T_SORT pub) {r : Nat} (hr : r < tr.height T_SORT)
    {a b : Expr} (he : Expr.mul a b ∈ Sort.constraints) :
    a.eval tr T_SORT r pub = 0 ∨ b.eval tr T_SORT r pub = 0 :=
  mul_eq_zero'.mp (by simpa using con hL hr he)


theorem first_act (hL : TableLocal Sort.table tr T_SORT pub) {r : Nat} (hr : r < tr.height T_SORT)
    (h : tr.cell T_SORT r sf = 1) : tr.cell T_SORT r act = 1 := by
  have := con hL hr (e := .mul (c sf) (Dsl.not (c act))) (by simp [Sort.constraints])
  simp only [eval_mul, eval_c, eval_not] at this
  rw [h] at this
  grind

theorem cont (hL : TableLocal Sort.table tr T_SORT pub) {r : Nat} (hr : r + 1 < tr.height T_SORT)
    (ha : tr.cell T_SORT r act = 1) (hl : tr.cell T_SORT r sl = 0) : tr.cell T_SORT (r + 1) act = 1 ∧ tr.cell T_SORT (r + 1) sf = 0 := by
  have h1 := con hL (by omega : r < _) (e := mul3 (c act) (Dsl.not (c sl)) (Dsl.not (n act)))
    (by simp [Sort.constraints])
  have h2 := con hL (by omega : r < _) (e := mul3 (c act) (Dsl.not (c sl)) (n sf))
    (by simp [Sort.constraints])
  simp only [eval_mul3, eval_c, eval_not, eval_n, nxt hr] at h1 h2
  rw [ha, hl] at h1 h2
  constructor <;> grind


variable (hL : TableLocal Sort.table tr T_SORT pub)
include hL

theorem cval {r : Nat} (hr : r < tr.height T_SORT) {x : Nat}
    (hx : x ∈ [act, sf, sl, ft, cin, cout] ++ (List.range 8).map dbit) :
    tr.cell T_SORT r x = if tr.cell T_SORT r x = 1 then 1 else 0 := by
  rcases isBool hL hr hx with h | h <;> simp [h]

theorem last_act {r : Nat} (hr : r < tr.height T_SORT) (h : tr.cell T_SORT r sl = 1) :
    tr.cell T_SORT r act = 1 := by
  have := con hL hr (e := .mul (c sl) (Dsl.not (c act))) (by simp [Sort.constraints])
  simp only [eval_mul, eval_c, eval_not] at this
  rw [h] at this; grind

theorem within {r : Nat} (hr : r + 1 < tr.height T_SORT)
    (ha : tr.cell T_SORT r act = 1) (hl : tr.cell T_SORT r sl = 0) :
    tr.cell T_SORT (r + 1) rr = tr.cell T_SORT r rr ∧ tr.cell T_SORT (r + 1) ft = tr.cell T_SORT r ft ∧
    tr.cell T_SORT (r + 1) i = tr.cell T_SORT r i + 1 ∧
    tr.cell T_SORT (r + 1) cin = tr.cell T_SORT r cout := by
  have h1 := con hL (by omega : r < _) (e := mul3 (c act) (Dsl.not (c sl)) (sub (n rr) (c rr)))
    (by simp [Sort.constraints])
  have h2 := con hL (by omega : r < _) (e := mul3 (c act) (Dsl.not (c sl)) (sub (n ft) (c ft)))
    (by simp [Sort.constraints])
  have h3 := con hL (by omega : r < _)
    (e := mul3 (c act) (Dsl.not (c sl)) (sub (n i) (.add (c i) (k 1)))) (by simp [Sort.constraints])
  have h4 := con hL (by omega : r < _) (e := mul3 (c act) (Dsl.not (c sl)) (sub (n cin) (c cout)))
    (by simp [Sort.constraints])
  simp only [eval_mul3, eval_c, eval_not, eval_n, eval_sub, eval_add, eval_k, nxt hr] at h1 h2 h3 h4
  rw [ha, hl] at h1 h2 h3 h4
  refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

theorem nextSeg {r : Nat} (hr : r + 1 < tr.height T_SORT) (hl : tr.cell T_SORT r sl = 1)
    (ha : tr.cell T_SORT (r + 1) act = 1) :
    tr.cell T_SORT (r + 1) sf = 1 ∧ tr.cell T_SORT (r + 1) ft = 0 := by
  have h1 := con hL (by omega : r < _) (e := mul3 (c sl) (n act) (Dsl.not (n sf)))
    (by simp [Sort.constraints])
  have h2 := con hL (by omega : r < _) (e := mul3 (c sl) (n act) (n ft)) (by simp [Sort.constraints])
  simp only [eval_mul3, eval_c, eval_not, eval_n, nxt hr] at h1 h2
  rw [ha, hl] at h1 h2
  constructor <;> grind

theorem pad {r : Nat} (hr : r + 1 < tr.height T_SORT) (ha : tr.cell T_SORT r act = 0) :
    tr.cell T_SORT (r + 1) act = 0 := by
  have h1 := con hL (by omega : r < _) (e := mul3 .isTransition (Dsl.not (c act)) (n act))
    (by simp [Sort.constraints])
  simp only [eval_mul3, eval_c, eval_not, eval_n, eval_isTransition, nxt hr,
    if_neg (show ¬ r + 1 = tr.height T_SORT by omega)] at h1
  rw [ha] at h1; grind

theorem row0 (h0 : 0 < tr.height T_SORT) :
    tr.cell T_SORT 0 sf = 1 ∧ tr.cell T_SORT 0 ft = 1 := by
  have h1 := con hL h0 (e := .mul .isFirst (Dsl.not (c sf))) (by simp [Sort.constraints])
  have h2 := con hL h0 (e := .mul .isFirst (Dsl.not (c ft))) (by simp [Sort.constraints])
  simp only [eval_mul, eval_c, eval_not, eval_isFirst, if_pos rfl] at h1 h2
  constructor <;> grind

theorem lastRow (h0 : 0 < tr.height T_SORT) (ha : tr.cell T_SORT (tr.height T_SORT - 1) act = 1) :
    tr.cell T_SORT (tr.height T_SORT - 1) sl = 1 := by
  have h1 := con hL (by omega : tr.height T_SORT - 1 < _)
    (e := .mul .isLast (.mul (c act) (Dsl.not (c sl)))) (by simp [Sort.constraints])
  simp only [eval_mul, eval_c, eval_not, eval_isLast,
    if_pos (show tr.height T_SORT - 1 + 1 = tr.height T_SORT by omega)] at h1
  rw [ha] at h1; grind

theorem segFields {r : Nat} (hr : r < tr.height T_SORT) :
    (tr.cell T_SORT r sf = 1 → tr.cell T_SORT r i = 0 ∧ tr.cell T_SORT r cin = 1) ∧
    (tr.cell T_SORT r sl = 1 → tr.cell T_SORT r i = 31 ∧ tr.cell T_SORT r cout = 0) := by
  have h1 := con hL hr (e := .mul (c sf) (c i)) (by simp [Sort.constraints])
  have h2 := con hL hr (e := .mul (c sl) (sub (c i) (k 31))) (by simp [Sort.constraints])
  have h3 := con hL hr (e := .mul (c sf) (Dsl.not (c cin))) (by simp [Sort.constraints])
  have h4 := con hL hr (e := .mul (c sl) (c cout)) (by simp [Sort.constraints])
  simp only [eval_mul, eval_c, eval_not, eval_sub, eval_k] at h1 h2 h3 h4
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h] at h1 h3; constructor <;> grind
  · rw [h] at h2 h4; constructor <;> grind

theorem delay {r : Nat} (hr : r + 1 < tr.height T_SORT) (ha : tr.cell T_SORT r act = 1) :
    tr.cell T_SORT (r + 1) (d 0) = tr.cell T_SORT r bb ∧
    ∀ j, j < 31 → tr.cell T_SORT (r + 1) (d (j + 1)) = tr.cell T_SORT r (d j) := by
  have h1 := con hL (by omega : r < _) (e := .mul (c act) (sub (n (d 0)) (c bb)))
    (by simp [Sort.constraints])
  simp only [eval_mul, eval_c, eval_sub, eval_n, nxt hr] at h1
  rw [ha] at h1
  refine ⟨by grind, fun j hj => ?_⟩
  have h2 := con hL (by omega : r < _) (e := .mul (c act) (sub (n (d (j + 1))) (c (d j))))
    (by simp only [Sort.constraints, List.mem_append, List.mem_map, List.mem_range]
        exact Or.inr ⟨j, hj, rfl⟩)
  simp only [eval_mul, eval_c, eval_sub, eval_n, nxt hr] at h2
  rw [ha] at h2; grind

theorem chainEq {r : Nat} (hr : r < tr.height T_SORT) (ha : tr.cell T_SORT r act = 1)
    (hf : tr.cell T_SORT r ft = 0) :
    tr.cell T_SORT r bb + 256 * tr.cell T_SORT r cout =
      tr.cell T_SORT r (d 31) + diffE.eval tr T_SORT r pub + tr.cell T_SORT r cin := by
  have h1 := con hL hr (e := .mul (.mul (c act) (Dsl.not (c ft)))
      (sub (c bb) (sub (.add (c (d 31)) (.add diffE (c cin))) (smul 256 (c cout)))))
    (by simp [Sort.constraints])
  simp only [eval_mul, eval_c, eval_not, eval_sub, eval_add, eval_smul] at h1
  rw [ha, hf] at h1
  grind

end ZkFormal.Near.SortProof

namespace ZkFormal.Near.SortProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Sort

variable {tr : Trace Fp} {pub : List Fp}

def isOne (tr : Trace Fp) (x : Nat) (r : Nat) : Bool := decide (tr.cell T_SORT r x = 1)

theorem zero_of_not_one (hL : TableLocal Sort.table tr T_SORT pub) {r : Nat} (hr : r < tr.height T_SORT)
    {x : Nat} (hx : x ∈ [act, sf, sl, ft, cin, cout] ++ (List.range 8).map dbit)
    (h : isOne tr x r = false) : tr.cell T_SORT r x = 0 := by
  rcases isBool hL hr hx with h' | h'
  · exact h'
  · simp [isOne, h'] at h

theorem segFacts (hL : TableLocal Sort.table tr T_SORT pub) :
    SegFacts (tr.height T_SORT) (isOne tr act) (isOne tr sf) (isOne tr sl) where
  first_act r hr h := by simp only [isOne, decide_eq_true_eq] at h ⊢; exact first_act hL hr h
  last_act r hr h := by simp only [isOne, decide_eq_true_eq] at h ⊢; exact last_act hL hr h
  cont r hr ha hl := by
    simp only [isOne, decide_eq_true_eq] at ha
    have hl' := zero_of_not_one hL (by omega) (by simp) hl
    have := cont hL hr ha hl'
    simp [isOne, this.1, this.2]
  next r hr hl ha := by
    simp only [isOne, decide_eq_true_eq] at hl ha ⊢
    exact (nextSeg hL hr hl ha).1
  pad r hr ha := by
    have := pad hL hr (zero_of_not_one hL (by omega) (by simp) ha)
    simp [isOne, this]
  start h0 := by simp [isOne, (row0 hL h0).1]
  stop h0 ha := by
    simp only [isOne, decide_eq_true_eq] at ha ⊢; exact lastRow hL h0 ha

/-- Inside a segment `(s, ℓ)`, a column with `x(r+1) = x(r) + δ` per row. -/
theorem seg_step {s ℓ : Nat} (hseg : IsSeg (isOne tr act) (isOne tr sf) (isOne tr sl) s ℓ)
    (hL : TableLocal Sort.table tr T_SORT pub) (hH : s + ℓ ≤ tr.height T_SORT) {r : Nat}
    (h1 : s ≤ r) (h2 : r + 1 < s + ℓ) :
    tr.cell T_SORT r act = 1 ∧ tr.cell T_SORT r sl = 0 := by
  obtain ⟨_, _, _, hact, _, hlast⟩ := hseg
  have ha := hact r h1 (by omega)
  have hl := hlast r h1 h2
  simp only [isOne, decide_eq_true_eq] at ha
  exact ⟨ha, zero_of_not_one hL (by omega) (by simp) hl⟩

end ZkFormal.Near.SortProof

namespace ZkFormal.Near.SortProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Sort

variable {tr : Trace Fp} {pub : List Fp}

theorem height_le (hL : TableLocal Sort.table tr T_SORT pub) : tr.height T_SORT ≤ 2 ^ 13 := by
  have := hL.log_le
  unfold Trace.height
  exact Nat.pow_le_pow_right (by omega) this

theorem height_pos (hL : TableLocal Sort.table tr T_SORT pub) : 0 < tr.height T_SORT := by
  unfold Trace.height; exact Nat.two_pow_pos _

/-- A segment is 32 rows with `i = 0 … 31` and constant `rr`, `ft`. -/
theorem seg32 (hL : TableLocal Sort.table tr T_SORT pub) {s ℓ : Nat}
    (hseg : IsSeg (isOne tr act) (isOne tr sf) (isOne tr sl) s ℓ) (hH : s + ℓ ≤ tr.height T_SORT) :
    ℓ = 32 ∧ ∀ j, j < ℓ → tr.cell T_SORT (s + j) i = ((j : Nat) : Fp) ∧
      tr.cell T_SORT (s + j) rr = tr.cell T_SORT s rr ∧ tr.cell T_SORT (s + j) ft = tr.cell T_SORT s ft := by
  have hP : tr.height T_SORT < P := by have := height_le hL; unfold P; omega
  have hpos := hseg.1
  have hsf : tr.cell T_SORT s sf = 1 := by have := hseg.2.1; simpa [isOne] using this
  have hsl : tr.cell T_SORT (s + ℓ - 1) sl = 1 := by have := hseg.2.2.1; simpa [isOne] using this
  have hw : ∀ r, s ≤ r → r + 1 < s + ℓ → _ := fun r h1 h2 =>
    within hL (by omega) (seg_step hseg hL hH h1 h2).1 (seg_step hseg hL hH h1 h2).2
  have hi := counter_of (f := fun r => tr.cell T_SORT r i) (s := s) (ℓ := ℓ) (v0 := 0)
    ((segFields hL (by omega : s < _)).1 hsf).1 (fun r h1 h2 => (hw r h1 h2).2.2.1)
  have hrr := const_of (f := fun r => tr.cell T_SORT r rr) (s := s) (ℓ := ℓ) (fun r h1 h2 => (hw r h1 h2).1)
  have hft := const_of (f := fun r => tr.cell T_SORT r ft) (s := s) (ℓ := ℓ) (fun r h1 h2 => (hw r h1 h2).2.1)
  have hend := ((segFields hL (by omega : s + ℓ - 1 < _)).2 hsl).1
  have h31 : ℓ - 1 = 31 := by
    have e := hi (s + ℓ - 1) (by omega) (by omega)
    rw [hend, show 0 + (s + ℓ - 1 - s) = ℓ - 1 by omega] at e
    have hb : (31 : Nat) < P := by unfold P; omega
    have ha : ℓ - 1 < P := by omega
    exact (ofNat_inj (a := 31) (b := ℓ - 1) hb ha e).symm
  refine ⟨by omega, fun j hj => ⟨?_, hrr (s + j) (by omega) (by omega), hft (s + j) (by omega) (by omega)⟩⟩
  have := hi (s + j) (by omega) (by omega)
  simpa [show 0 + (s + j - s) = j by omega] using this

end ZkFormal.Near.SortProof

namespace ZkFormal.Near.SortProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Sort

variable {tr : Trace Fp} {pub : List Fp}

theorem multNat1 (x : Nat) (r : Nat) :
    Interaction.multNat.go tr T_SORT r pub [c x] 0 = if tr.cell T_SORT r x = 1 then 1 else 0 := by
  simp only [Interaction.multNat.go, eval_c]
  by_cases h : tr.cell T_SORT r x = 1 <;> simp [h]

theorem rowT (r : Nat) (b : Nat) (s : Bool) :
    rowTraffic Sort.interactions tr T_SORT r pub b s =
      if b = B_RIDS ∧ s = false ∧ tr.cell T_SORT r act = 1 then
        [[tr.cell T_SORT r rr, tr.cell T_SORT r i, tr.cell T_SORT r bb]] else [] := by
  simp only [rowTraffic, Sort.interactions, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    Dsl.recv, Interaction.multNat, multNat1, Interaction.msgVal, List.map_cons, List.map_nil, eval_c]
  by_cases h1 : B_RIDS = b <;> by_cases h2 : s = false <;> by_cases h3 : tr.cell T_SORT r act = 1 <;>
    simp_all [eq_comm]

/-- The view: one id per segment. -/
def idsOf (tr : Trace Fp) (segs : List (Nat × Nat)) : List (Nat × List Nat) :=
  segs.map fun p => ((tr.cell T_SORT p.1 rr).toNat,
    (List.range 32).map fun j => (tr.cell T_SORT (p.1 + j) bb).toNat)

end ZkFormal.Near.SortProof

namespace ZkFormal.Near
/-- `flatMap` over `range' s ℓ` of functions that are singletons there. -/
theorem flatMap_range'_single {α : Type} (f : Nat → List α) (g : Nat → α) (s ℓ : Nat)
    (h : ∀ j, j < ℓ → f (s + j) = [g j]) :
    (List.range' s ℓ).flatMap f = (List.range ℓ).map g := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih =>
    rw [range'_succ', List.flatMap_append, ih (fun j hj => h j (by omega)),
      List.range_succ, List.map_append]
    simp [h ℓ (by omega)]

theorem flatMap_range'_nil {α : Type} (f : Nat → List α) (s ℓ : Nat)
    (h : ∀ j, j < ℓ → f (s + j) = []) : (List.range' s ℓ).flatMap f = [] := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih =>
    rw [range'_succ', List.flatMap_append, ih (fun j hj => h j (by omega))]
    simp [h ℓ (by omega)]

theorem flatMap_segs {α : Type} (segs : List (Nat × Nat)) (F G : Nat × Nat → List α)
    (h : ∀ p ∈ segs, F p = G p) : segs.flatMap F = segs.flatMap G := by
  induction segs with
  | nil => rfl
  | cons p rest ih =>
    simp only [List.flatMap_cons]
    rw [h p (by simp), ih (fun q hq => h q (by simp [hq]))]
end ZkFormal.Near

namespace ZkFormal.Near.SortProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Sort

variable {tr : Trace Fp} {pub : List Fp}

theorem traffic (hL : TableLocal Sort.table tr T_SORT pub) (segs : List (Nat × Nat))
    (hc : Consec 0 segs) (hend : segEnd 0 segs ≤ tr.height T_SORT)
    (hall : ∀ p ∈ segs, IsSeg (isOne tr act) (isOne tr sf) (isOne tr sl) p.1 p.2)
    (hpad : ∀ r, segEnd 0 segs ≤ r → r < tr.height T_SORT → isOne tr act r = false) :
    TableTraffic Sort.interactions tr T_SORT pub (sortTraffic (idsOf tr segs)) := by
  intro b m
  rw [tableBusCount_eq, tableBusCount_eq]
  -- rows split as segments ++ padding
  have hsplit : ∀ (sd : Bool), (List.range (tr.height T_SORT)).flatMap
      (fun r => rowTraffic Sort.interactions tr T_SORT r pub b sd) =
      segs.flatMap (fun p => (List.range' p.1 p.2).flatMap
        (fun r => rowTraffic Sort.interactions tr T_SORT r pub b sd)) := by
    intro sd
    have hA := segEnd_ge segs 0 hc
    have e1 : List.range (tr.height T_SORT) =
        List.range' 0 (segEnd 0 segs - 0) ++ List.range' (segEnd 0 segs) (tr.height T_SORT - segEnd 0 segs) := by
      rw [List.range_eq_range', Nat.sub_zero]; exact range'_split _ _ hend
    rw [e1, List.flatMap_append, range'_segs segs 0 hc, List.flatMap_assoc,
      flatMap_range'_nil _ _ _ (fun j hj => by
        rw [rowT]
        have := hpad (segEnd 0 segs + j) (by omega) (by omega)
        simp only [isOne, decide_eq_false_iff_not] at this
        simp [this]), List.append_nil]
  -- a segment's messages
  have hseg : ∀ p ∈ segs, ∀ (sd : Bool), (List.range' p.1 p.2).flatMap
      (fun r => rowTraffic Sort.interactions tr T_SORT r pub b sd) =
      if b = B_RIDS ∧ sd = false then (List.range 32).map
        (fun j => [tr.cell T_SORT p.1 rr, ((j : Nat) : Fp), tr.cell T_SORT (p.1 + j) bb]) else [] := by
    intro p hp sd
    have hH : p.1 + p.2 ≤ tr.height T_SORT := by have := seg_le_end segs 0 hc p hp; omega
    obtain ⟨h32, hcol⟩ := seg32 hL (hall p hp) hH
    have hact : ∀ j, j < p.2 → tr.cell T_SORT (p.1 + j) act = 1 := fun j hj => by
      have := (hall p hp).2.2.2.1 (p.1 + j) (by omega) (by omega); simpa [isOne] using this
    split
    · rename_i hb
      rw [← h32]
      apply flatMap_range'_single
      intro j hj
      rw [rowT, if_pos ⟨hb.1, hb.2, hact j hj⟩, (hcol j hj).1, (hcol j hj).2.1]
    · rename_i hb
      apply flatMap_range'_nil
      intro j hj
      rw [rowT, if_neg (fun h => hb ⟨h.1, h.2.1⟩)]
  constructor
  · rw [hsplit, flatMap_segs segs _ _ (fun p hp => (hseg p hp true))]
    simp [sortTraffic, flatMap_nil_fun]
  · rw [hsplit, flatMap_segs segs _ _ (fun p hp => (hseg p hp false))]
    simp only [sortTraffic, idsOf]
    by_cases hb : b = B_RIDS
    · simp only [hb, if_true, and_self, true_and, List.flatMap_map, List.map_flatMap, List.map_map]
      congr 1
      apply flatMap_segs
      intro p hp
      simp [Function.comp, Msg.toFp, Fp.ofNat_toNat]
      intro a ha
      refine ⟨rfl, ?_⟩
      rw [List.getElem?_range ha]
      simp [Fp.ofNat_toNat]
    · simp [hb, flatMap_nil_fun]

end ZkFormal.Near.SortProof

namespace ZkFormal.Near.SortProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Sort

variable {tr : Trace Fp} {pub : List Fp}

theorem delayK (hL : TableLocal Sort.table tr T_SORT pub) :
    ∀ k, k < 32 → ∀ r, k + 1 ≤ r → r < tr.height T_SORT →
      (∀ q, r - 1 - k ≤ q → q < r → tr.cell T_SORT q act = 1) →
      tr.cell T_SORT r (d k) = tr.cell T_SORT (r - 1 - k) bb := by
  intro k
  induction k with
  | zero =>
    intro _ r h1 h2 ha
    have := (delay hL (r := r - 1) (by omega) (ha (r - 1) (by omega) (by omega))).1
    rwa [show r - 1 + 1 = r by omega] at this
  | succ k ih =>
    intro hk r h1 h2 ha
    have := (delay hL (r := r - 1) (by omega) (ha (r - 1) (by omega) (by omega))).2 k (by omega)
    rw [show r - 1 + 1 = r by omega] at this
    rw [this, ih (by omega) (r - 1) (by omega) (by omega) (fun q hq1 hq2 => ha q (by omega) (by omega))]
    congr 1; omega

theorem dbit_bool (hL : TableLocal Sort.table tr T_SORT pub) {r : Nat} (hr : r < tr.height T_SORT) :
    ∀ b, b < 8 → tr.cell T_SORT r (dbit (0 + b)) = 0 ∨ tr.cell T_SORT r (dbit (0 + b)) = 1 :=
  fun b hb => isBool hL hr
    (List.mem_append_right _ (List.mem_map.mpr ⟨b, List.mem_range.mpr hb, by simp⟩))

/-- Consecutive segments carry consecutive increasing ids. -/
theorem incr (hL : TableLocal Sort.table tr T_SORT pub) (segs : List (Nat × Nat))
    (hc : Consec 0 segs) (hend : segEnd 0 segs ≤ tr.height T_SORT)
    (hall : ∀ p ∈ segs, IsSeg (isOne tr act) (isOne tr sf) (isOne tr sl) p.1 p.2) :
    SortWf (idsOf tr segs) := by
  have hP : tr.height T_SORT < P := by have := height_le hL; unfold P; omega
  have hlen : ∀ p ∈ segs, p.2 = 32 := fun p hp =>
    (seg32 hL (hall p hp) (by have := seg_le_end segs 0 hc p hp; omega)).1
  refine ⟨fun x hx => ?_, fun t ht hbytes => ?_⟩
  · simp only [idsOf, List.mem_map] at hx
    obtain ⟨p, -, rfl⟩ := hx
    exact ⟨by simp, Fp.toNat_lt _⟩
  · simp only [idsOf, List.length_map] at ht
    have hp0 : segs[t] ∈ segs := List.getElem_mem (by omega)
    have hp1 : segs[t + 1] ∈ segs := List.getElem_mem ht
    have hs1 := consec_get segs 0 hc t ht
    rw [hlen _ hp0] at hs1
    have hb0 := seg_le_end segs 0 hc _ hp1
    rw [hs1, hlen _ hp1] at hb0
    have hseg0 := hall _ hp0
    have hseg1 := hall _ hp1
    rw [hlen _ hp0] at hseg0
    rw [hs1, hlen _ hp1] at hseg1
    obtain ⟨-, hcol1⟩ := seg32 hL (hall _ hp1) (by rw [hlen _ hp1]; omega)
    rw [hlen _ hp1, hs1] at hcol1
    generalize hs : segs[t].1 = s at hs1 hb0 hseg0 hseg1 hcol1
    -- all rows of the two segments are active
    have hact : ∀ q, s ≤ q → q < s + 64 → tr.cell T_SORT q act = 1 := by
      intro q h1 h2
      rcases Nat.lt_or_ge q (s + 32) with h | h
      · have := hseg0.2.2.2.1 q h1 (by omega); simpa [isOne] using this
      · have := hseg1.2.2.2.1 q (by omega) (by omega)
        simpa [isOne] using this
    -- the second segment has ft = 0
    have hsl0 : tr.cell T_SORT (s + 31) sl = 1 := by
      have := hseg0.2.2.1; simpa [isOne] using this
    have hft : tr.cell T_SORT (s + 32) ft = 0 := (nextSeg hL (r := s + 31) (by omega) hsl0 (hact _ (by omega) (by omega))).2
    have hsf1 : tr.cell T_SORT (s + 32) sf = 1 := by
      have := hseg1.2.1; simpa [isOne] using this
    -- byte values
    let B : Nat → Nat := fun j => (tr.cell T_SORT (s + 32 + j) bb).toNat
    let D : Nat → Nat := fun j => (tr.cell T_SORT (s + j) bb).toNat
    let F : Nat → Nat := fun j => bitsVal (fun b => cv tr T_SORT (s + 32 + j) (dbit b)) 0 8
    let ci : Nat → Nat := fun j => if j < 32 then cv tr T_SORT (s + 32 + j) cin else 0
    have hB : ∀ j, j < 32 → B j < 256 := fun j hj => by
      have := hbytes _ (List.getElem_mem (by simp [idsOf]; omega : t + 1 < (idsOf tr segs).length))
      simp only [idsOf, List.getElem_map] at this
      rw [consec_get segs 0 hc t ht, hlen _ hp0, hs] at this
      exact this _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
    have hD : ∀ j, j < 32 → D j < 256 := fun j hj => by
      have := hbytes _ (List.getElem_mem (by simp [idsOf]; omega : t < (idsOf tr segs).length))
      simp only [idsOf, List.getElem_map] at this
      rw [hs] at this
      exact this _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
    have hcc : ∀ j, j < 32 → B j + 256 * ci (j + 1) = D j + F j + ci j := by
      intro j hj
      have hr : s + 32 + j < tr.height T_SORT := by omega
      have hftj : tr.cell T_SORT (s + 32 + j) ft = 0 := by rw [(hcol1 j hj).2.2]; exact hft
      have e := chainEq hL hr (hact _ (by omega) (by omega)) hftj
      have hd31 := delayK hL 31 (by omega) (s + 32 + j) (by omega) hr
        (fun q h1 h2 => hact q (by omega) (by omega))
      rw [show diffE = bits (fun j => c (dbit j)) 0 8 from rfl] at e
      rw [hd31, show s + 32 + j - 1 - 31 = s + j by omega,
        eval_bits tr T_SORT (s + 32 + j) pub dbit 0 8 (dbit_bool hL hr)] at e
      -- carry out of row j = carry in of row j + 1
      have hco : (tr.cell T_SORT (s + 32 + j) cout).toNat = ci (j + 1) := by
        by_cases hj' : j + 1 < 32
        · have hw := within hL (r := s + 32 + j) (by omega) (hact _ (by omega) (by omega))
            (by
              rcases isBool hL hr (x := sl) (by simp) with h | h
              · exact h
              · exfalso
                have := hseg1.2.2.2.2.2 (s + 32 + j) (by omega) (by omega)
                simp [isOne, h] at this)
          simp only [ci, if_pos hj', cv]
          rw [show s + 32 + (j + 1) = s + 32 + j + 1 by omega, hw.2.2.2]
        · have hj31 : j = 31 := by omega
          subst hj31
          have hsl1 : tr.cell T_SORT (s + 32 + 31) sl = 1 := by
            have := hseg1.2.2.1
            simpa [isOne, show s + 32 + 32 - 1 = s + 32 + 31 by omega] using this
          rw [((segFields hL hr).2 hsl1).2]
          simp [ci]; rfl
      have hcib : ci j ≤ 1 := by
        simp only [ci, if_pos hj]; exact cv_bool (isBool hL hr (by simp))
      have hcob : (tr.cell T_SORT (s + 32 + j) cout).toNat ≤ 1 := cv_bool (isBool hL hr (by simp))
      have hF : F j < 256 := bitsVal_lt _ _ _ (fun b hb => cv_bool (dbit_bool hL hr b hb))
      have hBj := hB j hj
      have hDj := hD j hj
      rw [← hco]
      apply ofNat_inj (by unfold P; omega) (by unfold P; omega)
      rw [natCast_add, natCast_mul, natCast_add, natCast_add]
      simp only [B, D, F, ci, if_pos hj, cv, natCast_eq, Fp.ofNat_toNat] at e ⊢
      exact e
    have hci0 : ci 0 = 1 := by
      simp only [ci, if_pos (show 0 < 32 by omega), cv, Nat.add_zero]
      rw [((segFields hL (by omega : s + 32 < _)).1 hsf1).2]; rfl
    have key := carry_chain ((List.range 32).map B) ((List.range 32).map D) ((List.range 32).map F) ci
      (by simp) (by simp) (fun j hj => by simp at hj; simpa [hj] using hcc j hj)
    rw [hci0] at key
    simp only [List.length_map, List.length_range, ci, Nat.lt_irrefl, if_false, Nat.mul_zero,
      Nat.add_zero] at key
    -- back to the view's lists
    simp only [idsOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem ht,
      List.getElem?_eq_getElem (show t < segs.length by omega), Option.map_some, Option.getD_some]
    rw [consec_get segs 0 hc t ht, hlen _ hp0, hs, le256_eq_leNat _ (fun y hy => by
          simp only [List.mem_map, List.mem_range] at hy; obtain ⟨j, hj, rfl⟩ := hy; exact hD j hj),
      le256_eq_leNat _ (fun y hy => by
          simp only [List.mem_map, List.mem_range] at hy; obtain ⟨j, hj, rfl⟩ := hy; exact hB j hj)]
    simp only [B, D] at key
    omega

end ZkFormal.Near.SortProof

namespace ZkFormal.Near

/-- **The sort table's view.** -/
theorem sort_view : SortViewStmt := by
  intro tr pub hL
  obtain ⟨segs, hc, hend, hall, hpad⟩ := segments_of (SortProof.segFacts hL) (SortProof.height_pos hL)
  exact ⟨SortProof.idsOf tr segs, SortProof.incr hL segs hc hend hall,
    SortProof.traffic hL segs hc hend hall hpad⟩

end ZkFormal.Near
