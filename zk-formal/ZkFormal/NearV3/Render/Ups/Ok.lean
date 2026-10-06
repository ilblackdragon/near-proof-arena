import ZkFormal.NearV3.Render.Ups.Local
import ZkFormal.NearV3.Extract.Ups.PlanDefs

/-!
# ZkFormal.NearV3.Render.Ups.Ok — the honest input `UpsOk` and the proof toolkit

**`UpsOk insts`**: the conditions on the instance descriptions under which the generator's
table satisfies the constraints.  `InstOk I` collects the per-instance conditions (grown
group by group); `UpsOk` adds the structural ones (`UpsShape`) and the row cap
`R + 1 ≤ 2^22` (parametric: no other bound on `L` or the number of instances).

Toolkit: indicator lemmas (`ind`), the cells of each row kind as explicit functions (`WC`, `VC`,
`QC`, all `rfl`), the zero cells of each row kind (`zW`, `zV`, `zQ`) for the vanishing check
`vz`, and the row dispatch `actRow`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Render.EvI
  ZkFormal.Near.Dsl

namespace UpsGen

/-! ## The honest input -/

/-- Per-instance conditions. -/
structure InstOk (I : UpsInst) : Prop where
  L1 : 1 ≤ L I
  nQ1 : 1 ≤ nQ I
  q1 : ∀ k, k < nQ I → 1 ≤ (part I k).q.length
  /-- the case and the terminal facts are in range -/
  ci : I.ci < 11
  D : I.D < 3
  ts : 1 ≤ I.ts ∧ I.ts ≤ 3
  ti : I.ti < 3
  x : I.x < 16
  /-- a nibble terminal (`t* ∈ {1, 2}`) vs the `END` terminal (`t* = 3`) -/
  tsEnd : I.ts = 3 → I.ci = 0 ∨ I.ci = 1 ∨ I.ci = 2 ∨ I.ci = 5 ∨ I.ci = 7 ∨ I.ci = 8
  tsNib : I.ts ≠ 3 → I.ci = 3 ∨ I.ci = 4 ∨ I.ci = 6 ∨ I.ci = 9 ∨ I.ci = 10
  /-- the value length (`SPLEN`, three bytes) -/
  Lsmall : L I < 2 ^ 24
  /-- the number of parts: the terminal parts of the plan, one per depth above `N_D` -/
  nQ : nQ I = UpsRows.nTof I.ci I.ti + I.dep.getD I.D 0

/-- **The honest input of `upsV3`.** -/
structure UpsOk (insts : List UpsInst) : Prop where
  pos : 0 < insts.length
  inst : ∀ I ∈ insts, InstOk I
  /-- the row cap (`maxLog = 22`; one padding row at least) -/
  cap : R insts + 1 ≤ 2 ^ 22

theorem UpsOk.shape {insts : List UpsInst} (ok : UpsOk insts) : UpsShape insts :=
  ⟨ok.pos, fun I h => (ok.inst I h).L1, fun I h => (ok.inst I h).nQ1, fun I h => (ok.inst I h).q1⟩

/-! ## Indicators -/

theorem ind_pos {p : Prop} [Decidable p] (h : p) : ind p = 1 := by simp [ind, h]
theorem ind_neg {p : Prop} [Decidable p] (h : ¬ p) : ind p = 0 := by simp [ind, h]
@[simp] theorem ind_True : ind True = 1 := rfl
@[simp] theorem ind_False : ind False = 0 := rfl
@[simp] theorem ind_tt : ind (true = true) = 1 := rfl
@[simp] theorem ind_ft : ind (false = true) = 0 := rfl
theorem ind01 (p : Prop) [Decidable p] : ind p = 0 ∨ ind p = 1 := by
  unfold ind; split <;> simp

/-! ## Cells by row kind -/

/-- Cells of walk row `t`. -/
abbrev WC (I : UpsInst) (t x : Nat) : Int := if isSeg x then segCell I x else wCell I t x
/-- Cells of value row `p`. -/
abbrev VC (I : UpsInst) (p x : Nat) : Int := if isSeg x then segCell I x else vCell I p x
/-- Cells of node row `p` of part `k` (source `Q`): field `st`, index `ix`, length `fl`, windows
before `wi`, `UPB` count `u`. -/
abbrev QC (I : UpsInst) (Q : UpsPartI) (k p st ix fl wi u x : Nat) : Int :=
  if isSeg x then segCell I x else if isPC x then pcCell I Q k x else qRow I Q k p st ix fl wi u x

theorem rowCell_w (insts : List UpsInst) (q i t : Nat) :
    rowCell insts q (i, .w t) = WC (inst insts i) t := rfl
theorem rowCell_v (insts : List UpsInst) (q i p : Nat) :
    rowCell insts q (i, .v p) = VC (inst insts i) p := rfl
theorem rowCell_q (insts : List UpsInst) (q i k p : Nat) :
    rowCell insts q (i, .q k p) = QC (inst insts i) (part (inst insts i) k) k p
      (fieldAt (part (inst insts i) k).shape p).1 (fieldAt (part (inst insts i) k).shape p).2.1
      (fieldAt (part (inst insts i) k).shape p).2.2.1 (fieldAt (part (inst insts i) k).shape p).2.2.2
      (uU insts q) := rfl

/-! ## Zero cells -/

/-- Nonzero cells of a walk row (besides the segment constants). -/
def nzW (x : Nat) : Bool :=
  x == 0 || x == 1 || (4 ≤ x && x ≤ 7) || (49 ≤ x && x ≤ 62) || x == 105 || (124 ≤ x && x ≤ 126) ||
    (129 ≤ x && x < 161) || (173 ≤ x && x ≤ 175)
def zW (x : Nat) : Bool := decide (x < 187) && !isSeg x && !nzW x

def nzV (x : Nat) : Bool :=
  x == 0 || x == 2 || x == 8 || x == 9 || (65 ≤ x && x ≤ 68) || x == 100 || x == 101 || x == 181 || x == 182
def zV (x : Nat) : Bool := decide (x < 187) && !isSeg x && !nzV x

def zQ (x : Nat) : Bool := [1, 2, 4, 5, 6, 7, 173, 174, 175].contains x

theorem zW_cell (I : UpsInst) (t x : Nat) (h : zW x = true) : WC I t x = 0 := by
  simp only [zW, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨-, h1⟩, h2⟩ := h
  simp only [WC, h1, Bool.false_eq_true, if_false]
  unfold wCell
  split <;> (try exact absurd h2 (by decide))
  simp only [nzW, Bool.or_eq_false_iff, Bool.and_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not] at h2
  split
  · omega
  · rfl

theorem zV_cell (I : UpsInst) (p x : Nat) (h : zV x = true) : VC I p x = 0 := by
  simp only [zV, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨-, h1⟩, h2⟩ := h
  simp only [VC, h1, Bool.false_eq_true, if_false]
  unfold vCell
  split <;> first | exact absurd h2 (by decide) | rfl

theorem zQ_cell (I : UpsInst) (Q : UpsPartI) (k p st ix fl wi u x : Nat) (h : zQ x = true) :
    QC I Q k p st ix fl wi u x = 0 := by
  simp only [zQ, List.contains_eq_mem, List.mem_cons, List.not_mem_nil, decide_eq_true_eq, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-! ## Row dispatch -/

theorem actRow {insts : List UpsInst} (hs : UpsShape insts) {q : Nat} (hq : q < R insts) :
    ∃ i, i < insts.length ∧ (recs insts).getD q default ∈ recs insts ∧
      (((∃ t, t < 4 ∧ (recs insts).getD q default = (i, .w t)) ∨
        (∃ p, p < L (inst insts i) ∧ (recs insts).getD q default = (i, .v p)) ∨
        (∃ k p, k < nQ (inst insts i) ∧ p < (part (inst insts i) k).q.length ∧
          (recs insts).getD q default = (i, .q k p)))) := by
  have hm := getD_mem hq
  have h2 := mem_recs.1 hm
  refine ⟨((recs insts).getD q default).1, h2.1, hm, ?_⟩
  rcases mem_recsI.1 h2.2 with ⟨t, ht, h⟩ | ⟨p, hp, h⟩ | ⟨k, p, hk, hp, h⟩
  · exact .inl ⟨t, ht, by rw [← h]⟩
  · exact .inr (.inl ⟨p, hp, by rw [← h]⟩)
  · exact .inr (.inr ⟨k, p, hk, hp, by rw [← h]⟩)

/-- The successor of an active row of instance `i`: the next row of the instance (`nextRK`). -/
theorem nextRow {insts : List UpsInst} (hs : UpsShape insts) {q i : Nat} {rk rk' : RK} (hq : q < R insts)
    (hr : (recs insts).getD q default = (i, rk)) (hn : nextRK (inst insts i) rk = some rk') (x : Nat) :
    nextCell insts q x = rowCell insts (q + 1) (i, rk') x := by
  have h1 : q + 1 < R insts := by
    apply Classical.byContradiction; intro h
    have := lastAt hs
    rw [show R insts - 1 = q by omega, hr] at this
    cases this
    rw [next_last (hs.L1 _ (inst_mem (by have := hs.pos; omega))) (hs.nQ1 _ (inst_mem (by have := hs.pos; omega)))
      (hs.q1 _ (inst_mem (by have := hs.pos; omega)))] at hn
    cases hn
  have ha := adjAt hs h1
  rw [hr] at ha
  rcases ha with ⟨h, h'⟩ | ⟨h, -⟩
  · simp only at h h'
    rw [hn] at h
    have e := Option.some.inj h
    simp only [nextCell, h1, if_true]
    have e2 : (recs insts).getD (q + 1) default = (i, rk') := by
      revert e h'
      generalize (recs insts).getD (q + 1) default = b
      obtain ⟨b1, b2⟩ := b
      intro e h'; simp only at e h'; rw [e, h']
    rw [e2]
  · simp only at h; rw [hn] at h; cases h

/-- After the last row of an instance: the next instance's `W0`, or the zero row. -/
theorem nextLast {insts : List UpsInst} (hs : UpsShape insts) {q i : Nat} {rk : RK} (hq : q < R insts)
    (hr : (recs insts).getD q default = (i, rk)) (hn : nextRK (inst insts i) rk = none) (x : Nat) :
    nextCell insts q x = 0 ∨ (i + 1 < insts.length ∧ nextCell insts q x = rowCell insts (q + 1) (i + 1, .w 0) x) := by
  by_cases h1 : q + 1 < R insts
  · right
    have ha := adjAt hs h1
    rw [hr] at ha
    rcases ha with ⟨h, -⟩ | ⟨-, h'⟩
    · simp only at h; rw [hn] at h; cases h
    · have hm := mem_recs.1 (getD_mem h1)
      rw [h'] at hm
      refine ⟨hm.1, ?_⟩
      simp only [nextCell, h1, if_true, h']
  · left; simp [nextCell, h1]

end UpsGen

end ZkFormal.NearV3.Render
