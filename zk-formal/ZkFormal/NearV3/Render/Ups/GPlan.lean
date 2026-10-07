import ZkFormal.NearV3.Render.Ups.GBool
import ZkFormal.NearV3.Render.Ups.PlanInput

/-!
# ZkFormal.NearV3.Render.Ups.GPlan — `cPlan` on the honest table

The part plan and part headers hold on the first row of each part (`pf`): the value part
(`j = 0`) by the walk facts (`D < 3`), a node part by `PartOk` (kinds by `termPlan`, depth,
descend counter, source level, node type and hex-prefix facts, `MEMD` child); the derived
`memory_usage` selectors (`useA`, `bN`, …, `Kc`) and copy flags are the generator's formulas.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Render.EvI
  ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

namespace UpsGen

/-! ## The plan constraints by `decide` -/

theorem evC_congr {C D C' D' P : Nat → Int} {fst lst trn : Int} :
    ∀ e : Expr, (∀ x ∈ e.colsC, C x = C' x) → (∀ x ∈ e.colsN, D x = D' x) →
      ev C D fst lst trn P e = ev C' D' fst lst trn P e
  | .const _, _, _ => rfl
  | .col x nx, hc, hn => by
    cases nx
    · exact hc x (by simp [Expr.colsC])
    · exact hn x (by simp [Expr.colsN])
  | .pub _, _, _ => rfl
  | .isFirst, _, _ => rfl
  | .isLast, _, _ => rfl
  | .isTransition, _, _ => rfl
  | .add a b, hc, hn => by
    simp only [Expr.colsC, Expr.colsN, List.mem_append] at hc hn
    simp only [ev]
    rw [evC_congr a (fun x h => hc x (Or.inl h)) (fun x h => hn x (Or.inl h)),
      evC_congr b (fun x h => hc x (Or.inr h)) (fun x h => hn x (Or.inr h))]
  | .mul a b, hc, hn => by
    simp only [Expr.colsC, Expr.colsN, List.mem_append] at hc hn
    simp only [ev]
    rw [evC_congr a (fun x h => hc x (Or.inl h)) (fun x h => hn x (Or.inl h)),
      evC_congr b (fun x h => hc x (Or.inr h)) (fun x h => hn x (Or.inr h))]
  | .neg a, hc, hn => by
    simp only [Expr.colsC, Expr.colsN] at hc hn
    simp only [ev]
    rw [evC_congr a hc hn]

/-- A part's first row with the plan indices fixed, over `ℤ`. -/
def planRowI (ci ti jj ki uu : Nat) (x : Nat) : Int := (UpsRows.planRow ci ti jj ki uu x : Nat)

def upOf (ki : Nat) : Nat := if ki = 0 ∨ ki = 1 ∨ ki = 11 then 1 else 0

/-- `kindCode` and the terminal / upper flag agree with the plan, for every index combination
(position `k < 5`, `4` standing for `k ≥ 4`) whose kind is the planned one. -/
def planCheckI : Bool :=
  (List.range 11).all fun ci => (List.range 3).all fun ti => (List.range 5).all fun k =>
    (List.range 12).all fun ki =>
      !((decide (k < UpsRows.nTof ci ti) → ki = ((UpsRows.termPlan (UpsRows.UCase.all.getD ci .LP) ti).getD k .RLP).ix) ∧
        (decide (UpsRows.nTof ci ti ≤ k) → ki = 0 ∨ ki = 1 ∨ ki = 11)) ||
      (ev (planRowI ci ti (if k < 4 then k + 1 else 0) ki (upOf ki)) (fun _ => 0) 0 0 0 (fun _ => 0) UpsRows.eKC == 0 &&
       ev (planRowI ci ti (if k < 4 then k + 1 else 0) ki (upOf ki)) (fun _ => 0) 0 0 0 (fun _ => 0) UpsRows.eUT == 0)

theorem planCheckI_ok : planCheckI = true := by decide +kernel

def nTCheckI : Bool :=
  (List.range 11).all fun ci => (List.range 3).all fun ti =>
    ev (planRowI ci ti 0 0 0) (fun _ => 0) 0 0 0 (fun _ => 0) nTE == (UpsRows.nTof ci ti : Int)

theorem nTCheckI_ok : nTCheckI = true := by decide +kernel

/-- No selectors / public inputs. -/
def noSel : Expr → Bool
  | .const _ => true
  | .col _ _ => true
  | .add a b => noSel a && noSel b
  | .mul a b => noSel a && noSel b
  | .neg a => noSel a
  | _ => false

theorem evS_congr {C D P P' : Nat → Int} {f l t f' l' t' : Int} :
    ∀ e : Expr, noSel e = true → ev C D f l t P e = ev C D f' l' t' P' e
  | .const _, _ => rfl
  | .col _ _, _ => rfl
  | .add a b, h => by
    simp only [noSel, Bool.and_eq_true] at h; simp only [ev]; rw [evS_congr a h.1, evS_congr b h.2]
  | .mul a b, h => by
    simp only [noSel, Bool.and_eq_true] at h; simp only [ev]; rw [evS_congr a h.1, evS_congr b h.2]
  | .neg a, h => by simp only [noSel] at h; simp only [ev]; rw [evS_congr a h]
  | .pub _, h => by simp [noSel] at h
  | .isFirst, h => by simp [noSel] at h
  | .isLast, h => by simp [noSel] at h
  | .isTransition, h => by simp [noSel] at h

theorem planCols_lst : UpsRows.planCols = [8, 3, 180, 179, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 34, 35, 36,
    50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64] := by decide

/-- A node part's first row agrees with the plan row of its indices. -/
theorem plan_agree (I : UpsInst) (Q : UpsPartI) (k st ix fl wi u : Nat) :
    ∀ x ∈ UpsRows.planCols, QC I Q k 0 st ix fl wi u x =
      planRowI I.ci I.ti (if k < 4 then k + 1 else 0) Q.kind (upOf Q.kind) x := by
  intro x hx
  rw [planCols_lst] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    cellsimp <;> simp only [planRowI, UpsRows.planRow, upOf, upV, kin, ind, pf, qb, UpsV3.up, kPT, List.map,
      List.sum_cons, List.sum_nil, Nat.reduceEqDiff, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceSub, ite_true, ite_false,
      true_or, or_true, false_or, or_false, and_true, true_and, and_false, false_and, and_self] <;>
    (repeat' split) <;> omega

theorem planCols_lt : ∀ x ∈ UpsRows.planCols, x < 187 := by decide
theorem eKC_noSel : noSel UpsRows.eKC = true := by decide
theorem eUT_noSel : noSel UpsRows.eUT = true := by decide
theorem nTE_noSel : noSel nTE = true := by decide

/-- The plan facts at the representative position `min k 4`. -/
theorem plan_at {I : UpsInst} (iok : InstOk I) {k : Nat} (pk : PartOk I k (part I k)) :
    ev (planRowI I.ci I.ti (if k < 4 then k + 1 else 0) (part I k).kind (upOf (part I k).kind)) (fun _ => 0) 0 0 0
        (fun _ => 0) UpsRows.eKC = 0 ∧
    ev (planRowI I.ci I.ti (if k < 4 then k + 1 else 0) (part I k).kind (upOf (part I k).kind)) (fun _ => 0) 0 0 0
        (fun _ => 0) UpsRows.eUT = 0 := by
  have h := planCheckI_ok
  simp only [planCheckI, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    Bool.and_eq_true, beq_iff_eq] at h
  have hnt := UpsRows.nTof_le I.ci iok.ci I.ti iok.ti
  by_cases hk4 : k < 4
  · have := h I.ci iok.ci I.ti iok.ti k (by omega) (part I k).kind pk.kind
    simp only [hk4, ite_true] at this ⊢
    rcases this with h1 | h1
    · exact absurd ⟨fun h => pk.kindT (by simpa using h), fun h => pk.kindU (by simpa using h)⟩ h1
    · exact h1
  · have := h I.ci iok.ci I.ti iok.ti 4 (by omega) (part I k).kind pk.kind
    simp only [hk4, ite_false, show ¬ (4 < 4) by omega] at this ⊢
    rcases this with h1 | h1
    · exact absurd ⟨fun h => absurd (by simpa using h) (show ¬ 4 < UpsRows.nTof I.ci I.ti by omega),
        fun _ => pk.kindU (by omega)⟩ h1
    · exact h1

section
variable {C D P : Nat → Int} {fst lst trn : Int}

theorem plan_cells {I : UpsInst} {k st ix fl wi u : Nat}
    (hC : ∀ x, x < 187 → C x = QC I (part I k) k 0 st ix fl wi u x) {e : Expr}
    (hs : noSel e = true) (hc : (∀ x ∈ e.colsC, x ∈ UpsRows.planCols) ∧ e.colsN = []) :
    ev C D fst lst trn P e = ev (planRowI I.ci I.ti (if k < 4 then k + 1 else 0) (part I k).kind
      (upOf (part I k).kind)) (fun _ => 0) 0 0 0 (fun _ => 0) e := by
  rw [evS_congr (f' := 0) (l' := 0) (t' := 0) (P' := fun _ => 0) e hs]
  apply evC_congr e
  · intro x hx
    have hm := hc.1 x hx
    rw [hC x (planCols_lt x hm), plan_agree I (part I k) k st ix fl wi u x hm]
  · intro x hx; rw [hc.2] at hx; simp at hx

theorem plan_kc {I : UpsInst} (iok : InstOk I) {k st ix fl wi u : Nat} (pk : PartOk I k (part I k))
    (hC : ∀ x, x < 187 → C x = QC I (part I k) k 0 st ix fl wi u x) :
    ((ev C D fst lst trn P UpsRows.eKC : Int) : Fp) = 0 := by
  apply cast0; rw [plan_cells hC eKC_noSel UpsRows.eKC_cols]; exact (plan_at iok pk).1

theorem plan_ut {I : UpsInst} (iok : InstOk I) {k st ix fl wi u : Nat} (pk : PartOk I k (part I k))
    (hC : ∀ x, x < 187 → C x = QC I (part I k) k 0 st ix fl wi u x) :
    ((ev C D fst lst trn P UpsRows.eUT : Int) : Fp) = 0 := by
  apply cast0; rw [plan_cells hC eUT_noSel UpsRows.eUT_cols]; exact (plan_at iok pk).2

theorem plan_nT {I : UpsInst} (iok : InstOk I) {k st ix fl wi u : Nat}
    (hC : ∀ x, x < 187 → C x = QC I (part I k) k 0 st ix fl wi u x) :
    ev C D fst lst trn P nTE = (UpsRows.nTof I.ci I.ti : Int) := by
  rw [plan_cells hC nTE_noSel UpsRows.nTE_cols]
  have h := nTCheckI_ok
  simp only [nTCheckI, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  rw [← h I.ci iok.ci I.ti iok.ti]
  apply evC_congr nTE _ (by intro x hx; simp [UpsRows.nTE_cols.2] at hx)
  intro x hx
  have := UpsRows.nTE_sub x hx
  simp only [planRowI, UpsRows.planRow]
  have h1 : ¬ (x = pf ∨ x = qb) := by simp only [pf, qb]; omega
  rw [if_neg h1, if_neg h1]
  rcases this with h | h
  · rw [if_pos h, if_pos h]
  · have h2 : ¬ (17 ≤ x ∧ x < 28) := by omega
    simp only [h2, h, ite_false, ite_true, and_self]

set_option hygiene false in
macro "plan_mem" : tactic => `(tactic| (simp only [UpsV3.cPlan, UpsV3.kinds, List.map, List.range_succ,
    List.range_zero, List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hex <;>
  rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl))

theorem termPlan_notUp : ∀ ci, ci < 11 → ∀ ti, ti < 3 → ∀ k, k < UpsRows.nTof ci ti →
    ((UpsRows.termPlan (UpsRows.UCase.all.getD ci .LP) ti).getD k .RLP).ix ≠ 0 ∧
    ((UpsRows.termPlan (UpsRows.UCase.all.getD ci .LP) ti).getD k .RLP).ix ≠ 1 ∧
    ((UpsRows.termPlan (UpsRows.UCase.all.getD ci .LP) ti).getD k .RLP).ix ≠ 11 := by decide

/-- A terminal part is not an upper kind. -/
theorem termNotUp {I : UpsInst} (iok : InstOk I) {k : Nat} (pk : PartOk I k (part I k)) :
    k < UpsRows.nTof I.ci I.ti → (part I k).kind ≠ 0 ∧ (part I k).kind ≠ 1 ∧ (part I k).kind ≠ 11 := by
  intro h; rw [pk.kindT h]; exact termPlan_notUp _ iok.ci _ iok.ti _ h

theorem getD3 (l : List Nat) (d : Nat) : (d = 0 → l.getD d 0 = l.getD 0 0) ∧ (d = 1 → l.getD d 0 = l.getD 1 0) ∧
    (d = 2 → l.getD d 0 = l.getD 2 0) :=
  ⟨fun h => by rw [h], fun h => by rw [h], fun h => by rw [h]⟩

set_option hygiene false in
/-- Split on the part kind, specialise the fact `fh`, close by `omega` after splitting the indicators. -/
macro "pkind" : tactic => `(tactic| (rcases (show (part I k).kind = 0 ∨ (part I k).kind = 1 ∨ (part I k).kind = 2 ∨
    (part I k).kind = 3 ∨ (part I k).kind = 4 ∨ (part I k).kind = 5 ∨ (part I k).kind = 6 ∨ (part I k).kind = 7 ∨
    (part I k).kind = 8 ∨ (part I k).kind = 9 ∨ (part I k).kind = 10 ∨ (part I k).kind = 11 by omega)
  with e | e | e | e | e | e | e | e | e | e | e | e <;>
  (try simp only [e, Nat.reduceEqDiff, ind_True, ind_False, true_or, or_true, false_or, or_false, true_implies,
    false_implies, Nat.reduceLeDiff, ne_eq, not_false_eq_true, not_true_eq_false, true_and, and_true, false_and,
    and_false, Int.zero_mul, Int.mul_zero, Int.one_mul, Int.mul_one, Int.add_zero, Int.zero_add, beq_self_eq_true,
    Nat.reduceBEq, Bool.false_and, Bool.true_and, Bool.and_true, Bool.and_false, Bool.false_eq_true,
    Bool.true_eq_false, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, imp_false,
    iff_iff_implies_and_implies, Decidable.imp_iff_not_or] at fh ⊢) <;>
  (try simp only [ind]) <;> (repeat' split) <;> first | omega | (simp_all [ind] <;> omega)))

set_option hygiene false in
/-- A node-row plan constraint with the part fact `f`. -/
macro "pq" f:term : tactic => `(tactic| (
  have fh := $f
  ups_ev [hC]
  cellsimp
  apply cast0
  try simp only [ind_True, Int.one_mul, upV, kin, cin, nokeyV, useAV, bNV, bLV, cOV, cSV, CcV, eLV, eSV, KcV,
    vcpV, xcpV, ba0V, ba1V, spY1V, spY2V, spRecv, XcpB, Spy1B, Spy2B, List.map, List.sum_cons, List.sum_nil]
  first | rfl | omega | pkind))

theorem plan_q0 {I : UpsInst} (iok : InstOk I) {k : Nat} (pk : PartOk I k (part I k)) {st ix fl wi u : Nat}
    (hC : ∀ x, x < 187 → C x = QC I (part I k) k 0 st ix fl wi u x) :
    ∀ ex ∈ UpsV3.cPlan, ((ev C D fst lst trn P ex : Int) : Fp) = 0 := by
  intro ex hex
  have hci := iok.ci; have hti := iok.ti; have hts := iok.ts; have hD := iok.D
  have hk := pk.kind; have hsd := pk.sd; have hty := pk.ty
  plan_mem
  -- the value-row block (`vb = 0`)
  iterate 16 (ups_ev [hC]; (try cellsimp); exact cast0 rfl)
  · pq True
  · exact plan_kc iok pk hC
  · exact plan_ut iok pk hC
  · pq True
  · simp only [ev, Dsl.sub, Dsl.c, Dsl.k]; rw [plan_nT iok hC]
    pq (And.intro (termNotUp iok pk) (And.intro pk.kindU (And.intro pk.pdepT (And.intro pk.pdepU (getD3 I.dep I.D)))))
  · pq (And.intro (termNotUp iok pk) (And.intro pk.kindU pk.rcT))
  · pq True
  · pq (And.intro pk.sdRD pk.sdT)
  · pq (And.intro pk.sN (getD3 I.N (part I k).sd))
  · pq (And.intro pk.pdepS (getD3 I.dep (part I k).sd))
  · pq True
  · pq pk.tyBr
  · pq pk.tyBV
  · pq pk.tyExt
  · pq (And.intro pk.tyExt pk.pt)
  · pq pk.pt
  · pq pk.tyLeaf
  · pq pk.tySpb
  · pq pk.spbKids
  · pq pk.tyBr
  · pq True
  · pq pk.nlf
  · pq pk.nlf
  · pq pk.wex
  · pq pk.wex
  · pq pk.mv
  · pq pk.mveOdd
  · pq pk.xcp
  · pq pk.jmD
  · pq pk.jmS
  all_goals pq True


/-- Walk rows have neither a value flag nor a part-first flag. -/
theorem plan_w {I : UpsInst} {t : Nat}
    (hC : ∀ x, x < 187 → C x = WC I t x) :
    ∀ ex ∈ UpsV3.cPlan, ((ev C D fst lst trn P ex : Int) : Fp) = 0 := by
  intro ex hex
  exact vzC (zc := zW) (fun x hx => by
    rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx)
    (List.all_eq_true.1 (by decide : UpsV3.cPlan.all (vz zW (fun _ => false) false false false) = true) ex hex)

/-- Non-first node rows have neither a value flag nor a part-first flag. -/
theorem plan_qn {I : UpsInst} {Q : UpsPartI} {k p st ix fl wi u : Nat} (hp : p ≠ 0)
    (hC : ∀ x, x < 187 → C x = QC I Q k p st ix fl wi u x) :
    ∀ ex ∈ UpsV3.cPlan, ((ev C D fst lst trn P ex : Int) : Fp) = 0 := by
  intro ex hex
  refine vzC (zc := fun x => zQ x || x == 8) (fun x hx => ?_)
    (List.all_eq_true.1 (by decide : UpsV3.cPlan.all
      (vz (fun x => zQ x || x == 8) (fun _ => false) false false false) = true) ex hex)
  simp only [Bool.or_eq_true, beq_iff_eq] at hx
  rcases hx with hx | rfl
  · rw [hC x (by simp [zQ] at hx; omega)]; exact zQ_cell _ _ _ _ _ _ _ _ _ _ hx
  · rw [hC 8 (by decide)]; cellsimp; simp [ind, hp]

/-- The value part uses the terminal source level and carries no node-kind flags. -/
theorem plan_v {I : UpsInst} (iok : InstOk I) {p : Nat}
    (hC : ∀ x, x < 187 → C x = VC I p x) :
    ∀ ex ∈ UpsV3.cPlan, ((ev C D fst lst trn P ex : Int) : Fp) = 0 := by
  intro ex hex
  have hd := iok.D
  have hdep := getD3 I.dep I.D
  have hN := getD3 I.N I.D
  plan_mem <;> ups_ev [hC] <;> (try cellsimp) <;> apply cast0 <;>
    (try rfl) <;> simp only [ind] <;> (repeat' split) <;> omega

/-- All plan constraints, with explicit semantic conditions on the constructed parts. -/
theorem cPlan_ok {insts : List UpsInst} (ok : UpsOk insts)
    (parts : ∀ I ∈ insts, ∀ k, k < nQ I → PartOk I k (part I k))
    {H : Nat} (hH : R insts + 1 ≤ H) : GroupOk insts H UpsV3.cPlan := by
  apply groupOk_by ok hH (fun e he => by simp [UpsV3.constraints, he])
  · intro i hi t ht q _ _ C D P hC _
    exact plan_w hC
  · intro i hi p hp q _ _ C D P hC _
    exact plan_v (ok.inst _ (inst_mem hi)) hC
  · intro i hi k p hk hp q _ _ C D P hC _
    by_cases h0 : p = 0
    · subst p
      exact plan_q0 (ok.inst _ (inst_mem hi)) (parts _ (inst_mem hi) k hk) hC
    · exact plan_qn h0 hC

end

end UpsGen

end ZkFormal.NearV3.Render
