import ZkFormal.NearV3.Render.Ups.Tac
import ZkFormal.NearV3.Render.WalkLocal

/-!
# ZkFormal.NearV3.Render.Ups.GWalk — `cWalk` on the honest table

**`cWalk_ok`**: the walk constraints hold on the honest table.  On a walk row `W_t` the
constraints are the walk conditions `WalkOkU` (`Ok.lean`) of `t` (and of `t + 1` for the
transition constraints); value and node rows have every walk flag zero (`vz`).

Method (UPSV3-DESIGN §8.3): the walk facts of the row are collected in one conjunction `fs`;
after unfolding the cells, split on the mode of the row (`wmode`), then close by `omega`
(after splitting the remaining indicators, `wfin`), the bit / two-value products (`nl_bool`,
`nl_13`), the inverse cell (`inv_cast`), or a further split on the next row's mode / on `t*`
(`wts`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Render.EvI
  ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

namespace UpsGen

/-- The inverse cell. -/
theorem inv_cast (a b : Nat) (ha : a < ZkFormal.Algebra.P) (hb : b < ZkFormal.Algebra.P) (h : a ≠ b) :
    ((((a : Int) - (b : Int)) * (((Fp.ofNat a - Fp.ofNat b)⁻¹).toNat : Int) - 1 : Int) : Fp) = 0 := by
  rw [Lean.Grind.Ring.intCast_sub, Lean.Grind.Ring.intCast_mul, Lean.Grind.Ring.intCast_sub,
    Lean.Grind.Ring.intCast_natCast, Lean.Grind.Ring.intCast_natCast, Lean.Grind.Ring.intCast_natCast]
  show (Fp.ofNat a - Fp.ofNat b) * Fp.ofNat ((Fp.ofNat a - Fp.ofNat b)⁻¹).toNat - ((1 : Int) : Fp) = 0
  rw [Fp.ofNat_toNat, Fp.mul_inv_cancel (WalkLocal.fp_ne ha hb h)]
  rfl

theorem sum_cast : ∀ l : List Nat, (l.map fun n : Nat => (n : Int)).sum = ((l.sum : Nat) : Int)
  | [] => rfl
  | a :: l => by simp [sum_cast l]

theorem bm_bits (x : Nat) (h : x < 2 ^ 16) :
    ((List.range 16).map fun i => (2 ^ i : Int) * ((x / 2 ^ i % 2 : Nat) : Int)).sum = x := by
  have := WalkGen.bits_sum x 16
  rw [Nat.mod_eq_of_lt h] at this
  have e : ((List.range 16).map fun i => (2 ^ i : Int) * ((x / 2 ^ i % 2 : Nat) : Int)) =
      ((List.range 16).map fun j => 2 ^ j * (x / 2 ^ j % 2)).map (fun n : Nat => (n : Int)) := by
    simp [List.map_map]
  rw [e, sum_cast, this]

theorem nl_bool {x : Nat} (h : x ≤ 1) : ((x : Int) * ((x : Int) + -((1 : Nat) : Int))) = 0 := by
  rcases (show x = 0 ∨ x = 1 by omega) with rfl | rfl <;> rfl

theorem nl_13 {x : Nat} (h : x = 1 ∨ x = 3) :
    (((x : Int) + -((1 : Nat) : Int)) * ((x : Int) + -((3 : Nat) : Int))) = 0 := by
  rcases h with rfl | rfl <;> rfl

/-- The inverse cell on `W1` (symbol `0`). -/
theorem inv_w1 {b : Nat} (hb : b < ZkFormal.Algebra.P) (h : 0 ≠ b) :
    ((((-(b : Int)) * (((Fp.ofNat 0 - Fp.ofNat b)⁻¹).toNat : Int) + -((1 : Nat) : Int)) : Int) : Fp) = 0 := by
  have := inv_cast 0 b (by decide) hb h
  rw [← this]; congr 1; try simp [Int.sub_eq_add_neg]

/-- The inverse cell on `W2`, `W3` (symbol `s`). -/
theorem inv_s {s b : Nat} (hs : s < ZkFormal.Algebra.P) (hb : b < ZkFormal.Algebra.P) (h : s ≠ b) :
    (((((s : Int) + -(b : Int)) * (((Fp.ofNat s - Fp.ofNat b)⁻¹).toNat : Int) + -((1 : Nat) : Int)) : Int) : Fp) = 0 := by
  have := inv_cast s b hs hb h
  rw [← this]; congr 1; try simp [Int.sub_eq_add_neg]

set_option hygiene false in
/-- Reduce literal indicators, levels, entries, bitmap registers, symbols in the facts `fs` and the goal. -/
macro "wred" : tactic => `(tactic| try simp only [Nat.reduceEqDiff, Nat.reduceLeDiff, Nat.reduceAdd, ind_True,
  ind_False, Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add, Int.one_mul, Int.mul_one, ite_true, ite_false,
  true_and, and_true, false_and, and_false, ne_eq, not_false_eq_true, not_true_eq_false, true_implies,
  false_implies, forall_const, Nat.zero_ne_one, Nat.one_ne_zero, true_or, or_true, false_or, or_false, true_iff,
  false_iff, iff_true, iff_false, lv, wReg, wsym, presV, vidV, SYM_START, SYM_END, List.getD_cons_succ, List.getD_cons_zero, Nat.reduceLT,
  Int.natCast_zero, EK_KEY, EK_LEND, EK_VAL, EK_DOWN] at fs ⊢)

set_option hygiene false in
/-- Split on the mode of walk row `t` (hypothesis `h`). -/
macro "wmode" t:term "," h:ident : tactic => `(tactic| (rcases (show (step I $t).mode = 0 ∨ (step I $t).mode = 1 ∨
  (step I $t).mode = 2 ∨ (step I $t).mode = 3 by omega) with $h:ident|$h:ident|$h:ident|$h:ident <;>
  simp only [$h:ident] at fs ⊢ <;> wred))

set_option hygiene false in
/-- Split on the terminal row `t*`. -/
macro "wts" : tactic => `(tactic| (rcases (show I.ts = 1 ∨ I.ts = 2 ∨ I.ts = 3 by omega) with ht|ht|ht <;>
  simp only [ht] at fs ⊢ <;> (try simp only [hm] at fs) <;> (try simp only [hm2] at fs) <;> wred))

set_option hygiene false in
/-- Split on the entry flag of walk row `t`. -/
macro "went" t:term : tactic => `(tactic| (rcases (show ent I $t = 0 ∨ ent I $t = 1 by omega) with he|he <;>
  simp only [he] at fs ⊢ <;> wred))

/-- Close by `omega` after splitting the remaining indicators. -/
macro "wfin" : tactic => `(tactic| (apply cast0; (try simp only [ind]); (try ((repeat' split) <;> omega)); done))

set_option hygiene false in
/-- Close the walk constraints of row `t` (next row `t + 1`). -/
macro "wclose" t:term "," t':term : tactic => `(tactic| (
  all_goals try (apply cast0; rfl)
  all_goals wmode $t, hm
  all_goals first
    | (apply cast0; rfl)
    | (apply cast0; omega)
    | exact cast0 (nl_bool (by omega))
    | exact cast0 (nl_13 (by omega))
    | wfin
    | exact inv_w1 (by omega) (by omega)
    | exact inv_s (by decide) (by omega) (by omega)
    | (wmode $t', hm2 <;> wfin)
    | (wts <;> wfin)
    | (went 1 <;> wfin)
    | (went 2 <;> wfin)
    | (went 1 <;> went 2 <;> wfin)
    | (wts <;> went 1 <;> went 2 <;> wfin)))

/-- The entry flag of a step row. -/
theorem ent_cases (I : UpsInst) (t : Nat) (ht : t = 1 ∨ t = 2) :
    (ent I t = 1 ∧ (step I t).mode = 0 ∧ (step I t).e.getD 4 0 = 0) ∨
      (ent I t = 0 ∧ ¬((step I t).mode = 0 ∧ (step I t).e.getD 4 0 = 0)) := by
  unfold ent; split
  · left; exact ⟨rfl, by omega, by omega⟩
  · right; exact ⟨rfl, by omega⟩

section
variable {I : UpsInst} (iok : InstOk I) {C D P : Nat → Int} {fst lst trn : Int}
include iok

set_option maxHeartbeats 4000000 in
theorem walk_w0 (hC : ∀ x, x < 200 → C x = WC I 0 x) (hD : ∀ x, x < 200 → D x = WC I 1 x) :
    ∀ ex ∈ UpsV3.cWalk, ((ev C D fst lst trn P ex : Int) : Fp) = 0 := by
  intro ex hex
  have W := iok.walk
  have hts := iok.ts; have hci := iok.ci; have hD3 := iok.D; have hti := iok.ti
  have m0 := W.mode 0 (by decide)
  have m1 := W.mode 1 (by decide)
  have fs := And.intro (ent_cases I 1 (by decide)) <| And.intro (ent_cases I 2 (by decide)) <| And.intro W.w0 <| And.intro (W.chain 0 (by decide)) <| And.intro W.tsStep <|
    And.intro W.termI <| And.intro W.termD <| And.intro W.termX <| And.intro W.termCase W.termEk
  wred
  simp only [UpsV3.cWalk, List.mem_cons, List.not_mem_nil, or_false] at hex
  rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ups_ev [hC, hD] <;> cellsimp <;> wred
  wclose 0, 1

set_option maxHeartbeats 4000000 in
theorem walk_w1 (hC : ∀ x, x < 200 → C x = WC I 1 x) (hD : ∀ x, x < 200 → D x = WC I 2 x) :
    ∀ ex ∈ UpsV3.cWalk, ((ev C D fst lst trn P ex : Int) : Fp) = 0 := by
  intro ex hex
  have W := iok.walk
  have hts := iok.ts; have hci := iok.ci; have hD3 := iok.D; have hti := iok.ti
  have m1 := W.mode 1 (by decide)
  have m2 := W.mode 2 (by decide)
  have fs := And.intro (ent_cases I 1 (by decide)) <| And.intro (ent_cases I 2 (by decide)) <| And.intro (W.stepE 1 (by decide) (by decide)) <| And.intro (W.chain 1 (by decide)) <|
    And.intro (W.drain 1 (by decide) (by decide)) <| And.intro (W.absK 1 (by decide)) <|
    And.intro (W.absB 1 (by decide)) <| And.intro (W.inRec 1 (by decide) (by decide)) <|
    And.intro (W.look 1 (by decide) (by decide)) <| And.intro W.tsStep <| And.intro W.termI <|
    And.intro W.termD <| And.intro W.termX <| And.intro W.termCase W.termEk
  wred
  simp only [UpsV3.cWalk, List.mem_cons, List.not_mem_nil, or_false] at hex
  rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ups_ev [hC, hD] <;> cellsimp <;> wred
  wclose 1, 2

set_option maxHeartbeats 4000000 in
theorem walk_w2 (hC : ∀ x, x < 200 → C x = WC I 2 x) (hD : ∀ x, x < 200 → D x = WC I 3 x) :
    ∀ ex ∈ UpsV3.cWalk, ((ev C D fst lst trn P ex : Int) : Fp) = 0 := by
  intro ex hex
  have W := iok.walk
  have hts := iok.ts; have hci := iok.ci; have hD3 := iok.D; have hti := iok.ti
  have m2 := W.mode 2 (by decide)
  have m3 := W.mode 3 (by decide)
  have fs := And.intro (ent_cases I 1 (by decide)) <| And.intro (ent_cases I 2 (by decide)) <| And.intro (W.stepE 2 (by decide) (by decide)) <| And.intro (W.chain 2 (by decide)) <|
    And.intro (W.drain 2 (by decide) (by decide)) <| And.intro (W.absK 2 (by decide)) <|
    And.intro (W.absB 2 (by decide)) <| And.intro (W.inRec 2 (by decide) (by decide)) <|
    And.intro (W.look 2 (by decide) (by decide)) <| And.intro W.tsStep <| And.intro W.termI <|
    And.intro W.termD <| And.intro W.termX <| And.intro W.termCase W.termEk
  wred
  simp only [UpsV3.cWalk, List.mem_cons, List.not_mem_nil, or_false] at hex
  rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ups_ev [hC, hD] <;> cellsimp <;> wred
  wclose 2, 3

set_option maxHeartbeats 4000000 in
theorem walk_w3 (hC : ∀ x, x < 200 → C x = WC I 3 x) :
    ∀ ex ∈ UpsV3.cWalk, ((ev C D fst lst trn P ex : Int) : Fp) = 0 := by
  intro ex hex
  have W := iok.walk
  have hts := iok.ts; have hci := iok.ci; have hD3 := iok.D; have hti := iok.ti
  have m3 := W.mode 3 (by decide)
  have m2 := W.mode 2 (by decide)
  have fs := And.intro (ent_cases I 1 (by decide)) <| And.intro (ent_cases I 2 (by decide)) <| And.intro (W.stepE 3 (by decide) (by decide)) <| And.intro (W.absK 3 (by decide)) <|
    And.intro (W.absB 3 (by decide)) <| And.intro (W.look 3 (by decide) (by decide)) <|
    And.intro W.tsStep <| And.intro W.termI <|
    And.intro W.termD <| And.intro W.termX <| And.intro W.termCase W.termEk
  wred
  simp only [UpsV3.cWalk, List.mem_cons, List.not_mem_nil, or_false] at hex
  rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ups_ev [hC] <;> cellsimp <;> wred
  wclose 3, 2

end

/-- A group vanishing on node rows by their zero cells. -/
theorem actQ_vz {insts : List UpsInst} {es : List Expr} {q : Nat} {I : UpsInst} {Q : UpsPartI}
    {k p st ix fl wi u : Nat}
    (h : es.all (vz zQ (fun _ => false) false false false) = true) :
    ActGoal insts es q (QC I Q k p st ix fl wi u) := by
  intro C D P hC _ ex hex
  exact vzC (zc := zQ) (fun x hx => by rw [hC x (by simp [zQ] at hx; omega)]; exact zQ_cell _ _ _ _ _ _ _ _ _ _ hx)
    (List.all_eq_true.1 h ex hex)

/-- **`cWalk`.** -/
theorem cWalk_ok {insts : List UpsInst} (ok : UpsOk insts) {H : Nat} (hH : R insts + 1 ≤ H) :
    GroupOk insts H UpsV3.cWalk := by
  apply groupOk_by ok hH (fun e he => by simp [UpsV3.constraints, he])
  · intro i hi t ht q hq hr C D P hC hD ex hex
    have iok := ok.inst _ (inst_mem hi)
    have hn : ∀ t', t' = t + 1 → t < 3 → ∀ x, x < 200 → D x = WC (inst insts i) t' x := by
      intro t' e h3 x hx
      rw [hD x hx, nextRow ok.shape hq hr (rk' := .w t') (by simp only [nextRK]; rw [if_pos h3, e]) x, rowCell_w]
    rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 by omega) with rfl | rfl | rfl | rfl
    · exact walk_w0 iok hC (hn 1 rfl (by decide)) ex hex
    · exact walk_w1 iok hC (hn 2 rfl (by decide)) ex hex
    · exact walk_w2 iok hC (hn 3 rfl (by decide)) ex hex
    · exact walk_w3 iok hC ex hex
  · intro i hi p hp q _ _
    exact actV_vz (by decide)
  · intro i hi k p hk hp q _ _
    exact actQ_vz (by decide)

end UpsGen

end ZkFormal.NearV3.Render
