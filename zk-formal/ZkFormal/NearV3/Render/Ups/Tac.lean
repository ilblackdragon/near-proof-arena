import ZkFormal.NearV3.Render.Ups.Ok

/-!
# ZkFormal.NearV3.Render.Ups.Tac — tactics for the group proofs

* `ups_ev [hs…]`: unfold an integer evaluation `ev` of a `Dsl` expression of `upsV3` and rewrite
  the cells with the given equations (`hC : ∀ x, x < 187 → C x = …`);
* `cellsimp`: unfold the row-kind cells `WC` / `VC` / `QC` at literal columns (segment
  constants, walk, value, part constants, node rows), keeping the derived flags folded;
* `lt3 … lt16`: small ranges as disjunctions.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Render.EvI
  ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

namespace UpsGen

syntax "ups_ev" "[" (Lean.Parser.Tactic.simpLemma),* "]" : tactic
set_option maxRecDepth 4000 in
macro_rules
  | `(tactic| ups_ev [$ts,*]) => `(tactic| simp only [ev, Dsl.c, Dsl.n, Dsl.k, Dsl.sub, Dsl.mul3, Dsl.not,
      Dsl.smul, Dsl.sum, Dsl.bits, Dsl.mid, Dsl.bool, sumc, List.map, List.range_succ, List.range_zero,
      List.nil_append, List.cons_append, List.map_cons, List.map_nil, List.map_append, ite_true, ite_false,
      Bool.false_eq_true, Nat.reduceAdd, Nat.reducePow, Nat.reduceMul, Nat.reduceLT, Int.reduceNeg,
      UpsV3.act, wk, vb, qb, sf, wt1, wt2, wt3, pf, pl, tau, N0, N1, N2, L0, L1, L2, cLP, cBR, cBV, cBI, cLSa, cLSb,
      cLSc, cESl0, cESl1, cESn0, cESn1, dd0, dd1, dd2, ts1, ts2, ts3, ti0, ti1, ti2, tX, xb, px, bmL, bmH, pres, vid,
      UpsV3.nQ, UpsV3.rlen, UpsV3.j, kRDB, kRDE, kRLP, kRBR, kRBV, kRBI, kMVL, kMVE, kNLF, kWEX, kSPB, jo, sd0, sd1, sd2,
      UpsV3.sN, plen, qtl, qte, qtb1, qtb2, UpsV3.qhk, UpsV3.qodd, nokey, UpsV3.nochild, qlen, rootP, UpsV3.jm,
      UpsV3.clen, Kc, eL, eS, useA, UpsV3.bN, bL, cO, cS, Cc, UpsV3.neg, UpsV3.phk, UpsV3.podd, vcp, xcp, ba0, ba1,
      spY1, spY2, nN, nI, nib, nN2, nI2, ek, UpsV3.inv, hv, wbm, enter, lv0, lv1, lv2, trm, qpos, UpsV3.b, rd, rb,
      spos, UpsV3.u, sTAG, sHPL, sHPF, sKEY, sVLEN, sVH, sBM, sCH, sMEM, fs, fe, idx, fw, lastw, wfr, tgt, wy, wn,
      gD, dI, dL, cp, aft, reg, LR, SR, gMs, gMr, rx, mBv, mCv, mS, mK, mB, dep0, dep1, dep2, kPT, UpsV3.up,
      UpsV3.rc, pdep, UpsV3.cN, rcid, rdc, rootRid, tb, cb, cc, ci, ci2, X1, Ein, hb, lb, wb, upsId, Lexpr, symE,
      trmE, mDE, wbE, tagE, hiE, loE, tIE, DE, sdE, kRD, kM, splitE, pwE, pnE, spValE, spYE, twoE, spRecvE, s15E,
      winFr, tE, cbE, ccE, coE, sigE, depDE, depSE, K_VUPS, UpsV3.cases, UpsV3.states, UpsV3.kinds, nTE, nTermE,
      isT2, isT3, isT4, termE, kindCode, plan1, plan2, plan3, plan4, EK_KEY, EK_LEND, EK_VAL, EK_DOWN,
      SYM_START, SYM_END, $ts,*])

/-- Unfold the row-kind cells at literal columns. -/
syntax "cellsimp" : tactic
macro_rules
  | `(tactic| cellsimp) => `(tactic| simp only [WC, VC, QC, isSeg, isPC, segCell, wCell, vCell, pcCell, qRow,
      decide_true, decide_false, Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and, Bool.or_false,
      Bool.false_or, Bool.or_true, Bool.true_or, Bool.not_true, Bool.not_false, Nat.reduceLeDiff, Nat.reduceLT,
      Nat.reduceSub, Nat.reduceEqDiff, Nat.reduceBEq, Nat.reduceAdd, ite_true, ite_false, Bool.false_eq_true,
      Nat.lt_irrefl, Nat.le_refl, and_true, true_and, and_false, false_and, beq_self_eq_true,
      Nat.zero_add, Nat.add_zero, Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add, Int.one_mul, Int.mul_one,
      Int.sub_self, Int.neg_zero, Int.sub_zero])

theorem lt3 {x : Nat} (h : x < 3) : x = 0 ∨ x = 1 ∨ x = 2 := by omega
theorem lt11 {x : Nat} (h : x < 11) :
    x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7 ∨ x = 8 ∨ x = 9 ∨ x = 10 := by omega
theorem lt16 {x : Nat} (h : x < 16) :
    x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7 ∨ x = 8 ∨ x = 9 ∨ x = 10 ∨ x = 11 ∨
      x = 12 ∨ x = 13 ∨ x = 14 ∨ x = 15 := by omega

/-- A constraint vanishing by the zero cells of the current row. -/
theorem vzC {zc : Nat → Bool} {C D : Nat → Int} {fst lst trn : Int} {P : Nat → Int} {e : Expr}
    (hz : ∀ x, zc x = true → C x = 0) (hv : vz zc (fun _ => false) false false false e = true) :
    ((ev C D fst lst trn P e : Int) : Fp) = 0 := by
  rw [ev_vz hz (fun _ h => absurd h (by simp)) (fun h => absurd h (by simp)) (fun h => absurd h (by simp))
    (fun h => absurd h (by simp)) e hv]; rfl

theorem cast0 {z : Int} (h : z = 0) : ((z : Int) : Fp) = 0 := by rw [h]; rfl

/-- The goal of a group on an active row with given current cells. -/
def ActGoal (insts : List UpsInst) (es : List Expr) (q : Nat) (cells : Nat → Int) : Prop :=
  ∀ (C D P : Nat → Int), (∀ x, x < 187 → C x = cells x) → (∀ x, x < 187 → D x = nextCell insts q x) →
    ∀ ex ∈ es, ((ev C D (if q = 0 then 1 else 0) 0 1 P ex : Int) : Fp) = 0

/-- A group, by row kind. -/
theorem groupOk_by {insts : List UpsInst} (ok : UpsOk insts) {H : Nat} (hH : R insts + 1 ≤ H) {es : List Expr}
    (hsub : ∀ e ∈ es, e ∈ UpsV3.constraints)
    (hw : ∀ i, i < insts.length → ∀ t, t < 4 → ∀ q, q < R insts → (recs insts).getD q default = (i, .w t) →
      ActGoal insts es q (WC (inst insts i) t))
    (hv : ∀ i, i < insts.length → ∀ p, p < L (inst insts i) → ∀ q, q < R insts →
      (recs insts).getD q default = (i, .v p) → ActGoal insts es q (VC (inst insts i) p))
    (hq : ∀ i, i < insts.length → ∀ k p, k < nQ (inst insts i) → p < (part (inst insts i) k).q.length →
      ∀ q, q < R insts → (recs insts).getD q default = (i, .q k p) →
      ActGoal insts es q (QC (inst insts i) (part (inst insts i) k) k p
        (fieldAt (part (inst insts i) k).shape p).1 (fieldAt (part (inst insts i) k).shape p).2.1
        (fieldAt (part (inst insts i) k).shape p).2.2.1 (fieldAt (part (inst insts i) k).shape p).2.2.2
        (uU insts q))) :
    GroupOk insts H es := by
  apply groupOk_of ok.shape hH hsub
  intro q hq' C D P hC hD ex hex
  obtain ⟨i, hi, -, hk⟩ := actRow ok.shape hq'
  rcases hk with ⟨t, ht, hr⟩ | ⟨p, hp, hr⟩ | ⟨k, p, hk, hp, hr⟩ <;> rw [hr] at hC
  · exact hw i hi t ht q hq' hr C D P (fun x hx => by rw [hC x hx, rowCell_w]) hD ex hex
  · exact hv i hi p hp q hq' hr C D P (fun x hx => by rw [hC x hx, rowCell_v]) hD ex hex
  · exact hq i hi k p hk hp q hq' hr C D P (fun x hx => by rw [hC x hx, rowCell_q]) hD ex hex

/-- A group vanishing on value rows by their zero cells. -/
theorem actV_vz {insts : List UpsInst} {es : List Expr} {q : Nat} {I : UpsInst} {p : Nat}
    (h : es.all (vz zV (fun _ => false) false false false) = true) : ActGoal insts es q (VC I p) := by
  intro C D P hC _ ex hex
  exact vzC (zc := zV) (fun x hx => by rw [hC x (by simp [zV] at hx; omega)]; exact zV_cell _ _ _ hx)
    (List.all_eq_true.1 h ex hex)

end UpsGen

end ZkFormal.NearV3.Render
