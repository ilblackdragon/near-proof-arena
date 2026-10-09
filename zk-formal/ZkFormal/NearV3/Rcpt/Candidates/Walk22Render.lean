/- Candidate log22 generalization of Render/WalkRender.lean. Frozen renderer unchanged;
all cells and interactions retain their original definitions. -/
import ZkFormal.NearV3.Rcpt.Candidates.Walk22Local

/-!
# ZkFormal.NearV3.Render.WalkRender — traffic of the honest `walkV3` table

For honest walks `ws` (`WalkOk ws`) and any trace whose table `t` has the cells of
`WalkGen.cell ws` (`Render/WalkGen.lean`):
* `walk_render_local` (`Render/WalkLocal.lean`): `TableLocal WalkV3.table`;
* `walk_render_traffic`: the traffic is `walkTraffic3 ws`.  Row `(wv, j)` receives
  `KEYNIB (w, j − 1, sym, [last])` for `j ≠ 0`, receives / sends its edge (`u`, `u + 1`) in
  modes 0–1 and its `BMAP` message (`ub`, `ub + 1`) in mode 2, and sends
  `FINAL (w, τ, fk, k)` on the last row; padding rows nothing.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Candidates.Walk22Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl
open ZkFormal.NearV3.WalkV3 (act ws we gK w tau sym nN nI nib nN2 nI2 ek u mS mK mB mD inv hv ub fk kk bmb
  bmE selIdx selSum selBit absE modes boolCols)
open WalkGen WalkLocal
open ZkFormal.NearV3.Render.UniqLocal (ofNat0 ofNat1)

namespace WalkTraffic

/-- The messages of row record `p` on bus `b`, side `sd` (as naturals). -/
def rowMsgs (p : WalkGen.Rec) (b : Nat) (sd : Bool) : List ZkFormal.Near.Msg :=
  (if b = B_KEYNIB ∧ sd = false ∧ p.2 ≠ 0 then
    [[p.1.w, p.2 - 1, (stp p).sym, if p.2 + 1 = p.1.steps.length then 1 else 0]] else []) ++
  (if b = B_EDGE ∧ sd = false ∧ (stp p).mode ≤ 1 then [(stp p).edgeMsg (stp p).u] else []) ++
  (if b = B_EDGE ∧ sd = true ∧ (stp p).mode ≤ 1 then [(stp p).edgeMsg ((stp p).u + 1)] else []) ++
  (if b = B_BMAP ∧ sd = false ∧ (stp p).mode = 2 then [(stp p).bmapMsg (stp p).ub] else []) ++
  (if b = B_BMAP ∧ sd = true ∧ (stp p).mode = 2 then [(stp p).bmapMsg ((stp p).ub + 1)] else []) ++
  (if b = B_FINAL ∧ sd = true ∧ p.2 + 1 = p.1.steps.length then [[p.1.w, p.1.tau, p.1.fk, p.1.k]] else [])

theorem ite_map {P Q : Prop} [Decidable P] [Decidable Q] {x : List Fp} {m : ZkFormal.Near.Msg} (h : P ↔ Q)
    (hm : Q → x = Msg.toFp m) : (if P then [x] else []) = (if Q then [m] else []).map Msg.toFp := by
  by_cases hq : Q
  · rw [if_pos (h.2 hq), if_pos hq, hm hq]; rfl
  · rw [if_neg (fun hp => hq (h.1 hp)), if_neg hq]; rfl

theorem ofNat_ite_one (P : Prop) [Decidable P] : Fp.ofNat (if P then 1 else 0) = 1 ↔ P := by
  split <;> simp_all [ofNat0, ofNat1]

theorem list6 : ∀ (l : List Nat), l.length = 6 →
    l = [l.getD 0 0, l.getD 1 0, l.getD 2 0, l.getD 3 0, l.getD 4 0, l.getD 5 0]
  | [_, _, _, _, _, _], _ => rfl

theorem bits_val (x : Nat) (hx : x < 2 ^ 16) :
    ((List.range 16).map fun j => 2 ^ j * (x / 2 ^ j % 2)).sum = x := by
  rw [bits_sum x 16, Nat.mod_eq_of_lt hx]

section rows
variable {L : List WalkR} (hok : WalkOk L) {tr : Trace Fp} {tt : Nat} {pub : List Fp} {H : Nat}
  (hH : tr.height tt = H) (hHS : rows L ≤ H)
  (hc : ∀ q col, q < H → col < 56 → tr.cell tt q col = Fp.ofNat (WalkGen.cell L H q col))
include hok hH hHS hc

theorem rowAct {q : Nat} (hq : q < H) (ha : q < rows L) (b : Nat) (sd : Bool) :
    rowTraffic WalkV3.interactions tr tt q pub b sd = (rowMsgs ((recs L).getD q default) b sd).map Msg.toFp := by
  have cq := fun (x : Nat) (hx : x < 56) => cA hok hH hHS hc hq ha hx
  have hp := recs_getD_mem ha
  obtain ⟨Fj, Fn, Fm, Fe, FS, FK, FB, FE, F0, FL, FC⟩ := rowF hok hp
  generalize hpp : (recs L).getD q default = p at cq Fj Fn Fm Fe FS FK FB FE F0 FL FC
  have he6 := list6 _ Fe
  have hbm : (stp p).mode = 2 → bmE.eval tr tt q pub = Fp.ofNat (stp p).bm := by
    intro h2
    have := WalkProof.evsum (tr := tr) (tt := tt) (pub := pub) (r := q) 16
      (fun j => smul (2 ^ j) (c (bmb j))) (fun j => 2 ^ j * ((stp p).bm / 2 ^ j % 2)) (fun j hj => by
        rw [eval_smul, eval_c, cq _ (by simp only [bmb]; omega), cellBmb p hj, if_pos h2, natCast_mul]; rfl)
    simp only [bmE, bits, Nat.zero_add]
    rw [this, bits_val _ (FB h2).2.1]; rfl
  rw [WalkProof.rowT]
  simp only [rowMsgs, List.map_append]
  have ap : ∀ {a b c d : List (List Fp)}, a = b → c = d → a ++ c = b ++ d := by
    intro a b c d h1 h2; rw [h1, h2]
  refine ap (ap (ap (ap (ap ?_ ?_) ?_) ?_) ?_) ?_
  · apply ite_map
    · rw [cq _ (by decide)]; simp only [gK, rowCell]
      constructor
      · rintro ⟨h1, h2, h3⟩; refine ⟨h1, h2, fun h0 => ?_⟩; rw [if_pos h0, ofNat0] at h3; exact fp_zero_ne_one h3
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by rw [if_neg h3]; rfl⟩
    · intro _; simp only [cq, w, WalkV3.t, sym, we, Nat.reduceLT, rowCell, Msg.toFp, List.map_cons, List.map_nil]
  · apply ite_map
    · rw [cq _ (by decide), cq _ (by decide)]; simp only [mS, mK, rowCell, ofNat_add']
      apply and_congr Iff.rfl; apply and_congr Iff.rfl
      constructor
      · intro h; apply Classical.byContradiction; intro hn
        rw [if_neg (by omega), if_neg (by omega)] at h; exact fp_zero_ne_one h
      · intro h; rcases (show (stp p).mode = 0 ∨ (stp p).mode = 1 by omega) with h' | h' <;> simp [h'] <;> rfl
    · intro _
      simp only [WalkProof.cellsE, cq, nN, nI, nib, nN2, nI2, ek, u, Nat.reduceLT, rowCell, WStep3.edgeMsg,
        Msg.toFp]
      rw [he6]
      simp
  · apply ite_map
    · rw [cq _ (by decide), cq _ (by decide)]; simp only [mS, mK, rowCell, ofNat_add']
      apply and_congr Iff.rfl; apply and_congr Iff.rfl
      constructor
      · intro h; apply Classical.byContradiction; intro hn
        rw [if_neg (by omega), if_neg (by omega)] at h; exact fp_zero_ne_one h
      · intro h; rcases (show (stp p).mode = 0 ∨ (stp p).mode = 1 by omega) with h' | h' <;> simp [h'] <;> rfl
    · intro _
      simp only [WalkProof.cellsE, cq, nN, nI, nib, nN2, nI2, ek, u, Nat.reduceLT, rowCell, WStep3.edgeMsg,
        Msg.toFp]
      rw [he6]
      simp [ZkFormal.NearV3.Render.UniqLocal.ofNat_succ]
  · apply ite_map
    · rw [cq _ (by decide)]; simp only [mB, rowCell, ofNat_ite_one]
    · intro h
      have h2 := h.2.2
      simp only [WalkProof.cellsB, cq, nN, hv, ub, Nat.reduceLT, rowCell, WStep3.bmapMsg, Msg.toFp,
        List.map_cons, List.map_nil, hbm h2, h2, if_true]
  · apply ite_map
    · rw [cq _ (by decide)]; simp only [mB, rowCell, ofNat_ite_one]
    · intro h
      have h2 := h.2.2
      simp only [WalkProof.cellsB, cq, nN, hv, ub, Nat.reduceLT, rowCell, WStep3.bmapMsg, Msg.toFp,
        List.map_cons, List.map_nil, hbm h2, h2, if_true, ZkFormal.NearV3.Render.UniqLocal.ofNat_succ]
  · apply ite_map
    · rw [cq _ (by decide)]; simp only [we, rowCell, ofNat_ite_one]
    · intro h
      simp only [cq, w, tau, fk, kk, Nat.reduceLT, rowCell, h.2.2, if_true, Msg.toFp, List.map_cons, List.map_nil]

theorem rowPad {q : Nat} (hq : q < H) (ha : ¬ q < rows L) (b : Nat) (sd : Bool) :
    rowTraffic WalkV3.interactions tr tt q pub b sd = [] := by
  have cq := fun (x : Nat) (hx : x < 56) => cP hok hH hHS hc hq ha hx
  rw [WalkProof.rowT]
  simp only [cq, gK, mS, mK, mB, we, Nat.reduceLT, fp_zero_ne_one, and_false, if_false, List.append_nil]
  have : ¬ ((0 : Fp) + 0 = 1) := by grind
  simp [this]

end rows

/-! ## Per-walk message lists -/

theorem flat_opt {α β : Type} (p : α → Prop) [DecidablePred p] (f : α → β) (l : List α) :
    (l.filter fun x => decide (p x)).map f = l.flatMap fun x => if p x then [f x] else [] := by
  rw [WalkProof.filter_map_fm]; congr 1; funext x; simp

theorem steps_flat {β : Type} (wv : WalkR) (g : WStep3 → List β) :
    wv.steps.flatMap g = (List.range wv.steps.length).flatMap fun j => g (stp (wv, j)) :=
  flatMap_getD default wv.steps g

theorem keynib_flat (wv : WalkR) (h : 1 ≤ wv.steps.length) :
    (List.range wv.steps.length).flatMap (fun j =>
      if j ≠ 0 then [[wv.w, j - 1, (stp (wv, j)).sym, if j + 1 = wv.steps.length then 1 else 0]] else []) =
    (List.range (wv.steps.length - 1)).map fun t =>
      [wv.w, t, (wv.step (t + 1)).sym, if t + 2 = wv.steps.length then 1 else 0] := by
  obtain ⟨m, hm⟩ : ∃ m, wv.steps.length = m + 1 := ⟨wv.steps.length - 1, by omega⟩
  rw [hm, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, Nat.add_sub_cancel]
  simp only [ne_eq, not_true_eq_false, if_false, List.nil_append, Nat.add_one_ne_zero, not_false_eq_true,
    if_true, Nat.add_sub_cancel, stp]
  rw [flatMap_single (g := fun t => [wv.w, t, (wv.step (t + 1)).sym, if t + 2 = m + 1 then 1 else 0])
    (fun t _ => by simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, show t + 1 + 1 = t + 2 by omega])]

/-- The messages of one walk's rows, per bus. -/
theorem walk_msgs (wv : WalkR) (h : 1 ≤ wv.steps.length) (b : Nat) (sd : Bool) :
    (List.range wv.steps.length).flatMap (fun j => rowMsgs (wv, j) b sd) =
      if sd then walkSends3 [wv] b else walkRecvs3 [wv] b := by
  have h1 : B_KEYNIB ≠ B_EDGE := by decide
  have h2 : B_KEYNIB ≠ B_BMAP := by decide
  have h3 : B_EDGE ≠ B_BMAP := by decide
  have h4 : B_EDGE ≠ B_FINAL := by decide
  have h5 : B_BMAP ≠ B_FINAL := by decide
  have h6 : B_KEYNIB ≠ B_FINAL := by decide
  have hs := And.intro h1.symm (And.intro h2.symm (And.intro h3.symm (And.intro h4.symm (And.intro h5.symm h6.symm))))
  simp only [ne_eq] at hs
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hs
  have hfin : (List.range wv.steps.length).flatMap (fun j =>
      if j + 1 = wv.steps.length then [[wv.w, wv.tau, wv.fk, wv.k]] else []) = [[wv.w, wv.tau, wv.fk, wv.k]] := by
    obtain ⟨m, hm⟩ : ∃ m, wv.steps.length = m + 1 := ⟨wv.steps.length - 1, by omega⟩
    rw [hm, List.range_succ, List.flatMap_append,
      flatMap_nil' (fun j hj => by have := List.mem_range.1 hj; rw [if_neg (by omega)])]
    simp
  cases sd
  · simp only [Bool.false_eq_true, if_false, walkRecvs3, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    by_cases hE : b = B_EDGE
    · subst hE
      simp only [if_true, flat_opt, steps_flat, rowMsgs, g1, g2, g3, g4, g5, g6, h1, h3, h4, false_and, and_false, if_false,
        List.nil_append, List.append_nil, true_and, Bool.false_eq_true, and_self]
    · by_cases hB : b = B_BMAP
      · subst hB
        simp only [hE, if_false, if_true, flat_opt, steps_flat, rowMsgs, g1, g2, g3, g4, g5, g6, h2, h3.symm, h5, false_and, and_false,
          List.nil_append, List.append_nil, true_and, Bool.false_eq_true, and_self, Ne.symm h3, Ne.symm h2]
      · by_cases hK : b = B_KEYNIB
        · subst hK
          simp only [hE, hB, if_false, if_true, rowMsgs, g1, g2, g3, g4, g5, g6, h1, h2, h6, false_and, and_false, List.nil_append,
            List.append_nil, true_and, Bool.false_eq_true, and_self]
          exact keynib_flat wv h
        · simp only [hE, hB, hK, if_false, rowMsgs, false_and, List.nil_append, List.append_nil]
          exact flatMap_nil' (fun _ _ => by simp)
  · simp only [if_true, walkSends3, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    by_cases hE : b = B_EDGE
    · subst hE
      simp only [if_true, flat_opt, steps_flat, rowMsgs, g1, g2, g3, g4, g5, g6, h1, h3, h4, false_and, and_false, if_false,
        List.nil_append, List.append_nil, true_and, Bool.true_eq_false, and_self]
    · by_cases hB : b = B_BMAP
      · subst hB
        simp only [hE, if_false, if_true, flat_opt, steps_flat, rowMsgs, g1, g2, g3, g4, g5, g6, h2, h3.symm, h5, false_and, and_false,
          List.nil_append, List.append_nil, true_and, Bool.true_eq_false, and_self, Ne.symm h3, Ne.symm h2]
      · by_cases hF : b = B_FINAL
        · subst hF
          simp only [hE, hB, if_false, if_true, rowMsgs, g1, g2, g3, g4, g5, g6, Ne.symm h4, Ne.symm h5, Ne.symm h6, false_and, and_false,
            List.nil_append, List.append_nil, true_and, and_self, List.map_cons, List.map_nil]
          exact hfin
        · simp only [hE, hB, hF, if_false, rowMsgs, false_and, List.nil_append, List.append_nil, and_false]
          exact flatMap_nil' (fun _ _ => by simp)

theorem recs_msgs (L : List WalkR) (hlen : ∀ wv ∈ L, 1 ≤ wv.steps.length) (b : Nat) (sd : Bool) :
    (recs L).flatMap (fun p => rowMsgs p b sd) = if sd then walkSends3 L b else walkRecvs3 L b := by
  rw [walkSends3_flat, walkRecvs3_flat]
  simp only [recs, List.flatMap_assoc, List.flatMap_map]
  cases sd
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact ZkFormal.Near.Render.flatMap_congr' (fun wv hw => by
      have := walk_msgs wv (hlen wv hw) b false; simp only [Bool.false_eq_true, ↓reduceIte] at this; exact this)
  · simp only [↓reduceIte]
    exact ZkFormal.Near.Render.flatMap_congr' (fun wv hw => by
      have := walk_msgs wv (hlen wv hw) b true; simp only [↓reduceIte] at this; exact this)

end WalkTraffic

open WalkTraffic in
/-- **The honest `walkV3` table has the traffic of `ws`.**  Same hypotheses on the trace as
`walk_render_local`. -/
theorem walk_render_traffic_at (ws : List WalkR) (hok : WalkOk ws) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (hle : rows ws ≤ tr.height t)
    (hcell : ∀ r x, r < tr.height t → x < WalkV3.width →
      tr.cell t r x = Fp.ofNat (WalkGen.cell ws (tr.height t) r x)) :
    TableTraffic WalkV3.interactions tr t pub (walkTraffic3 ws) := by
  have hall : ∀ sd b, (List.range (tr.height t)).flatMap (fun r => rowTraffic WalkV3.interactions tr t r pub b sd) =
      (if sd then walkSends3 ws b else walkRecvs3 ws b).map Msg.toFp := by
    intro sd b
    rw [range_split hle, List.flatMap_append,
      flatMap_nil' (l := List.map _ _) (fun q hq => by
        obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
        exact rowPad hok rfl hle hcell (by have := List.mem_range.1 hq'; omega) (by omega) b sd),
      List.append_nil,
      flatMap_congr' (g := fun q => (rowMsgs ((recs ws).getD q default) b sd).map Msg.toFp) (fun q hq =>
        rowAct hok rfl hle hcell (by have := List.mem_range.1 hq; omega) (List.mem_range.1 hq) b sd),
      ← recs_msgs ws (len1 hok) b sd, ← recs_length,
      ← flatMap_getD default (recs ws) (fun p => (rowMsgs p b sd).map Msg.toFp), List.map_flatMap]
  apply traffic_of
  · intro b; rw [hall true b]; exact List.Perm.refl _
  · intro b; rw [hall false b]; exact List.Perm.refl _

open WalkTraffic in
/-- **The honest `walkV3` table has the traffic of `ws`.**  Same hypotheses on the trace as
`walk_render_local`. -/
theorem walk_render_traffic (ws : List WalkR) (hok : WalkOk ws) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (hlog : tr.log t = logOf (rows ws))
    (hcell : ∀ r x, r < tr.height t → x < WalkV3.width →
      tr.cell t r x = Fp.ofNat (WalkGen.cell ws (tr.height t) r x)) :
    TableTraffic WalkV3.interactions tr t pub (walkTraffic3 ws) := by
  apply walk_render_traffic_at ws hok tr t pub
  · simp only [Trace.height, hlog]; exact le_pow_logOf _
  · exact hcell

end ZkFormal.NearV3.Candidates.Walk22Render
