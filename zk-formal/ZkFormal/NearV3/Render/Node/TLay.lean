import ZkFormal.NearV3.Render.Node.TSimple
import ZkFormal.NearV3.Render.Node.Win

/-!
# ZkFormal.NearV3.Render.Node.TLay — record traffic along the layout; window buses
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Dsl
open ZkFormal.Near.Render.NodeGen (F Win layout bitOf b2n)

namespace NodeGen3

/-- Along the layout. -/
theorem lay_flat {β : Type} (vs : List NodeS3) (n : Nat) (G : F × Nat → List β) :
    (List.range (layN vs n).length).flatMap (fun p => G ((layN vs n).getD p default)) =
      (fieldsOf (rec vs n).v).flatMap fun f => (List.range (f.len (hplenOf (rec vs n).v))).flatMap fun i => G (f, i) := by
  rw [← ZkFormal.Near.Render.flatMap_getD default (layN vs n) G]
  simp only [layN, layout, List.flatMap_assoc, List.flatMap_map]

/-- Records: `recN` along the layout, when the row messages depend on field, index and bytes only. -/
theorem recN_lay {vs : List NodeS3} (ok : NodeOk vs) {n : Nat} (hn : n < vs.length) (b : Nat) (sd : Bool)
    (G : F × Nat → List ZkFormal.Near.Msg)
    (hG : ∀ p, p < (layN vs n).length → rowN (rowCell vs (mkR vs n p)) b sd = G ((layN vs n).getD p default)) :
    recN vs n b sd = (fieldsOf (rec vs n).v).flatMap fun f =>
      (List.range (f.len (hplenOf (rec vs n).v))).flatMap fun i => G (f, i) := by
  rw [recN, ZkFormal.Near.Render.flatMap_congr' (fun p hp => hG p (List.mem_range.1 hp)), lay_flat]

/-- Child windows whose messages depend on the child only. -/
theorem wins_flat {β : Type} (kids : List NKid) (K : NKid → List β)
    (Hc : Win → List β) (hK : ∀ k w l s, Hc (kidWin k w l s) = K k) (K0 : K .none = []) :
    (branchWins kids).flatMap (fun f => match f with | .ch w => Hc w | _ => []) = kids.flatMap K := by
  unfold branchWins
  generalize hP : (kids.zip (List.range kids.length)).filter (fun x => x.1 ≠ .none) = P
  have h1 : ((P.zip (List.range P.length)).map (fun x => F.ch (kidWin x.1.1 x.2 (x.2 + 1 = P.length)
      (some x.1.2)))).flatMap (fun f => match f with | .ch w => Hc w | _ => []) = P.flatMap fun x => K x.1 := by
    rw [List.flatMap_map]
    have : ∀ (Q : List (NKid × Nat)) (L : List Nat), Q.length ≤ L.length →
        (Q.zip L).flatMap (fun x => Hc (kidWin x.1.1 x.2 (x.2 + 1 = P.length) (some x.1.2))) =
          Q.flatMap fun x => K x.1 := by
      intro Q
      induction Q with
      | nil => intro L _; simp
      | cons q Q ih =>
        intro L hL
        cases L with
        | nil => simp at hL
        | cons l L =>
          simp only [List.zip_cons_cons, List.flatMap_cons]
          rw [ih L (by simpa using hL), hK]
    exact this P _ (by simp)
  have h2 : (kids.zip (List.range kids.length)).flatMap (fun x => K x.1) = kids.flatMap K := by
    have : ∀ (Q : List NKid) (L : List Nat), Q.length ≤ L.length →
        (Q.zip L).flatMap (fun x => K x.1) = Q.flatMap K := by
      intro Q
      induction Q with
      | nil => intro L _; simp
      | cons q Q ih =>
        intro L hL
        cases L with
        | nil => simp at hL
        | cons l L => simp only [List.zip_cons_cons, List.flatMap_cons]; rw [ih L (by simpa using hL)]
    exact this kids _ (by simp)
  have h3 : P.flatMap (fun x => K x.1) = (kids.zip (List.range kids.length)).flatMap (fun x => K x.1) := by
    rw [← hP]
    generalize kids.zip (List.range kids.length) = Q
    induction Q with
    | nil => rfl
    | cons q Q ih =>
      by_cases hq : q.1 = .none
      · simp only [List.filter_cons, hq, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
          if_false, List.flatMap_cons, ih, K0, List.nil_append]
      · simp only [List.filter_cons, hq, ne_eq, not_false_eq_true, decide_true, if_true, List.flatMap_cons, ih]
  rw [h1, h3, h2]

theorem revealed_branch {β : Type} (sv : Option NSlot3) (kids : List NKid) (m : List Nat)
    (g : Nat × Nat × Nat × List Nat × List Nat → List β) :
    (NodeV3.branch sv kids m).revealed.flatMap g =
      kids.flatMap (fun k => match k with | .node c l r pre po => g (c, l, r, pre, po) | _ => []) := by
  simp only [NodeV3.revealed]
  induction kids with
  | nil => rfl
  | cons k kids ih => cases k <;> simp [List.filterMap_cons, ih]

theorem map32 (l : List Nat) (h : l.length = 32) : (List.range 32).map (fun j => l.getD (0 + j) 0) = l := by
  apply List.ext_getElem (by simp [h])
  intro i h1 h2; simp [List.getD_eq_getElem?_getD, show i < l.length by simp at h1; omega]

end NodeGen3

end ZkFormal.NearV3.Render
