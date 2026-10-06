import ZkFormal.NearV3.Render.Node.TAsm

/-!
# ZkFormal.NearV3.Render.Node.TSimple — record traffic: BYTES, PARENT (receive), DUP, ENT, SIZE
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Dsl
open ZkFormal.Near.Render.NodeGen (F Win layout bitOf b2n)

namespace NodeGen3

/-- `rowN` keeps exactly the pieces of bus `b`, side `sd`. -/
macro "rown_simp" : tactic => `(tactic| simp only [rowN, rowN0, rowNU, B_BYTES, B_DIGEST, B_PARENT, B_VPARENT, B_EDGE, B_BMAP,
  B_DIGS, B_DUP, B_ENT, B_SIZE, B_UPB, Nat.reduceEqDiff, true_and, and_true, false_and, and_false, ite_true, ite_false,
  List.nil_append, List.append_nil, Bool.false_eq_true, Bool.true_eq_false, decide_true, decide_false])

section
variable (vs : List NodeS3) (n p : Nat)

theorem rowN_bytesS : rowN (rowCell vs (mkR vs n p)) B_BYTES true =
    [[msgId K_NPRE n, p, ((rec vs n).v.ser false).getD p 0], [msgId K_NPOST n, p, ((rec vs n).v.ser true).getD p 0]] := by
  rown_simp; simp [Rc.c0, Rc.c4, Rc.c5, Rc.c8, Rc.c9, mkR, gt]

theorem rowN_parentR : rowN (rowCell vs (mkR vs n p)) B_PARENT false =
    gt (b2n (p = 0)) [n, (rec vs n).tau, (rec vs n).depth, ((rec vs n).v.ser false).length, (rec vs n).res] := by
  rown_simp; simp [Rc.c1, Rc.c4, Rc.c163, Rc.c7, Rc.c6, Rc.c153, mkR]

theorem rowN_dupR : rowN (rowCell vs (mkR vs n p)) B_DUP false =
    gt (b2n (p = 0 ∧ (rec vs n).dup = true)) [msgId K_NPRE n, (rec vs n).repE] := by
  rown_simp; simp [Rc.c144, Rc.c4, Rc.c172, mkR]

theorem rowN_entS : rowN (rowCell vs (mkR vs n p)) B_ENT true =
    gt (b2n (rec vs n).hd) [msgId K_NPRE n, ((rec vs n).v.ser false).length, p, ((rec vs n).v.ser false).getD p 0] := by
  rown_simp; simp [Rc.c171, Rc.c4, Rc.c6, Rc.c5, Rc.c8, mkR]

theorem rowN_entR : rowN (rowCell vs (mkR vs n p)) B_ENT false =
    gt (b2n (rec vs n).dup) [(rec vs n).repE, ((rec vs n).v.ser false).length, p, ((rec vs n).v.ser false).getD p 0] := by
  rown_simp; simp [Rc.c170, Rc.c172, Rc.c6, Rc.c5, Rc.c8, mkR]

theorem rowN_sizeS : rowN (rowCell vs (mkR vs n p)) B_SIZE true = [] := by
  rown_simp; simp [Rc.c3, gt]

theorem rowN_upb (sd : Bool) : rowN (rowCell vs (mkR vs n p)) B_UPB sd =
    [[msgId K_NPOST n, p, ((rec vs n).v.ser true).getD p 0, ((rec vs n).v.ser false).length, (rec vs n).depth,
      cidAt vs n p, if sd then 0 else (rec vs n).mU.getD p 0]] := by
  cases sd <;> (rown_simp; simp [Rc.c0, Rc.c4, Rc.c5, Rc.c9, Rc.c6, Rc.c7, Rc.c137, Rc.c185, mkR, gt, cidAt]; try rfl)

end

theorem gt_b2n (P : Prop) [Decidable P] (m : ZkFormal.Near.Msg) : gt (b2n (decide P)) m = if P then [m] else [] := by
  by_cases h : P <;> simp [gt, b2n, h]

theorem gt_b2n' (x : Bool) (m : ZkFormal.Near.Msg) : gt (b2n x) m = if x then [m] else [] := by
  cases x <;> rfl

section
variable {vs : List NodeS3} (ok : NodeOk vs) {n : Nat} (hn : n < vs.length)
include ok hn

theorem rec_bytesS : (recN vs n B_BYTES true).Perm
    (emitAt (msgId K_NPRE n) 0 ((rec vs n).v.ser false) ++ emitAt (msgId K_NPOST n) 0 ((rec vs n).v.ser true)) := by
  simp only [recN, rowN_bytesS]
  have h1 := len_eq ok hn
  have h2 := len_eq' ok hn
  refine (ZkFormal.Near.Render.perm_flatMap_append (List.range (layN vs n).length)
    (fun p => [[msgId K_NPRE n, p, ((rec vs n).v.ser false).getD p 0]])
    (fun p => [[msgId K_NPOST n, p, ((rec vs n).v.ser true).getD p 0]])).trans ?_
  simp only [emitAt, h1, h2, Nat.zero_add, ← List.map_eq_flatMap]
  exact List.Perm.refl _

theorem rec_parentR : recN vs n B_PARENT false =
    [[n, (rec vs n).tau, (rec vs n).depth, ((rec vs n).v.ser false).length, (rec vs n).res]] := by
  simp only [recN, rowN_parentR, gt_b2n]
  obtain ⟨m, hm⟩ : ∃ m, (layN vs n).length = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos (lay_pos (rec vs n).v)).symm⟩
  rw [hm, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
  simp

theorem rec_dupR : recN vs n B_DUP false = if (rec vs n).dup then [[msgId K_NPRE n, (rec vs n).repE]] else [] := by
  simp only [recN, rowN_dupR, gt_b2n]
  obtain ⟨m, hm⟩ : ∃ m, (layN vs n).length = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos (lay_pos (rec vs n).v)).symm⟩
  rw [hm, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
  cases (rec vs n).dup <;> simp

theorem rec_entS : recN vs n B_ENT true = if (rec vs n).hd then
    (List.range ((rec vs n).v.ser false).length).map fun p =>
      [msgId K_NPRE n, ((rec vs n).v.ser false).length, p, ((rec vs n).v.ser false).getD p 0] else [] := by
  simp only [recN, rowN_entS, gt_b2n', len_eq ok hn]
  cases (rec vs n).hd <;> simp [← List.map_eq_flatMap]

theorem rec_entR : recN vs n B_ENT false = if (rec vs n).dup then
    (List.range ((rec vs n).v.ser false).length).map fun p =>
      [(rec vs n).repE, ((rec vs n).v.ser false).length, p, ((rec vs n).v.ser false).getD p 0] else [] := by
  simp only [recN, rowN_entR, gt_b2n', len_eq ok hn]
  cases (rec vs n).dup <;> simp [← List.map_eq_flatMap]

theorem rec_sizeS : recN vs n B_SIZE true = [] := by
  simp [recN, rowN_sizeS]

theorem rec_upb (sd : Bool) :
    recN vs n B_UPB sd = upbOf n (rec vs n) (fun p => if sd then 0 else (rec vs n).mU.getD p 0) := by
  simp only [recN, rowN_upb, upbOf, ← len_eq ok hn]
  rw [← List.map_eq_flatMap]
  apply List.map_congr_left; intro p hp; rw [List.mem_range] at hp
  rw [show (rec vs n).ucid.getD p 0 = cidAt vs n p from ok.ucid n hn p hp]

end

end NodeGen3

end ZkFormal.NearV3.Render
