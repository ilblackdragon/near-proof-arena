import ZkFormal.NearV3.Render.Node.Frame

/-!
# ZkFormal.NearV3.Render.Node.Facts — facts about one node row of the honest table
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Render.EvI
open ZkFormal.Near.Render.NodeGen (F Win layout bitOf b2n)

namespace NodeGen3

theorem rec_mem {vs : List NodeS3} {n : Nat} (hn : n < vs.length) : rec vs n ∈ vs := by
  simp only [rec, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some]
  exact List.getElem_mem _

theorem rec_eq {vs : List NodeS3} {n : Nat} (hn : n < vs.length) : rec vs n = vs[n] := by
  simp only [rec, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some]

theorem isTag_iff (f : F) : f.isTag = true ↔ f.state = 14 := by
  cases f <;> simp [NodeGen.F.isTag, F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH,
    Node.sBM, Node.sCH, Node.sMEM]

theorem state_range (f : F) : 14 ≤ f.state ∧ f.state ≤ 22 := by
  cases f <;> simp [F.state, Node.sTAG, Node.sHPL, Node.sHPF, Node.sKEY, Node.sVLEN, Node.sVH, Node.sBM, Node.sCH,
    Node.sMEM]

theorem typeOf_sum (v : NodeV3) : (typeOf v).1 + (typeOf v).2.1 + (typeOf v).2.2.1 + (typeOf v).2.2.2 = 1 := by
  cases v with
  | leaf => rfl
  | ext => rfl
  | branch sv => cases sv <;> rfl

theorem bits9 (D : Nat) (h : D < 512) :
    (bitOf D 0 + 2 * bitOf D 1 + 4 * bitOf D 2 + 8 * bitOf D 3) +
      16 * (bitOf D 4 + 2 * bitOf D 5 + 4 * bitOf D 6 + 8 * bitOf D 7) + 256 * bitOf D 8 = D := by
  simp only [bitOf, Nat.reducePow, Nat.div_one]; omega

theorem bitOf_le (x i : Nat) : bitOf x i ≤ 1 := by simp only [bitOf]; omega

theorem b2n_le (p : Prop) [Decidable p] : b2n (decide p) ≤ 1 := by simp only [b2n]; split <;> omega

section
variable {vs : List NodeS3} (ok : NodeOk vs) {n p : Nat} (hn : n < vs.length) (hp : p < (layN vs n).length)
include ok hn

theorem rwf : (rec vs n).v.wf := ok.wf.wf _ (rec_mem hn)
theorem rdepth : (rec vs n).depth < 400 := ok.depth _ (rec_mem hn)

theorem len_eq : ((rec vs n).v.ser false).length = (layN vs n).length := ser_len (rwf ok hn) false
theorem len_eq' : ((rec vs n).v.ser true).length = (layN vs n).length := ser_len (rwf ok hn) true

include hp

theorem fmem : ((layN vs n).getD p default).1 ∈ fieldsOf (rec vs n).v ∧
    ((layN vs n).getD p default).2 < ((layN vs n).getD p default).1.len (hplenOf (rec vs n).v) := by
  refine ⟨lay_mem _ _ ?_, lay_idx _ hp⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp]; exact List.getElem_mem _

theorem row_b (post : Bool) : ((rec vs n).v.ser post).getD p 0 =
    (fbytes (rec vs n).v post ((layN vs n).getD p default).1).getD ((layN vs n).getD p default).2 0 :=
  ser_getD (rwf ok hn) post hp

theorem tag_iff : ((layN vs n).getD p default).1.state = 14 ↔ p = 0 := by
  rw [← isTag_iff]; exact lay_tag _ p hp

theorem last_iff : p + 1 = (layN vs n).length ↔
    (((layN vs n).getD p default).1.state = 22 ∧ ((layN vs n).getD p default).2 = 7) :=
  lay_last_iff (rwf ok hn) hp

theorem first_idx (h0 : p = 0) : ((layN vs n).getD p default) = (F.tag, 0) := by
  subst h0
  obtain ⟨X, hX, _⟩ := fields_first (rec vs n).v
  simp only [layN, hX, NodeSeq.layout_cons, F.len, List.range_one, List.map_cons, List.map_nil,
    List.singleton_append]
  rfl

end

theorem R_pos {vs : List NodeS3} (ok : NodeOk vs) : 0 < R vs := by
  rw [R_off]; exact off_pos ok.pos

theorem map_getD' {α β : Type} (d : α) (F' : α → β) (l : List α) :
    (List.range l.length).map (fun t => F' (l.getD t d)) = l.map F' := by
  apply List.ext_getElem (by simp)
  intro i h1 h2; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < l.length by simpa using h1)]

theorem R_eq {vs : List NodeS3} (ok : NodeOk vs) : R vs = (vs.map fun s => (s.v.ser false).length).sum := by
  simp only [R, recsOf, List.length_flatMap, nodeRecs_len]
  rw [List.map_congr_left (g := fun n => ((rec vs n).v.ser false).length) (fun n hn =>
    (len_eq ok (List.mem_range.1 hn)).symm)]
  exact congrArg List.sum (map_getD' default (fun s : NodeS3 => (s.v.ser false).length) vs)

end NodeGen3

end ZkFormal.NearV3.Render
