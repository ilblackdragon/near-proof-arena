import ZkFormal.NearV3.Rcpt.Render.Srcp.Boolean
import ZkFormal.Near.Render.Proof.NodeEv

namespace ZkFormal.NearV3.Render.SrcpGen
open ZkFormal.Near ZkFormal.Near.Render.EvI ZkFormal.Air

/-- Indices of row-local segment shape polynomials in the actual table. -/
def shapeIndices : List Nat := [13, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- Root and segment shape equations are satisfied without successor assumptions. -/
theorem shape_polynomials (B : SrcpB) (z : Nat) (k : Kind) (hk : k ∈ kinds B)
    (D P : Nat → Int) (fst lst trn : Int) (n : Nat) (hn : n ∈ shapeIndices) :
    ev (fun x => ((frame B z k).cell x : Int)) D fst lst trn P
      (SrcpV3.constraints.getD n (.const 0)) = 0 := by
  have hb (b : Bool) : b = true ∨ b = false := by cases b <;> simp
  have hk' := (mem_kinds B k).mp hk
  cases k with
  | root =>
    simp only [shapeIndices, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h | h | h | h | h | h | h | h | h | h | h | h
    all_goals subst n
    all_goals simp [SrcpV3.constraints, ev, Dsl.bool, Dsl.mul3, Dsl.sub, Dsl.not,
      Dsl.c, Dsl.k, Dsl.smul, frame, rootFrame, Frame.cell,
      SrcpV3.rt, SrcpV3.sg, SrcpV3.lf, SrcpV3.wf, SrcpV3.wl, SrcpV3.wn,
      SrcpV3.sf, SrcpV3.sl, SrcpV3.pw, SrcpV3.dir, SrcpV3.aw, Int.add_right_neg]
  | leaf p =>
    have hp : p < 32 := by simpa using hk'
    by_cases h0 : p = 0 <;> by_cases h31 : p = 31
    all_goals
      simp only [shapeIndices, List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with h | h | h | h | h | h | h | h | h | h | h | h
    all_goals subst n
    all_goals simp [SrcpV3.constraints, ev, Dsl.bool, Dsl.mul3, Dsl.sub, Dsl.not,
      Dsl.c, Dsl.k, Dsl.smul, frame, leafFrame, Frame.cell,
      SrcpV3.rt, SrcpV3.sg, SrcpV3.lf, SrcpV3.wf, SrcpV3.wl, SrcpV3.wn,
      SrcpV3.sf, SrcpV3.sl, SrcpV3.pw, SrcpV3.dir, SrcpV3.aw, h0, h31]
  | path i o =>
    have ho : o < 64 := (show i < B.path.length ∧ o < 64 by simpa using hk').2
    have hf := path_first_flag B z i o ho
    have hl := path_last_flag B z i o ho
    by_cases h0 : o = 0 <;> by_cases h63 : o = 63 <;>
      by_cases hw : o % 32 = 0 <;> by_cases he : o % 32 = 31 <;>
      by_cases hn32 : 32 ≤ o
    all_goals try omega
    all_goals rcases hb (B.path.getD i default).dir with hd | hd
    all_goals simp only [List.getD_eq_getElem?_getD] at hd
    all_goals
      simp only [shapeIndices, List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with h | h | h | h | h | h | h | h | h | h | h | h
    all_goals subst n
    all_goals simp [SrcpV3.constraints, ev, Dsl.bool, Dsl.mul3, Dsl.sub, Dsl.not,
      Dsl.c, Dsl.k, Dsl.smul, frame, pathFrame, Frame.cell,
      SrcpV3.rt, SrcpV3.sg, SrcpV3.lf, SrcpV3.wf, SrcpV3.wl, SrcpV3.wn,
      SrcpV3.sf, SrcpV3.sl, SrcpV3.pw, SrcpV3.dir, SrcpV3.aw, h0, h63, hw, he, hn32, hd, Int.add_right_neg]

/-- SIZE's terminal gate does not affect any local shape equation. -/
theorem shape_gz (C : Frame) (g : Bool) (D P : Nat → Int) (fst lst trn : Int)
    (n : Nat) (hn : n ∈ shapeIndices) :
    ev (fun x => (({ C with gz := g }).cell x : Int)) D fst lst trn P
        (SrcpV3.constraints.getD n (.const 0)) =
      ev (fun x => (C.cell x : Int)) D fst lst trn P
        (SrcpV3.constraints.getD n (.const 0)) := by
  simp only [shapeIndices, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst n; rfl

/-- The shape polynomials vanish on every active rendered row. -/
theorem active_shape (bs : List SrcpB) (r : Nat) (hr : r < R bs)
    (D P : Nat → Int) (fst lst trn : Int) (n : Nat) (hn : n ∈ shapeIndices) :
    ev (fun x => (cell bs r x : Int)) D fst lst trn P
      (SrcpV3.constraints.getD n (.const 0)) = 0 := by
  have hm : (recs bs).getD r default ∈ recs bs := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr]
    exact List.getElem_mem _
  have hk := (mem_recs hm).2
  simp only [cell, hr, ite_true, rowFrame]
  rw [shape_gz (n := n) (hn := hn)]
  exact shape_polynomials _ _ _ hk D P fst lst trn n hn

end ZkFormal.NearV3.Render.SrcpGen
