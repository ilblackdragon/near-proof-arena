import ZkFormal.NearV3.Rcpt.Render.Srcp.RowShape

namespace ZkFormal.NearV3.Render.SrcpGen
open ZkFormal.Near ZkFormal.Near.Render.EvI ZkFormal.Air ZkFormal.Algebra

set_option maxRecDepth 4096 in
/-- Accumulator bytes and digest enable gates agree on every generated descriptor. -/
theorem lookup_gate_polynomials (B : SrcpB) (z : Nat) (k : Kind) (g : Bool)
    (D P : Nat → Int) (fst lst trn : Int) (n : Nat) (hn : n = 57 ∨ n = 58) :
    ev (fun x => (({ frame B z k with gz := g }).cell x : Int)) D fst lst trn P
      (SrcpV3.constraints.getD n (.const 0)) = 0 := by
  cases k with
  | root =>
    rcases hn with hn | hn <;> subst n
    all_goals simp [SrcpV3.constraints, ev, Dsl.mul3, Dsl.sub, Dsl.c,
      frame, rootFrame, Frame.cell, SrcpV3.sg, SrcpV3.aw, SrcpV3.b, SrcpV3.reg,
      SrcpV3.gD, SrcpV3.rt, SrcpV3.wf]
  | leaf p =>
    by_cases hp : p = 0
    all_goals rcases hn with hn | hn <;> subst n
    all_goals simp [SrcpV3.constraints, ev, Dsl.mul3, Dsl.sub, Dsl.c,
      frame, leafFrame, Frame.cell, SrcpV3.sg, SrcpV3.aw, SrcpV3.b, SrcpV3.reg,
      SrcpV3.gD, SrcpV3.rt, SrcpV3.wf, hp, Int.add_right_neg]
  | path i o =>
    cases hd : (B.path.getD i default).dir <;> by_cases hw : 32 ≤ o <;>
      by_cases hf : o % 32 = 0
    all_goals simp only [List.getD_eq_getElem?_getD] at hd
    all_goals rcases hn with hn | hn <;> subst n
    all_goals simp [SrcpV3.constraints, ev, Dsl.mul3, Dsl.sub, Dsl.c,
      frame, pathFrame, Frame.cell, SrcpV3.sg, SrcpV3.aw, SrcpV3.b, SrcpV3.reg,
      SrcpV3.gD, SrcpV3.rt, SrcpV3.wf, hd, hw, hf, Int.add_right_neg]

/-- Both lookup gate polynomials vanish on active rows and SIZE-only padding. -/
theorem row_lookup_gate (bs : List SrcpB) (r : Nat)
    (D P : Nat → Int) (fst lst trn : Int) (n : Nat) (hn : n = 57 ∨ n = 58) :
    ev (fun x => (cell bs r x : Int)) D fst lst trn P
      (SrcpV3.constraints.getD n (.const 0)) = 0 := by
  by_cases hr : r < R bs
  · simp only [cell, hr, ite_true, rowFrame]
    exact lookup_gate_polynomials _ _ _ _ D P fst lst trn n hn
  · have hp : R bs ≤ r := by omega
    rcases hn with hn | hn <;> subst n
    all_goals simp [padding_cell hp, SrcpV3.constraints, ev, Dsl.mul3, Dsl.sub, Dsl.c,
      SrcpV3.sg, SrcpV3.aw, SrcpV3.b, SrcpV3.reg, SrcpV3.sz,
      SrcpV3.gD, SrcpV3.rt, SrcpV3.wf]

theorem lookup_gate_constraints {bs : List SrcpB} {tr : Trace Fp}
    {tt r : Nat} {pub : List Fp}
    (hc : ∀ x, tr.cell tt r x = Fp.ofNat (cell bs r x))
    (n : Nat) (hn : n = 57 ∨ n = 58) :
    (SrcpV3.constraints.getD n (.const 0)).eval tr tt r pub = 0 := by
  apply eval_zero_of_ev (C := fun x => (cell bs r x : Int))
    (D := fun x => ((tr.cell tt ((r + 1) % tr.height tt) x).toNat : Int))
  · intro x
    rw [hc x, ofNat_int]
  · intro x
    rw [← ofNat_int, Fp.ofNat_toNat]
  · exact row_lookup_gate bs r _ _ _ _ _ n hn

end ZkFormal.NearV3.Render.SrcpGen
