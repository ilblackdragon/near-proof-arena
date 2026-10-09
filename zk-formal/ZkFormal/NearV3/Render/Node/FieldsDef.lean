import ZkFormal.NearV3.Render.Node.FieldFacts

/-!
# ZkFormal.NearV3.Render.Node.FieldsDef — `cFields` in four parts; closing tactics
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Render.EvI
open ZkFormal.Near.Render.NodeGen (F Win layout bitOf b2n)
open ZkFormal.Near.Render.NodeRow (wOf lwOf len_facts)

namespace NodeGen3

macro "fclose" : tactic => `(tactic| ((try simp only [b2n, decide_eq_true_eq]); (repeat' split) <;> first | omega | contradiction))

set_option hygiene false in
macro "fall" : tactic => `(tactic| first
  | (fclose; done)
  | (rcases hF.2.2.2.1 with ⟨h, h'⟩ | h <;> first | (simp [h, h']; done) | (simp [h, bitOf]; done))
  | (rcases hF.2.2.2.2.1 with h | ⟨h, h'⟩ <;> first | (simp [h, h']; done) | (simp [h]; done))
  | (rcases hF.2.2.1 with h | h <;> (try simp only [h, bitOf]) <;> fclose)
  | (rcases hF.1 with h | h <;> (try simp only [h]) <;> fclose)
  | (rcases hF.1 with h | h <;> (simp [h]; done))
  | (rcases hF.2.2.1 with h | h <;> (simp [h, bitOf]; done))
  | (have h6 := hF.2.2.2.2.2.2; revert h6; cases twOf (rec vs n).v <;> cases tvOf (rec vs n).v <;> (simp [b2n]; done))
  | (rcases (show nokeyOf (rec vs n).v = 0 ∨ nokeyOf (rec vs n).v = 1 by omega) with h | h <;>
      (try simp only [h]) <;> fclose))


section
open ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3
/-- `cFields`, in four parts. -/
def cfS : List Expr := states.map (fun x => .mul (Expr.mul (c act) (Dsl.not (c fe))) (sub (n x) (c x)))
def cfA : List Expr := [ .mul (Expr.mul (c act) (Dsl.not (c fe))) (sub (n idx) (.add (c idx) (k 1))),
    .mul (Expr.mul (c act) (Dsl.not (c fe))) (n fs),
    mul3 (c fe) (Dsl.not (c nl)) (n idx),
    mul3 (c fe) (Dsl.not (c nl)) (Dsl.not (n fs)),
    mul3 (c fe) (c sTAG) (c idx),
    mul3 (c fe) (c sHPL) (sub (c idx) (k 3)),
    mul3 (c fe) (c sHPF) (c idx),
    mul3 (c fe) (c sKEY) (sub (.add (c idx) (k 2)) (c hplen)),
    mul3 (c fe) (c sVLEN) (sub (c idx) (k 3)),
    mul3 (c fe) (c sVH) (sub (c idx) (k 31)),
    mul3 (c fe) (c sBM) (sub (c idx) (k 1)),
    mul3 (c fe) (c sCH) (sub (c idx) (k 31)),
    mul3 (c fe) (c sMEM) (sub (c idx) (k 7)) ]
def cfB : List Expr := [ mul3 (c fe) (c sTAG) (sub (.add (c tl) (c te)) (n sHPL)),
    mul3 (c fe) (c sTAG) (sub (c tb1) (n sBM)),
    mul3 (c fe) (c sTAG) (sub (c tb2) (n sVLEN)),
    mul3 (c fe) (c sHPL) (Dsl.not (n sHPF)),
    mul3 (c fe) (c sHPF) (sub (Dsl.not (c nokey)) (n sKEY)),
    mul3 (c fe) (c sHPF) (sub (.mul (c nokey) (c tl)) (n sVLEN)),
    mul3 (c fe) (c sHPF) (sub (.mul (c nokey) (c te)) (n sCH)),
    mul3 (c fe) (c sKEY) (sub (c tl) (n sVLEN)),
    mul3 (c fe) (c sKEY) (sub (c te) (n sCH)),
    mul3 (c fe) (c sVLEN) (Dsl.not (n sVH)),
    mul3 (c fe) (c sVH) (sub (c tl) (n sMEM)),
    mul3 (c fe) (c sVH) (sub (c tb2) (n sBM)),
    mul3 (c fe) (c sBM) (sub (c nochild) (n sMEM)),
    mul3 (c fe) (c sBM) (sub (Dsl.not (c nochild)) (n sCH)),
    mul3 (c fe) (c sCH) (sub (k 1) (.add (n sCH) (n sMEM))),
    mul3 (c fe) (c sCH) (sub (c lastw) (n sMEM)),
    .mul (c nokey) (sub (c hplen) (k 1)),
    .mul (c nochild) popE,
    .mul (c tv) (.add (c tb1) (c te)),
    .mul (c tw) (Dsl.not (c tv)),
    .mul (c dup) (Dsl.not (c act)),
    .mul (c hd) (Dsl.not (c act)) ]
def cfM : List Expr := (List.range 16).map (fun i => .mul (.add (c tl) (c te)) (c (bm i)))
end

theorem cFields_split : NodeV3.cFields = cfS ++ (cfA ++ cfB) ++ cfM := by
  simp only [NodeV3.cFields, cfS, cfA, cfB, cfM, List.cons_append, List.nil_append]

end NodeGen3

end ZkFormal.NearV3.Render
