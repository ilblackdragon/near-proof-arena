import ZkFormal.NearV3.Rcpt.Render.Srcp.Duplicate

namespace ZkFormal.NearV3.Render.SrcpGen
open ZkFormal.Near ZkFormal.Near.Render.EvI ZkFormal.Air

def windowStepIndices : List Nat := [19, 20, 21, 35, 36, 37, 38, 39, 40, 41, 42, 43]

private theorem indices_cases {n : Nat} (hn : n ∈ windowStepIndices) :
    n = 19 ∨ n = 20 ∨ n = 21 ∨ n = 35 ∨ n = 36 ∨ n = 37 ∨ n = 38 ∨
    n = 39 ∨ n = 40 ∨ n = 41 ∨ n = 42 ∨ n = 43 := by
  simpa [windowStepIndices] using hn

macro "step_simp" : tactic => `(tactic| simp_all [SrcpV3.constraints, ev,
  Dsl.mul3, Dsl.sub, Dsl.not, Dsl.c, Dsl.n, Dsl.k, Dsl.smul,
  frame, rootFrame, leafFrame, pathFrame, Frame.cell,
  SrcpV3.rt, SrcpV3.sg, SrcpV3.lf, SrcpV3.wf, SrcpV3.wl, SrcpV3.wn,
  SrcpV3.sf, SrcpV3.sl, SrcpV3.pw, Int.add_right_neg])

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- The executable successor respects root, window and segment flag transitions. -/
theorem window_step_polynomials (B : SrcpB) (z : Nat) (a b : Kind) (g g' : Bool)
    (hk : a ∈ kinds B) (hn : nextKind B a = some b)
    (P : Nat → Int) (fst lst trn : Int) (n : Nat) (hi : n ∈ windowStepIndices) :
    ev (fun x => (({ frame B z a with gz := g }).cell x : Int))
      (fun x => (({ frame B z b with gz := g' }).cell x : Int)) fst lst trn P
      (SrcpV3.constraints.getD n (.const 0)) = 0 := by
  have hv := (mem_kinds B a).mp hk
  have hc := indices_cases hi
  cases a with
  | root =>
    simp only [nextKind, Option.some.injEq] at hn
    subst b
    rcases hc with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc
    all_goals subst n; step_simp
  | leaf p =>
    have hp : p < 32 := by simpa using hv
    simp only [nextKind] at hn
    split at hn
    · cases hn
      have hp31 : p ≠ 31 := by omega
      have hp0 : p + 1 ≠ 0 := by omega
      rcases hc with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc
      all_goals subst n; step_simp
      all_goals omega
    · have hp31 : p = 31 := by omega
      subst p
      split at hn
      · cases hn
        rcases hc with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc
        all_goals subst n; step_simp
      · contradiction
  | path i o =>
    have ho : o < 64 := (show i < B.path.length ∧ o < 64 by simpa using hv).2
    simp only [nextKind] at hn
    split at hn
    · cases hn
      have ho63 : o ≠ 63 := by omega
      by_cases hw : o % 32 = 31
      · have ho31 : o = 31 := by omega
        subst o
        rcases hc with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc
        all_goals subst n; step_simp
      · have hpw : (o + 1) % 32 = o % 32 + 1 := by omega
        have hfw : (o + 1) % 32 ≠ 0 := by omega
        have hsf : o + 1 ≠ 0 := by omega
        have hwn : (32 ≤ o + 1) = (32 ≤ o) := propext (by omega)
        have h31 : (31 ≤ o) = (32 ≤ o) := propext (by omega)
        by_cases hw32 : 32 ≤ o
        all_goals rcases hc with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc
        all_goals subst n; step_simp
        all_goals by_cases h31' : 31 ≤ o
        all_goals by_cases h32' : 32 ≤ o
        all_goals simp_all
        all_goals
          have h31none : ¬ 31 ≤ o := by omega
          have h32none : ¬ 32 ≤ o := by omega
          simp [h31none, h32none]
        all_goals omega
    · have ho63 : o = 63 := by omega
      subst o
      split at hn
      · cases hn
        rcases hc with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc
        all_goals subst n; step_simp
      · contradiction

end ZkFormal.NearV3.Render.SrcpGen
