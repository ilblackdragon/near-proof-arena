import ZkFormal.NearV3.Rcpt.Render.Srcp.CounterFacts

namespace ZkFormal.NearV3.Render.SrcpGen
open ZkFormal.Near ZkFormal.Near.Render.EvI ZkFormal.Air

def counterIndices : List Nat := [22, 44, 45, 46, 47, 48, 49]

macro "counter_simp" : tactic => `(tactic| simp_all [SrcpV3.constraints, ev,
  Dsl.mul3, Dsl.sub, Dsl.not, Dsl.c, Dsl.n, Dsl.k, Dsl.smul,
  frame, rootFrame, leafFrame, pathFrame, Frame.cell,
  SrcpV3.rt, SrcpV3.sg, SrcpV3.lf, SrcpV3.sl, SrcpV3.q, SrcpV3.pl,
  SrcpV3.j, SrcpV3.qe, SrcpV3.le, Int.add_right_neg])

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
/-- Internal root/segment transitions advance source counters and predecessor lengths. -/
theorem counter_step_polynomials (B : SrcpB) (h : CounterFacts B) (z : Nat)
    (a b : Kind) (g g' : Bool) (hk : a ∈ kinds B) (hn : nextKind B a = some b)
    (P : Nat → Int) (fst lst trn : Int) (n : Nat) (hi : n ∈ counterIndices) :
    ev (fun x => (({ frame B z a with gz := g }).cell x : Int))
      (fun x => (({ frame B z b with gz := g' }).cell x : Int)) fst lst trn P
      (SrcpV3.constraints.getD n (.const 0)) = 0 := by
  have hv := (mem_kinds B a).mp hk
  have hqpos := h.qpos
  simp only [counterIndices, List.mem_cons, List.not_mem_nil, or_false] at hi
  cases a with
  | root =>
    simp only [nextKind, Option.some.injEq] at hn
    subst b
    rcases hi with hi | hi | hi | hi | hi | hi | hi
    all_goals subst n; counter_simp
    all_goals omega
  | leaf p =>
    have hp : p < 32 := by simpa using hv
    simp only [nextKind] at hn
    split at hn
    · cases hn
      have hp31 : p ≠ 31 := by omega
      rcases hi with hi | hi | hi | hi | hi | hi | hi
      all_goals subst n; counter_simp
    · have hp31 : p = 31 := by omega
      subst p
      split at hn
      · rename_i hlen
        cases hn
        have hq0 := h.item_q 0 hlen
        have hp0 := h.item_pl 0 hlen
        have he : B.path[0]?.getD default = B.path[0] := by simp [List.getElem?_eq_getElem hlen]
        rcases hi with hi | hi | hi | hi | hi | hi | hi
        all_goals subst n; counter_simp
        all_goals omega
      · contradiction
  | path i o =>
    have hv' : i < B.path.length ∧ o < 64 := by simpa using hv
    simp only [nextKind] at hn
    split at hn
    · cases hn
      have ho63 : o ≠ 63 := by omega
      rcases hi with hi | hi | hi | hi | hi | hi | hi
      all_goals subst n; counter_simp
    · have ho63 : o = 63 := by omega
      subst o
      split at hn
      · rename_i hlen
        cases hn
        have hqi := h.item_q i hv'.1
        have hqn := h.item_q (i + 1) hlen
        have hpn := h.item_pl (i + 1) hlen
        have hei : B.path[i]?.getD default = B.path[i] := by simp [List.getElem?_eq_getElem hv'.1]
        have hen : B.path[i + 1]?.getD default = B.path[i + 1] := by simp [List.getElem?_eq_getElem hlen]
        rcases hi with hi | hi | hi | hi | hi | hi | hi
        all_goals subst n; counter_simp
        all_goals omega
      · contradiction

end ZkFormal.NearV3.Render.SrcpGen
