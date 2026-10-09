import ZkFormal.NearV3.Rcpt.Render.Srcp.CounterStep

namespace ZkFormal.NearV3.Render.SrcpGen
open ZkFormal.Near ZkFormal.Near.Render.EvI ZkFormal.Air

theorem frame_j (B : SrcpB) (z : Nat) (k : Kind) : (frame B z k).j = B.j := by
  cases k <;> rfl

theorem frame_qe (B : SrcpB) (z : Nat) (k : Kind) : (frame B z k).qe = B.qe := by
  cases k <;> rfl

theorem terminal_length_int (B : SrcpB) (h : CounterFacts B) (z : Nat) :
    ((frame B z (lastKind B)).le : Int) =
      64 - 32 * ((frame B z (lastKind B)).lf.toNat : Int) := by
  cases hp : B.path with
  | nil => simp [lastKind, hp, frame, leafFrame, h.le]
  | cons a xs => simp [lastKind, hp, frame, pathFrame, h.le]

set_option maxRecDepth 4096 in
/-- At a list end, root equality and cross-list counters finish the numeric equations. -/
theorem counter_end_polynomials (B : SrcpB) (h : CounterFacts B) (z : Nat) (g : Bool)
    (D P : Nat → Int) (fst lst trn : Int) (hSg : D SrcpV3.sg = 0)
    (hQ : trn * D SrcpV3.rt * (D SrcpV3.q - (B.lastQ : Int)) = 0)
    (hJ : trn * D SrcpV3.rt * (D SrcpV3.j - ((B.j : Int) + 1)) = 0)
    (n : Nat) (hi : n ∈ counterIndices) :
    ev (fun x => (({ frame B z (lastKind B) with gz := g }).cell x : Int))
      D fst lst trn P (SrcpV3.constraints.getD n (.const 0)) = 0 := by
  have hlen := terminal_length_int B h z
  simp only [SrcpV3.sg] at hSg
  simp only [Int.sub_eq_add_neg, Int.mul_assoc] at hQ hJ
  simp only [counterIndices, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with hi | hi | hi | hi | hi | hi | hi
  all_goals subst n
  all_goals simp [SrcpV3.constraints, ev, Dsl.mul3, Dsl.sub, Dsl.not, Dsl.c, Dsl.n,
    Dsl.k, Dsl.smul, Frame.cell, SrcpV3.rt, SrcpV3.sg, SrcpV3.sl, SrcpV3.q,
    SrcpV3.j, SrcpV3.qe, SrcpV3.le, SrcpV3.lf, SrcpV3.pl,
    terminal_rt, terminal_sl, terminal_q B h, frame_j, frame_qe,
    h.qe, hSg, Int.mul_assoc, Int.add_right_neg]
  all_goals first | exact hQ | exact hJ | omega

end ZkFormal.NearV3.Render.SrcpGen
