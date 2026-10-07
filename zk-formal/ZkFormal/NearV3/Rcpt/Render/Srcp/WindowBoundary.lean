import ZkFormal.NearV3.Rcpt.Render.Srcp.WindowStep

namespace ZkFormal.NearV3.Render.SrcpGen
open ZkFormal.Near ZkFormal.Near.Render.EvI ZkFormal.Air

set_option maxRecDepth 4096 in
theorem window_boundary (C D P : Nat → Int) (fst lst trn : Int)
    (hRt : C SrcpV3.rt = 0) (hWl : C SrcpV3.wl = 1)
    (hSl : C SrcpV3.sl = 1) (hSg : D SrcpV3.sg = 0)
    (n : Nat) (hi : n ∈ windowStepIndices) :
    ev C D fst lst trn P (SrcpV3.constraints.getD n (.const 0)) = 0 := by
  simp only [windowStepIndices, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with hi | hi | hi | hi | hi | hi | hi | hi | hi | hi | hi | hi
  all_goals subst n
  all_goals simp [SrcpV3.constraints, ev, Dsl.mul3, Dsl.sub, Dsl.not, Dsl.c, Dsl.n,
    Dsl.k, hRt, hWl, hSl, hSg]

set_option maxRecDepth 4096 in
theorem window_padding (C D P : Nat → Int) (fst lst trn : Int)
    (hRt : C SrcpV3.rt = 0) (hSg : C SrcpV3.sg = 0)
    (hWl : C SrcpV3.wl = 0) (hSl : C SrcpV3.sl = 0)
    (n : Nat) (hi : n ∈ windowStepIndices) :
    ev C D fst lst trn P (SrcpV3.constraints.getD n (.const 0)) = 0 := by
  simp only [windowStepIndices, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with hi | hi | hi | hi | hi | hi | hi | hi | hi | hi | hi | hi
  all_goals subst n
  all_goals simp [SrcpV3.constraints, ev, Dsl.mul3, Dsl.sub, Dsl.not, Dsl.c, Dsl.n,
    Dsl.k, hRt, hWl, hSl, hSg]

theorem last_wl_cell {bs : List SrcpB} (h : SrcpWf bs) : cell bs (R bs - 1) SrcpV3.wl = 1 := by
  have hr : R bs - 1 < R bs := by have := R_pos h; omega
  simp only [cell, hr, ite_true, lastAt h, rowFrame]
  change ((frame _ _ (lastKind _)).wl).toNat = 1
  rw [terminal_wl]; rfl

/-- The successor of the last active row is padding or the first root after wraparound. -/
theorem last_next_sg {bs : List SrcpB} (h : SrcpWf bs) (H r : Nat)
    (hH : R bs ≤ H) (hr : r < R bs) (hn : ¬ r + 1 < R bs) :
    cell bs ((r + 1) % H) SrcpV3.sg = 0 := by
  by_cases hh : r + 1 = H
  · rw [hh, Nat.mod_self]
    exact first_sg h
  · have hm : (r + 1) % H = r + 1 := Nat.mod_eq_of_lt (by omega)
    rw [hm]
    simp [padding_cell (show R bs ≤ r + 1 by omega), SrcpV3.sg, SrcpV3.sz]

end ZkFormal.NearV3.Render.SrcpGen
