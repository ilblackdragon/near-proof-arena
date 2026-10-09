import ZkFormal.NearV3.Rcpt.Render.Srcp.Accumulator

namespace ZkFormal.NearV3.Render.SrcpGen
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra

def boolCols : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 14, 15, 16, 21, 55]

theorem Frame.bool_bound (C : Frame) (x : Nat) (hx : x ∈ boolCols) : C.cell x ≤ 1 := by
  have hb (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide
  simp only [boolCols, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst x; exact hb _

theorem cell_bool_bound (bs : List SrcpB) (r x : Nat) (hx : x ∈ boolCols) :
    cell bs r x ≤ 1 := by
  unfold cell
  split
  · exact Frame.bool_bound _ x hx
  · have hn : x ≠ SrcpV3.sz := by
      intro he
      subst x
      exact (by decide : ¬ SrcpV3.sz ∈ boolCols) hx
    simp [hn]

/-- All thirteen Boolean constraints hold on every rendered row, including padding. -/
theorem bool_constraints {bs : List SrcpB} {tr : Trace Fp} {tt r : Nat} {pub : List Fp}
    (hc : ∀ x, x ∈ boolCols → tr.cell tt r x = Fp.ofNat (cell bs r x)) :
    ∀ ex ∈ SrcpV3.constraints.take 13, ex.eval tr tt r pub = 0 := by
  have he : SrcpV3.constraints.take 13 = boolCols.map (fun x => Dsl.bool (Dsl.c x)) := rfl
  rw [he]
  intro ex hex
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hex
  have hb := cell_bool_bound bs r x hx
  have hv : cell bs r x = 0 ∨ cell bs r x = 1 := by omega
  simp only [Dsl.bool, Dsl.c, Dsl.sub, Dsl.k, Expr.eval, Expr.evalWith, rowEnv, Bool.false_eq_true, ite_false]
  rw [hc x hx]
  rcases hv with hv | hv <;> rw [hv] <;> decide

end ZkFormal.NearV3.Render.SrcpGen
