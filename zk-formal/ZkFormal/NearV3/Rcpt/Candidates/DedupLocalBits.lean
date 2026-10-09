import ZkFormal.NearV3.Rcpt.Candidates.DedupTrafficComplete
import ZkFormal.NearV3.Rcpt.Candidates.DedupTable
import ZkFormal.Near.Extract.Eval

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupRender
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Air ZkFormal.Algebra Render.SrcpGen

set_option maxRecDepth 8192 in
private theorem gate_coverage : ∀ i ∈ DedupTable.interactions,
    ∀ b ∈ i.mult, b ∈ boolCols.map Dsl.c := by
  have hh : DedupTable.interactions.all
      (fun i => i.mult.all (fun b => (boolCols.map Dsl.c).any (fun e => decide (b = e)))) = true := by
    decide +kernel
  intro i hi b hb
  obtain ⟨e, he, heq⟩ := List.any_eq_true.mp
    (List.all_eq_true.mp (List.all_eq_true.mp hh i hi) b hb)
  exact (of_decide_eq_true heq).symm ▸ he

/-- All five candidate bus multiplicities are bits on every actual rendered row,
including skipped headers and padding, at arbitrary table height. -/
theorem mult_bits {bs : List SrcpB} {repeated : Nat → Bool}
    {tr : Trace Fp} {tt r : Nat} {pub : List Fp}
    (hc : ∀ x, tr.cell tt r x = Fp.ofNat (cell bs repeated r x)) :
    ∀ i ∈ DedupTable.interactions, ∀ b ∈ i.mult,
      b.eval tr tt r pub = 0 ∨ b.eval tr tt r pub = 1 := by
  intro i hi b hb
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (gate_coverage i hi b hb)
  have hn := cell_bool_bound bs repeated r x hx
  have hv : cell bs repeated r x = 0 ∨ cell bs repeated r x = 1 := by omega
  simp only [eval_c, hc x]
  rcases hv with hv | hv
  · rw [hv]; exact Or.inl rfl
  · rw [hv]; exact Or.inr rfl

end ZkFormal.NearV3.Rcpt.Candidates.DedupRender
