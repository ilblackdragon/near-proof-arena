import ZkFormal.NearV3.Rcpt.Render.Srcp.RowCounter
import ZkFormal.NearV3.Rcpt.Render.Srcp.RowSize

namespace ZkFormal.NearV3.Render.SrcpGen
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Air ZkFormal.Algebra

private def atIndex (n : Nat) : Expr := SrcpV3.constraints.getD n (.const 0)

private def covered : List Expr :=
  SrcpV3.constraints.take 13 ++ shapeIndices.map atIndex ++ firstIndices.map atIndex ++
  lastIndices.map atIndex ++ endIndices.map atIndex ++ [atIndex 23] ++ [atIndex 52] ++
  windowStepIndices.map atIndex ++ counterIndices.map atIndex ++ [57, 58].map atIndex ++
  digestIndices.map atIndex ++ (SrcpV3.constraints.drop 65).take 12 ++
  (SrcpV3.constraints.drop 77).take 4 ++ SrcpV3.constraints.drop 81

set_option maxRecDepth 8192 in
private theorem coverage : ∀ ex ∈ SrcpV3.constraints, ex ∈ covered := by
  have hh : SrcpV3.constraints.all (fun ex => covered.any (fun e => decide (ex = e))) = true := by decide +kernel
  intro ex hex
  obtain ⟨e, he, heq⟩ := List.any_eq_true.mp (List.all_eq_true.mp hh ex hex)
  exact (of_decide_eq_true heq).symm ▸ he

/-- Every actual source-table constraint holds on the honest row generator. -/
theorem constraints {bs : List SrcpB} (h : SrcpWf bs) {tr : Trace Fp}
    {tt r : Nat} {pub : List Fp} (hH : R bs ≤ tr.height tt) (hr : r < tr.height tt)
    (hc : ∀ x, tr.cell tt r x = Fp.ofNat (cell bs r x))
    (hd : ∀ x, tr.cell tt ((r + 1) % tr.height tt) x =
      Fp.ofNat (cell bs ((r + 1) % tr.height tt) x)) :
    ∀ ex ∈ SrcpV3.constraints, ex.eval tr tt r pub = 0 := by
  have mapped (is : List Nat)
      (hh : ∀ n ∈ is, (SrcpV3.constraints.getD n (.const 0)).eval tr tt r pub = 0) :
      ∀ ex ∈ is.map atIndex, ex.eval tr tt r pub = 0 := by
    intro ex hex
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hex
    exact hh n hn
  intro ex hex
  have hh := coverage ex hex
  simp only [covered, List.mem_append, or_assoc] at hh
  rcases hh with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
  · exact bool_constraints (fun x _ => hc x) ex h0
  · exact mapped _ (shape_constraints hc) ex h1
  · exact mapped _ (first_constraints h hc) ex h2
  · exact mapped _ (last_constraints h hH hr hc) ex h3
  · exact mapped _ (end_constraints h hr hc hd) ex h4
  · simp only [List.mem_singleton] at h5
    subst ex
    exact duplicate_constraint h hc
  · simp only [List.mem_singleton] at h6
    subst ex
    exact size_constraint h hr hc hd
  · exact mapped _ (window_constraints h hH hc hd) ex h7
  · exact mapped _ (counter_constraints h hH hc hd) ex h8
  · exact mapped _ (fun n hn => lookup_gate_constraints hc n (by simpa using hn)) ex h9
  · exact mapped _ (digest_constraints h hc) ex h10
  · exact list_carry_constraints h hH hc hd ex h11
  · exact segment_constraints h hH hc hd ex h12
  · exact register_constraints h hH hc hd ex h13

set_option maxRecDepth 8192 in
private theorem gate_coverage : ∀ i ∈ SrcpV3.interactions,
    ∀ b ∈ i.mult, b ∈ boolCols.map Dsl.c := by
  have hh : SrcpV3.interactions.all (fun i => i.mult.all (fun b => (boolCols.map Dsl.c).any (fun e => decide (b = e)))) = true := by decide +kernel
  intro i hi b hb
  obtain ⟨e, he, heq⟩ := List.any_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hh i hi) b hb)
  exact (of_decide_eq_true heq).symm ▸ he

theorem mult_bits {bs : List SrcpB} {tr : Trace Fp} {tt r : Nat} {pub : List Fp}
    (hc : ∀ x, tr.cell tt r x = Fp.ofNat (cell bs r x)) :
    ∀ i ∈ SrcpV3.interactions, ∀ b ∈ i.mult,
      b.eval tr tt r pub = 0 ∨ b.eval tr tt r pub = 1 := by
  intro i hi b hb
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (gate_coverage i hi b hb)
  have hn := cell_bool_bound bs r x hx
  have hv : cell bs r x = 0 ∨ cell bs r x = 1 := by omega
  simp only [eval_c, hc x]
  rcases hv with hv | hv
  · rw [hv]; exact Or.inl rfl
  · rw [hv]; exact Or.inr rfl

/-- Closed honest source-table local legality, at the original semantic row cap. -/
theorem table_local {bs : List SrcpB} (h : SrcpWf bs) {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hlog : tr.log tt = logOf (R bs))
    (hc : ∀ r, r < tr.height tt → ∀ x, tr.cell tt r x = Fp.ofNat (cell bs r x)) :
    TableLocal SrcpV3.table tr tt pub := by
  have hH : R bs ≤ tr.height tt := by
    simpa [Trace.height, hlog] using le_pow_logOf (R bs)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hlog]
    exact one_le_logOf _
  · simpa [SrcpV3.table, hlog] using rows_log_bound h
  · intro r hr ex hex
    have hn : (r + 1) % tr.height tt < tr.height tt := Nat.mod_lt _ (by omega)
    exact constraints h hH hr (hc r hr) (hc _ hn) ex hex
  · intro r hr
    exact mult_bits (hc r hr)

end ZkFormal.NearV3.Render.SrcpGen
