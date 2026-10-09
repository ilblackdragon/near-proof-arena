import ZkFormal.NearV3.Rcpt.Candidates.DedupTrafficComplete
import ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable
import ZkFormal.Near.Extract.Eval

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable
open DedupRender ZkFormal.Near ZkFormal.Near.Render ZkFormal.Air ZkFormal.Algebra Render.SrcpGen

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
theorem base_mult_bits {bs : List SrcpB} {repeated : Nat → Bool}
    {tr : Trace Fp} {tt r pos : Nat} {pub : List Fp}
    (hc : ∀ x, tr.cell tt r x = Fp.ofNat (cell bs repeated pos x)) :
    ∀ i ∈ DedupTable.interactions, ∀ b ∈ i.mult,
      b.eval tr tt r pub = 0 ∨ b.eval tr tt r pub = 1 := by
  intro i hi b hb
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (gate_coverage i hi b hb)
  have hn := cell_bool_bound bs repeated pos x hx
  have hv : cell bs repeated pos x = 0 ∨ cell bs repeated pos x = 1 := by omega
  simp only [eval_c, hc x]
  rcases hv with hv | hv
  · rw [hv]; exact Or.inl rfl
  · rw [hv]; exact Or.inr rfl

/-- Left base traffic is suppressed exactly at the carry endpoint; the endpoint
carry itself has multiplicity one. All multiplicity digits remain bits. -/
theorem left_mult_bits {bs : List SrcpB} {repeated : Nat → Bool}
    {tr : Trace Fp} {tt r pos carryBus : Nat} {pub : List Fp}
    (hc : ∀ x, tr.cell tt r x = Fp.ofNat (cell bs repeated pos x)) :
    ∀ i ∈ leftInteractions carryBus, ∀ b ∈ i.mult,
      b.eval tr tt r pub = 0 ∨ b.eval tr tt r pub = 1 := by
  intro i hi b hb
  rcases List.mem_append.mp hi with hi | hi
  · obtain ⟨it, hit, rfl⟩ := List.mem_map.mp hi
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hb
    have he := base_mult_bits (pub := pub) hc it hit e he
    by_cases hl : r + 1 = tr.height tt
    · simp only [eval_mul, eval_not, eval_isLast, hl, ite_true]; grind
    · simp only [eval_mul, eval_not, eval_isLast, hl, ite_false]; grind only
  · have hi' : i = Dsl.send carryBus .isLast carryMessage := by simpa using hi
    subst i
    have hb' : b = .isLast := by simpa [Dsl.send] using hb
    subst b
    by_cases hl : r + 1 = tr.height tt <;> simp [eval_isLast, hl]

/-- The right partition emits the ordinary source traffic and receives one full
carry row at its first physical row. -/
theorem right_mult_bits {bs : List SrcpB} {repeated : Nat → Bool}
    {tr : Trace Fp} {tt r pos carryBus : Nat} {pub : List Fp}
    (hc : ∀ x, tr.cell tt r x = Fp.ofNat (cell bs repeated pos x)) :
    ∀ i ∈ rightInteractions carryBus, ∀ b ∈ i.mult,
      b.eval tr tt r pub = 0 ∨ b.eval tr tt r pub = 1 := by
  intro i hi b hb
  rcases List.mem_append.mp hi with hi | hi
  · exact base_mult_bits hc i hi b hb
  · have hi' : i = Dsl.recv carryBus .isFirst carryMessage := by simpa using hi
    subst i
    have hb' : b = .isFirst := by simpa [Dsl.recv] using hb
    subst b
    by_cases hf : r = 0 <;> simp [eval_isFirst, hf]

end ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable
