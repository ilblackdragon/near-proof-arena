import ZkFormal.NearV3.Rcpt.Candidates.SourceVariableTrace

namespace ZkFormal.NearV3.Rcpt.Candidates.SourceLog22
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra DedupPartitionTable

theorem variable_bits {tr : Trace Fp} {a b c d : Nat} {pub : List Fp}
    (ha : TableLocal (SizeCount.sourceTable firstTable) tr a pub)
    (hb : TableLocal (SizeCount.sourceTable (middleTable 64 65)) tr b pub)
    (hc : TableLocal (SizeCount.sourceTable (middleTable 65 66)) tr c pub)
    (hd : TableLocal (SizeCount.sourceTable lastTable) tr d pub)
 :
    ∀ r, r<(variableTrace tr a b c d).height 0 →
      ∀ i∈DedupTable.interactions, ∀ e∈i.mult,
        e.eval (variableTrace tr a b c d) 0 r pub=0 ∨ e.eval (variableTrace tr a b c d) 0 r pub=1 := by
  have ha0 := SizeCount.source_local_base ha
  have hb0 := SizeCount.source_local_base hb
  have hc0 := SizeCount.source_local_base hc
  have hd0 := SizeCount.source_local_base hd
  have hp : 0<tr.height a := Nat.two_pow_pos _
  intro r _ i hi e he
  let sa := tr.height a-1
  let sb := tr.height b-1
  let sc := tr.height c-1
  let sd := tr.height d-1
  let u := min r (sa+sb+sc+sd)
  have hu : u≤sa+sb+sc+sd := Nat.min_le_right _ _
  have hpB : 0<tr.height b := Nat.two_pow_pos _
  have hpC : 0<tr.height c := Nat.two_pow_pos _
  have hpD : 0<tr.height d := Nat.two_pow_pos _
  by_cases h0 : u<sa
  · rw [base_mult_current (tr':=tr) (t':=a) (r':=u) (fun x => by
      change prefixCells sa (tr.cell a) (prefixCells sb (tr.cell b) (prefixCells sc (tr.cell c) (tr.cell d))) u x=tr.cell a u x
      simp [prefixCells,h0]) i hi e he]
    exact base_bits_of_left (by dsimp [sa,sb,sc,sd] at h0; omega) (ha0.bits u (by dsimp [sa,sb,sc,sd] at h0; omega)) i hi e he
  · by_cases h1 : u-sa<sb
    · rw [base_mult_current (tr':=tr) (t':=b) (r':=u-sa) (fun x => by
        change prefixCells sa (tr.cell a) (prefixCells sb (tr.cell b) (prefixCells sc (tr.cell c) (tr.cell d))) u x=tr.cell b (u-sa) x
        simp [prefixCells,h0,h1]) i hi e he]
      apply base_bits_of_left (carryBus:=65) (by dsimp [sa,sb,sc,sd] at h1; omega) ?_ i hi e he
      intro j hj k hk
      exact hb0.bits _ (by dsimp [sa,sb,sc,sd] at h1; omega) j (List.mem_append_left _ hj) k hk
    · by_cases h2 : u-sa-sb<sc
      · rw [base_mult_current (tr':=tr) (t':=c) (r':=u-sa-sb) (fun x => by
          change prefixCells sa (tr.cell a) (prefixCells sb (tr.cell b) (prefixCells sc (tr.cell c) (tr.cell d))) u x=tr.cell c (u-sa-sb) x
          simp [prefixCells,h0,h1,h2]) i hi e he]
        apply base_bits_of_left (carryBus:=66) (by dsimp [sa,sb,sc,sd] at h2; omega) ?_ i hi e he
        intro j hj k hk
        exact hc0.bits _ (by dsimp [sa,sb,sc,sd] at h2; omega) j (List.mem_append_left _ hj) k hk
      · rw [base_mult_current (tr':=tr) (t':=d) (r':=u-sa-sb-sc) (fun x => by
          change prefixCells sa (tr.cell a) (prefixCells sb (tr.cell b) (prefixCells sc (tr.cell c) (tr.cell d))) u x=tr.cell d (u-sa-sb-sc) x
          simp [prefixCells,h0,h1,h2]) i hi e he]
        exact hd0.bits _ (by dsimp [sa,sb,sc,sd] at *; omega) i (List.mem_append_left _ hi) e he

/-- The log24 trace is an extraction device only; all four submitted physical
tables remain log22. No protocol height limit is raised by this theorem. -/
theorem variable_local {tr : Trace Fp} {a b c d : Nat} {pub : List Fp}
    (ha : TableLocal (SizeCount.sourceTable firstTable) tr a pub)
    (hb : TableLocal (SizeCount.sourceTable (middleTable 64 65)) tr b pub)
    (hc : TableLocal (SizeCount.sourceTable (middleTable 65 66)) tr c pub)
    (hd : TableLocal (SizeCount.sourceTable lastTable) tr d pub)

    (hab : ∀ x, x<57 → tr.cell a (tr.height a-1) x=tr.cell b 0 x)
    (hbc : ∀ x, x<57 → tr.cell b (tr.height b-1) x=tr.cell c 0 x)
    (hcd : ∀ x, x<57 → tr.cell c (tr.height c-1) x=tr.cell d 0 x) :
    TableLocal (DedupTable.table 24) (variableTrace tr a b c d) 0 pub := by
  refine ⟨?_,?_,variable_constraints ha hb hc hd hab hbc hcd,
    variable_bits ha hb hc hd⟩
  · change 1≤24; decide
  · change 24≤24; decide

/-- The same reconstructed accepting trace yields one nonempty semantic source
sequence within the fixed logical extraction height, with arbitrary physical heights. -/
theorem variable_blocks {tr : Trace Fp} {a b c d : Nat} {pub : List Fp}
    (ha : TableLocal (SizeCount.sourceTable firstTable) tr a pub)
    (hb : TableLocal (SizeCount.sourceTable (middleTable 64 65)) tr b pub)
    (hc : TableLocal (SizeCount.sourceTable (middleTable 65 66)) tr c pub)
    (hd : TableLocal (SizeCount.sourceTable lastTable) tr d pub)

    (hab : ∀ x, x<57 → tr.cell a (tr.height a-1) x=tr.cell b 0 x)
    (hbc : ∀ x, x<57 → tr.cell b (tr.height b-1) x=tr.cell c 0 x)
    (hcd : ∀ x, x<57 → tr.cell c (tr.height c-1) x=tr.cell d 0 x) :
    ∃ bs stop,
      TableLocal (DedupTable.table 24) (variableTrace tr a b c d) 0 pub ∧
      DedupProof.BlockChain (variableTrace tr a b c d) 0 0 bs stop ∧
      bs≠[] ∧ DedupRender.R bs≤2^24 := by
  have hlocal := variable_local ha hb hc hd hab hbc hcd
  obtain ⟨bs,stop,hbs⟩ := DedupProof.extract_blocks hlocal
  refine ⟨bs,stop,hlocal,hbs,hbs.nonempty,?_⟩
  have hr := hbs.rows
  have hb := hbs.bound
  rw [variable_height] at hb
  omega

end ZkFormal.NearV3.Rcpt.Candidates.SourceLog22
