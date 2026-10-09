import ZkFormal.NearV3.Rcpt.Candidates.SourceLog22Trace

namespace ZkFormal.NearV3.Rcpt.Candidates.SourceLog22
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra DedupPartitionTable

theorem joined4_bits {tr : Trace Fp} {a b c d : Nat} {pub : List Fp}
    (ha : TableLocal (SizeCount.sourceTable firstTable) tr a pub)
    (hb : TableLocal (SizeCount.sourceTable (middleTable 64 65)) tr b pub)
    (hc : TableLocal (SizeCount.sourceTable (middleTable 65 66)) tr c pub)
    (hd : TableLocal (SizeCount.sourceTable lastTable) tr d pub)
    (hhb : tr.height b=tr.height a) (hhc : tr.height c=tr.height a) (hhd : tr.height d=tr.height a) :
    ∀ r, r<(joined4Trace tr a b c d).height 0 →
      ∀ i∈DedupTable.interactions, ∀ e∈i.mult,
        e.eval (joined4Trace tr a b c d) 0 r pub=0 ∨ e.eval (joined4Trace tr a b c d) 0 r pub=1 := by
  have ha0 := SizeCount.source_local_base ha
  have hb0 := SizeCount.source_local_base hb
  have hc0 := SizeCount.source_local_base hc
  have hd0 := SizeCount.source_local_base hd
  have hp : 0<tr.height a := Nat.two_pow_pos _
  intro r _ i hi e he
  let s := tr.height a-1
  let u := min r (4*s)
  have hu : u≤4*s := Nat.min_le_right _ _
  by_cases h0 : u<s
  · rw [base_mult_current (tr':=tr) (t':=a) (r':=u) (fun x => by
      change prefixCells s (tr.cell a) (prefixCells s (tr.cell b) (prefixCells s (tr.cell c) (tr.cell d))) u x=tr.cell a u x
      simp [prefixCells,h0]) i hi e he]
    exact base_bits_of_left (by dsimp [s] at h0; omega) (ha0.bits u (by dsimp [s] at h0; omega)) i hi e he
  · by_cases h1 : u-s<s
    · rw [base_mult_current (tr':=tr) (t':=b) (r':=u-s) (fun x => by
        change prefixCells s (tr.cell a) (prefixCells s (tr.cell b) (prefixCells s (tr.cell c) (tr.cell d))) u x=tr.cell b (u-s) x
        simp [prefixCells,h0,h1]) i hi e he]
      apply base_bits_of_left (carryBus:=65) (by dsimp [s] at h1; omega) ?_ i hi e he
      intro j hj k hk
      exact hb0.bits _ (by dsimp [s] at h1; omega) j (List.mem_append_left _ hj) k hk
    · by_cases h2 : u-s-s<s
      · rw [base_mult_current (tr':=tr) (t':=c) (r':=u-s-s) (fun x => by
          change prefixCells s (tr.cell a) (prefixCells s (tr.cell b) (prefixCells s (tr.cell c) (tr.cell d))) u x=tr.cell c (u-s-s) x
          simp [prefixCells,h0,h1,h2]) i hi e he]
        apply base_bits_of_left (carryBus:=66) (by dsimp [s] at h2; omega) ?_ i hi e he
        intro j hj k hk
        exact hc0.bits _ (by dsimp [s] at h2; omega) j (List.mem_append_left _ hj) k hk
      · rw [base_mult_current (tr':=tr) (t':=d) (r':=u-s-s-s) (fun x => by
          change prefixCells s (tr.cell a) (prefixCells s (tr.cell b) (prefixCells s (tr.cell c) (tr.cell d))) u x=tr.cell d (u-s-s-s) x
          simp [prefixCells,h0,h1,h2]) i hi e he]
        exact hd0.bits _ (by dsimp [s] at *; omega) i (List.mem_append_left _ hi) e he

/-- The log24 trace is an extraction device only; all four submitted physical
tables remain log22. No protocol height limit is raised by this theorem. -/
theorem joined4_local {tr : Trace Fp} {a b c d : Nat} {pub : List Fp}
    (ha : TableLocal (SizeCount.sourceTable firstTable) tr a pub)
    (hb : TableLocal (SizeCount.sourceTable (middleTable 64 65)) tr b pub)
    (hc : TableLocal (SizeCount.sourceTable (middleTable 65 66)) tr c pub)
    (hd : TableLocal (SizeCount.sourceTable lastTable) tr d pub)
    (hhb : tr.height b=tr.height a) (hhc : tr.height c=tr.height a) (hhd : tr.height d=tr.height a)
    (hab : ∀ x, x<57 → tr.cell a (tr.height a-1) x=tr.cell b 0 x)
    (hbc : ∀ x, x<57 → tr.cell b (tr.height a-1) x=tr.cell c 0 x)
    (hcd : ∀ x, x<57 → tr.cell c (tr.height a-1) x=tr.cell d 0 x) :
    TableLocal (DedupTable.table 24) (joined4Trace tr a b c d) 0 pub := by
  refine ⟨?_,?_,joined4_constraints ha hb hc hd hhb hhc hhd hab hbc hcd,
    joined4_bits ha hb hc hd hhb hhc hhd⟩
  · change 1≤tr.log a+2; omega
  · have hl : tr.log a≤22 := ha.log_le
    change tr.log a+2≤24
    omega

/-- The same reconstructed accepting trace yields one nonempty semantic source
sequence bounded by the sum of the four physical heights. -/
theorem joined4_blocks {tr : Trace Fp} {a b c d : Nat} {pub : List Fp}
    (ha : TableLocal (SizeCount.sourceTable firstTable) tr a pub)
    (hb : TableLocal (SizeCount.sourceTable (middleTable 64 65)) tr b pub)
    (hc : TableLocal (SizeCount.sourceTable (middleTable 65 66)) tr c pub)
    (hd : TableLocal (SizeCount.sourceTable lastTable) tr d pub)
    (hhb : tr.height b=tr.height a) (hhc : tr.height c=tr.height a) (hhd : tr.height d=tr.height a)
    (hab : ∀ x, x<57 → tr.cell a (tr.height a-1) x=tr.cell b 0 x)
    (hbc : ∀ x, x<57 → tr.cell b (tr.height a-1) x=tr.cell c 0 x)
    (hcd : ∀ x, x<57 → tr.cell c (tr.height a-1) x=tr.cell d 0 x) :
    ∃ bs stop,
      TableLocal (DedupTable.table 24) (joined4Trace tr a b c d) 0 pub ∧
      DedupProof.BlockChain (joined4Trace tr a b c d) 0 0 bs stop ∧
      bs≠[] ∧ DedupRender.R bs≤4*tr.height a := by
  have hlocal := joined4_local ha hb hc hd hhb hhc hhd hab hbc hcd
  obtain ⟨bs,stop,hbs⟩ := DedupProof.extract_blocks hlocal
  refine ⟨bs,stop,hlocal,hbs,hbs.nonempty,?_⟩
  have hr := hbs.rows
  have hb := hbs.bound
  rw [joined4_height] at hb
  omega

end ZkFormal.NearV3.Rcpt.Candidates.SourceLog22
