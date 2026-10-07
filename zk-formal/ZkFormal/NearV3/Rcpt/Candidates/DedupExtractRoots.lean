import ZkFormal.NearV3.Rcpt.Candidates.DedupExtractRows

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

variable {tr : Trace Fp} {pub : List Fp} {tt cap : Nat}

/-- All-occurrence repetition metadata forces an empty encoded receipt list,
including the first computed occurrence. -/
theorem repeated_empty (hL : TableLocal (DedupTable.table cap) tr tt pub)
    {r : Nat} (hr : r<tr.height tt) (hp : tr.cell tt r DedupTable.repeated=1) :
    tr.cell tt r SrcpV3.rt=1 ∧ tr.cell tt r SrcpV3.L=12 := by
  have h1 := con hL hr (.mul (c DedupTable.repeated) (Dsl.not (c SrcpV3.rt))) (by decide +kernel)
  have h2 := con hL hr (mul3 (c SrcpV3.rt) (c DedupTable.repeated) (sub (c SrcpV3.L) (k 12)))
    (by decide +kernel)
  simp only [eval_mul, eval_mul3, eval_c, eval_not, eval_sub, eval_k, hp] at h1 h2
  exact ⟨by grind, by grind⟩

/-- A skipped root is a one-row empty source header with no digest request. -/
theorem duplicate_fields (hL : TableLocal (DedupTable.table cap) tr tt pub)
    {r : Nat} (hr : r<tr.height tt) (hd : tr.cell tt r SrcpV3.dup=1) :
    tr.cell tt r SrcpV3.rt=1 ∧ tr.cell tt r SrcpV3.sg=0 ∧
    tr.cell tt r DedupTable.repeated=1 ∧ tr.cell tt r SrcpV3.L=12 ∧
    tr.cell tt r SrcpV3.qe=tr.cell tt r SrcpV3.q ∧ tr.cell tt r SrcpV3.le=0 ∧
    tr.cell tt r SrcpV3.gD=0 := by
  have ha := duplicate_root hL hr hd
  have hs := disjoint hL hr
  have hp := con hL hr (.mul (c SrcpV3.dup) (Dsl.not (c DedupTable.repeated))) (by decide +kernel)
  have hq := con hL hr (.mul (c SrcpV3.dup) (sub (c SrcpV3.qe) (c SrcpV3.q))) (by decide +kernel)
  have he := con hL hr (.mul (c SrcpV3.dup) (c SrcpV3.le)) (by decide +kernel)
  have hw := con hL hr (.mul (c SrcpV3.wf) (Dsl.not (c SrcpV3.sg))) (by decide +kernel)
  have hg := con hL hr (sub (c SrcpV3.gD)
    (.add DedupTable.computedRoot (.mul (c SrcpV3.wf) (c SrcpV3.aw)))) (by decide +kernel)
  simp only [eval_mul, eval_c, eval_not, eval_sub, eval_add, DedupTable.computedRoot, hd, ha] at hp hq he hw hg
  rw [ha] at hs
  have hrep : tr.cell tt r DedupTable.repeated=1 := by grind
  have hempty := (repeated_empty hL hr hrep).2
  exact ⟨ha, by grind, hrep, hempty, by grind, by grind, by grind⟩

/-- Skipping a nonterminal duplicate consumes no SHA counter and advances exactly
one public source index. -/
theorem duplicate_step (hL : TableLocal (DedupTable.table cap) tr tt pub)
    {r : Nat} (hr : r+1<tr.height tt) (hd : tr.cell tt r SrcpV3.dup=1)
    (hz : tr.cell tt r SrcpV3.gz=0) :
    tr.cell tt (r+1) SrcpV3.rt=1 ∧
    tr.cell tt (r+1) SrcpV3.q=tr.cell tt r SrcpV3.q ∧
    tr.cell tt (r+1) SrcpV3.j=tr.cell tt r SrcpV3.j+1 := by
  have hr' : r<tr.height tt := by omega
  have h1 := con hL hr' (mul3 (c SrcpV3.dup) (Dsl.not (c SrcpV3.gz)) (Dsl.not (n SrcpV3.rt))) (by decide +kernel)
  have h2 := con hL hr' (.mul .isTransition
    (mul3 (c SrcpV3.dup) (n SrcpV3.rt) (sub (n SrcpV3.q) (c SrcpV3.q)))) (by decide +kernel)
  have h3 := con hL hr' (.mul .isTransition
    (mul3 (c SrcpV3.dup) (n SrcpV3.rt) (sub (n SrcpV3.j) (.add (c SrcpV3.j) (k 1))))) (by decide +kernel)
  have hn : r+1≠tr.height tt := by omega
  simp only [eval_mul, eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_k,
    eval_isTransition, hn, ite_false, Nat.mod_eq_of_lt hr, hd, hz] at h1 h2 h3
  exact ⟨by grind, by grind, by grind⟩

/-- Computed roots still begin exactly one ordinary leaf segment. -/
theorem computed_after_root (hL : TableLocal (DedupTable.table cap) tr tt pub)
    {r : Nat} (hr : r+1<tr.height tt) (ha : tr.cell tt r SrcpV3.rt=1)
    (hd : tr.cell tt r SrcpV3.dup=0) :
    tr.cell tt (r+1) SrcpV3.sg=1 ∧ tr.cell tt (r+1) SrcpV3.lf=1 ∧
    tr.cell tt (r+1) SrcpV3.sf=1 ∧ tr.cell tt (r+1) SrcpV3.q=tr.cell tt r SrcpV3.q+1 := by
  have hh := old_row_of_nodup hL (by omega) hd
  have h1 := hh (.mul (c SrcpV3.rt) (Dsl.not (n SrcpV3.sg))) (by simp [SrcpV3.constraints])
  have h2 := hh (.mul (c SrcpV3.rt) (Dsl.not (n SrcpV3.lf))) (by simp [SrcpV3.constraints])
  have h3 := hh (.mul (c SrcpV3.rt) (Dsl.not (n SrcpV3.sf))) (by simp [SrcpV3.constraints])
  have h4 := hh (.mul (c SrcpV3.rt) (sub (n SrcpV3.q) (.add (c SrcpV3.q) (k 1)))) (by simp [SrcpV3.constraints])
  simp only [eval_mul, eval_c, eval_n, eval_not, eval_sub, eval_add, eval_k,
    Nat.mod_eq_of_lt hr, ha] at h1 h2 h3 h4
  exact ⟨by grind, by grind, by grind, by grind⟩

end ZkFormal.NearV3.Rcpt.Candidates.DedupProof
