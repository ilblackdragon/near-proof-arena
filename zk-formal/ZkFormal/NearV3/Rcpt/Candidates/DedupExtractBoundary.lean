import ZkFormal.NearV3.Rcpt.Candidates.DedupUnitDecomposition

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl SrcpV3

variable {tr : Trace Fp} {pub : List Fp} {tt cap : Nat}
variable (hL : TableLocal (DedupTable.table cap) tr tt pub)
include hL

/-- After a computed source's last segment, the next root advances only j. -/
theorem afterSegRt {r : Nat} (hr : r+1<tr.height tt) (hl : tr.cell tt r sl=1)
    (ha : tr.cell tt (r+1) rt=1) :
    tr.cell tt (r+1) q=tr.cell tt r q ∧ tr.cell tt (r+1) j=tr.cell tt r j+1 := by
  have hr' : r<tr.height tt := by omega
  have h1 := con hL hr' (.mul .isTransition (mul3 (c sl) (n rt) (sub (n q) (c q)))) (by decide +kernel)
  have h2 := con hL hr' (.mul .isTransition (mul3 (c sl) (n rt) (sub (n j) (.add (c j) (k 1))))) (by decide +kernel)
  have hn : r+1≠tr.height tt := by omega
  simp only [eval_mul, eval_mul3, eval_c, eval_n, eval_sub, eval_add, eval_k,
    eval_isTransition, hn, ite_false, SrcpProof.nxt hr, hl, ha] at h1 h2
  exact ⟨by grind, by grind⟩

/-- A terminal SIZE gate forbids another active row. -/
theorem gz_next_inactive {r : Nat} (hr : r+1<tr.height tt) (hz : tr.cell tt r gz=1) :
    tr.cell tt (r+1) rt=0 ∧ tr.cell tt (r+1) sg=0 := by
  have hh := con hL (r := r) (by omega)
    (.mul .isTransition (.mul (c gz) (.add (n rt) (n sg)))) (by decide +kernel)
  have hn : r+1≠tr.height tt := by omega
  simp only [eval_mul, eval_c, eval_n, eval_add, eval_isTransition,
    hn, ite_false, SrcpProof.nxt hr, hz] at hh
  have hd := disjoint hL (r := r+1) hr
  rcases mul_eq_zero'.mp hd with h | h <;> grind

/-- A duplicate followed by active traffic cannot be terminal. -/
theorem duplicate_active_step {r : Nat} (hr : r+1<tr.height tt) (hd : tr.cell tt r dup=1)
    (hn : tr.cell tt (r+1) rt=1 ∨ tr.cell tt (r+1) sg=1) :
    tr.cell tt (r+1) rt=1 ∧ tr.cell tt (r+1) q=tr.cell tt r q ∧
    tr.cell tt (r+1) j=tr.cell tt r j+1 := by
  rcases isBool hL (r := r) (by omega) (x := gz) (by simp [SrcpProof.bools]) with hz | hz
  · exact duplicate_step hL hr hd hz
  · obtain ⟨h1, h2⟩ := gz_next_inactive hL hr hz
    rcases hn with hn | hn <;> simp_all

/-- End-of-computation digest metadata stays exact in the candidate table. -/
theorem listEnd {r : Nat} (hr : r<tr.height tt) (hl : tr.cell tt r sl=1)
    (hn : tr.cell tt ((r+1)%tr.height tt) sg=0) :
    tr.cell tt r q=tr.cell tt r qe ∧ tr.cell tt r le=64-32*tr.cell tt r lf := by
  have h1 := con hL hr (mul3 (c sl) (Dsl.not (n sg)) (sub (c q) (c qe))) (by decide +kernel)
  have h2 := con hL hr (mul3 (c sl) (Dsl.not (n sg)) (sub (c le) (sub (k 64) (smul 32 (c lf))))) (by decide +kernel)
  simp only [eval_mul3, eval_c, eval_n, eval_not, eval_sub, eval_k, eval_smul, hl, hn] at h1 h2
  exact ⟨by grind, by grind⟩

end ZkFormal.NearV3.Rcpt.Candidates.DedupProof
