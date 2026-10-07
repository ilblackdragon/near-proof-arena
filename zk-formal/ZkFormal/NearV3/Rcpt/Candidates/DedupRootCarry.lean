import ZkFormal.NearV3.Rcpt.Candidates.DedupExtractCounters

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl SrcpV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal (DedupTable.table 24) tr tt pub)
include hL

/-- Computed roots cannot terminate the logical trace before their leaf. -/
theorem computed_root_not_last {r : Nat} (hr : r<tr.height tt)
    (ha : tr.cell tt r rt=1) (hd : tr.cell tt r dup=0) : r+1<tr.height tt := by
  by_cases hn : r+1<tr.height tt
  · exact hn
  · have he : r+1=tr.height tt := by omega
    have hh := con hL hr (.mul .isLast DedupTable.computedRoot) (by decide +kernel)
    simp only [eval_mul, eval_isLast, he, ite_true, DedupTable.computedRoot,
      eval_sub, eval_c, ha, hd] at hh
    exfalso; grind

/-- Computed roots preserve their public index, list length, and final digest
metadata into the leaf segment. -/
theorem computed_list_carry {r : Nat} (hr : r+1<tr.height tt)
    (ha : tr.cell tt r rt=1) (hd : tr.cell tt r dup=0) :
    ∀ x ∈ listConst, tr.cell tt (r+1) x=tr.cell tt r x := by
  intro x hx
  have hh := old_row_of_nodup hL (r := r) (by omega) hd
  have he := hh (.mul (c rt) (sub (n x) (c x))) (by
    unfold SrcpV3.constraints
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (List.mem_map_of_mem
      (f := fun x => Expr.mul (c rt) (sub (n x) (c x))) hx))))))
  simp only [eval_mul, eval_c, eval_n, eval_sub, SrcpProof.nxt hr, ha] at he
  grind

/-- Computed-root message counter increments are natural, without field wrap. -/
theorem root_q_succ {r : Nat} (hr : r+1<tr.height tt)
    (ha : tr.cell tt r rt=1) (hd : tr.cell tt r dup=0) :
    (tr.cell tt (r+1) q).toNat=(tr.cell tt r q).toNat+1 := by
  apply toNat_succ_of (computed_after_root hL hr ha hd).2.2.2
  have hb := (counter_bound hL (r := r) (by omega) (Or.inl ha)).1
  have hp := hP hL
  omega

/-- Path message counters also increment naturally. -/
theorem path_q_succ {r : Nat} (hr : r+1<tr.height tt) (hl : tr.cell tt r sl=1)
    (hs : tr.cell tt (r+1) sg=1) :
    (tr.cell tt (r+1) q).toNat=(tr.cell tt r q).toNat+1 := by
  apply toNat_succ_of (afterSegSg hL hr hl hs).2.2.1
  have ha := segment_last_active hL (r := r) (by omega) hl
  have hb := (counter_bound hL (r := r) (by omega) (Or.inr ha)).1
  have hp := hP hL
  omega

end ZkFormal.NearV3.Rcpt.Candidates.DedupProof
