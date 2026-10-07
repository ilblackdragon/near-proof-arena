import ZkFormal.NearV3.Rcpt.Candidates.DedupTable
import ZkFormal.NearV3.Rcpt.Extract.Srcp.Rows

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

variable {tr : Trace Fp} {pub : List Fp} {tt cap : Nat}

theorem con (hL : TableLocal (DedupTable.table cap) tr tt pub)
    {r : Nat} (hr : r<tr.height tt) (e : Expr)
    (he : DedupTable.constraints.any (fun x => decide (e=x)) = true) : e.eval tr tt r pub=0 := by
  obtain ⟨x, hx, heq⟩ := List.any_eq_true.mp he
  exact (of_decide_eq_true heq).symm ▸ hL.constr r hr x hx

/-- All original flags and the public all-occurrence repetition flag are bits. -/
theorem isBool (hL : TableLocal (DedupTable.table cap) tr tt pub)
    {r x : Nat} (hr : r<tr.height tt) (hx : x ∈ SrcpProof.bools ++ [DedupTable.repeated]) :
    tr.cell tt r x=0 ∨ tr.cell tt r x=1 := by
  have hall : (SrcpProof.bools ++ [DedupTable.repeated]).all
      (fun x => DedupTable.constraints.any (fun e => decide (Dsl.bool (c x)=e))) = true := by
    decide +kernel
  have hh := con hL hr (Dsl.bool (c x)) (List.all_eq_true.mp hall x hx)
  simp only [eval_bool, eval_c] at hh
  exact bool_cases hh

/-- Skipping is possible only on a root row. -/
theorem duplicate_root (hL : TableLocal (DedupTable.table cap) tr tt pub)
    {r : Nat} (hr : r<tr.height tt) (hd : tr.cell tt r SrcpV3.dup=1) :
    tr.cell tt r SrcpV3.rt=1 := by
  have hh := con hL hr (.mul (c SrcpV3.dup) (Dsl.not (c SrcpV3.rt))) (by decide +kernel)
  simp only [eval_mul, eval_c, eval_not, hd] at hh
  grind

theorem rootless_nodup (hL : TableLocal (DedupTable.table cap) tr tt pub)
    {r : Nat} (hr : r<tr.height tt) (ha : tr.cell tt r SrcpV3.rt=0) :
    tr.cell tt r SrcpV3.dup=0 := by
  have hh := con hL hr (.mul (c SrcpV3.dup) (Dsl.not (c SrcpV3.rt))) (by decide +kernel)
  simp only [eval_mul, eval_c, eval_not, ha] at hh
  grind

theorem disjoint (hL : TableLocal (DedupTable.table cap) tr tt pub)
    {r : Nat} (hr : r<tr.height tt) :
    tr.cell tt r SrcpV3.rt * tr.cell tt r SrcpV3.sg=0 := by
  exact con hL hr (.mul (c SrcpV3.rt) (c SrcpV3.sg)) (by decide +kernel)

/-- Every segment row remains an ordinary source row. -/
theorem segment_nodup (hL : TableLocal (DedupTable.table cap) tr tt pub)
    {r : Nat} (hr : r<tr.height tt) (hs : tr.cell tt r SrcpV3.sg=1) :
    tr.cell tt r SrcpV3.dup=0 := by
  have hh := disjoint hL hr
  rw [hs] at hh
  exact rootless_nodup hL hr (by grind)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem patched_values_nodup {r : Nat} (hd : tr.cell tt r SrcpV3.dup=0) :
    (SrcpV3.constraints.mapIdx DedupTable.patch).map (fun e => e.eval tr tt r pub) =
      SrcpV3.constraints.map (fun e => e.eval tr tt r pub) := by
  simp [List.range_succ, List.map_map, Function.comp_def, SrcpV3.constraints, SrcpV3.listConst, SrcpV3.segConst, DedupTable.patch,
    DedupTable.computedRoot, DedupTable.endRow, SrcpV3.actE,
    eval_mul, eval_mul3, eval_c, eval_sub, eval_add, eval_not, hd,
    Lean.Grind.Ring.sub_eq_add_neg, Lean.Grind.Semiring.add_zero,
    Lean.Grind.AddCommMonoid.zero_add, Lean.Grind.AddCommGroup.neg_zero]

/-- Away from skipped roots, the candidate recovers every original source
constraint exactly. This permits reuse of segment semantics without assuming an
old whole-table predicate or its smaller height cap. -/
theorem old_row_of_nodup (hL : TableLocal (DedupTable.table cap) tr tt pub)
    {r : Nat} (hr : r<tr.height tt) (hd : tr.cell tt r SrcpV3.dup=0) :
    ∀ e ∈ SrcpV3.constraints, e.eval tr tt r pub=0 := by
  have hh : ∀ v ∈ (SrcpV3.constraints.mapIdx DedupTable.patch).map (fun e => e.eval tr tt r pub), v=0 := by
    intro v hv
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hv
    exact hL.constr r hr e (List.mem_append_left _ he)
  rw [patched_values_nodup hd] at hh
  intro e he
  exact hh _ (List.mem_map.mpr ⟨e, he, rfl⟩)

/-- All original source constraints hold on arbitrary accepting segment rows. -/
theorem old_segment_row (hL : TableLocal (DedupTable.table cap) tr tt pub)
    {r : Nat} (hr : r<tr.height tt) (hs : tr.cell tt r SrcpV3.sg=1) :
    ∀ e ∈ SrcpV3.constraints, e.eval tr tt r pub=0 :=
  old_row_of_nodup hL hr (segment_nodup hL hr hs)

end ZkFormal.NearV3.Rcpt.Candidates.DedupProof
