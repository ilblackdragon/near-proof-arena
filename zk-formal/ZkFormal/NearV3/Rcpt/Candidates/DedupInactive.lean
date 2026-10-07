import ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionEndpoint
import ZkFormal.NearV3.Rcpt.Candidates.DedupCarry

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

private def inactiveEquations : List Expr :=
  [ .mul (c SrcpV3.wf) (not (c SrcpV3.sg)),
    .mul (c SrcpV3.wl) (not (c SrcpV3.sg)),
    .mul (c SrcpV3.lf) (not (c SrcpV3.sg)),
    sub (c SrcpV3.sf) (.mul (c SrcpV3.wf) (not (c SrcpV3.wn))),
    sub (c SrcpV3.sl) (.mul (c SrcpV3.wl) (.add (c SrcpV3.wn) (c SrcpV3.lf))),
    .mul (c SrcpV3.dup) (not (c SrcpV3.rt)),
    .mul (c DedupTable.repeated) (not (c SrcpV3.rt)),
    sub (c SrcpV3.gD) (.add DedupTable.computedRoot (.mul (c SrcpV3.wf) (c SrcpV3.aw))),
    .mul (c SrcpV3.gz) (not DedupTable.endRow) ]

set_option maxRecDepth 32768 in
private theorem inactive_mem : ∀ e ∈ inactiveEquations, e ∈ rightConstraints := by
  have hh : inactiveEquations.all (fun e => rightConstraints.any (fun x => decide (e = x))) = true := by
    decide +kernel
  intro e he
  obtain ⟨x, hx, heq⟩ := List.any_eq_true.mp (List.all_eq_true.mp hh e he)
  exact (of_decide_eq_true heq).symm ▸ hx

/-- Inactive source rows have no window flags, duplicate/repetition flags, or
bus selectors. This is derived from arbitrary field constraints. -/
theorem inactive_flags {tr : Trace Fp} {tt r : Nat} {pub : List Fp}
    (h : ∀ ex ∈ rightConstraints, ex.eval tr tt r pub = 0)
    (hrt : tr.cell tt r SrcpV3.rt = 0) (hsg : tr.cell tt r SrcpV3.sg = 0) :
    tr.cell tt r SrcpV3.wf = 0 ∧ tr.cell tt r SrcpV3.wl = 0 ∧
    tr.cell tt r SrcpV3.lf = 0 ∧ tr.cell tt r SrcpV3.sf = 0 ∧
    tr.cell tt r SrcpV3.sl = 0 ∧ tr.cell tt r SrcpV3.dup = 0 ∧
    tr.cell tt r DedupTable.repeated = 0 ∧ tr.cell tt r SrcpV3.gD = 0 ∧
    tr.cell tt r SrcpV3.gz = 0 := by
  have hh : ∀ e ∈ inactiveEquations, e.eval tr tt r pub = 0 :=
    fun e he => h e (inactive_mem e he)
  simp only [inactiveEquations, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, eval_mul, eval_not, eval_c, eval_sub, eval_add,
    DedupTable.computedRoot, DedupTable.endRow, hrt, hsg] at hh
  grind

/-- The terminal physical source row emits no ordinary source messages on any
bus, including SIZE. Its only possible partition traffic is the dedicated carry
interaction (which is not in this base list). -/
theorem endpoint_base_traffic_empty {tr : Trace Fp} {tt r : Nat} {pub : List Fp}
    (hl : r + 1 = tr.height tt)
    (h : ∀ ex ∈ rightConstraints, ex.eval tr tt r pub = 0)
    (bus : Nat) (send : Bool) :
    rowTraffic DedupTable.interactions tr tt r pub bus send = [] := by
  obtain ⟨hrt, hsg⟩ := field_endpoint_inactive hl h
  have hf := inactive_flags h hrt hsg
  have hgd := hf.2.2.2.2.2.2.2.1
  have hgz := hf.2.2.2.2.2.2.2.2
  simp [DedupTable.interactions, rowTraffic, Dsl.send, Dsl.recv,
    Interaction.multNat, Interaction.multNat.go, eval_c, hrt, hsg, hgd, hgz, Fp.toNat_zero]

end ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable
