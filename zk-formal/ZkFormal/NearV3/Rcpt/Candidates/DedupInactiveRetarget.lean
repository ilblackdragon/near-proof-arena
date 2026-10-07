import ZkFormal.NearV3.Rcpt.Candidates.DedupInactive

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra

/-- Explicit cell/selector environment used when joining physical source traces. -/
def cellEnv (C D : Nat → Fp) (fst lst trn : Fp) (pub : Nat → Fp) : Env Fp :=
  { ofNat := fun n => (n : Fp), add := (· + ·), mul := (· * ·), neg := (- ·),
    col := fun x nx => if nx then D x else C x, pub,
    isFirst := fst, isLast := lst, isTransition := trn }

structure Inactive (C : Nat → Fp) : Prop where
  rt : C SrcpV3.rt = 0
  sg : C SrcpV3.sg = 0
  wf : C SrcpV3.wf = 0
  wl : C SrcpV3.wl = 0
  lf : C SrcpV3.lf = 0
  sf : C SrcpV3.sf = 0
  sl : C SrcpV3.sl = 0
  dup : C SrcpV3.dup = 0
  rep : C DedupTable.repeated = 0
  gd : C SrcpV3.gD = 0
  gz : C SrcpV3.gz = 0

/-- Arbitrary accepting right endpoints supply the inactive-row invariant. -/
theorem endpoint_inactive {tr : Trace Fp} {tt r : Nat} {pub : List Fp}
    (hl : r + 1 = tr.height tt)
    (h : ∀ ex ∈ rightConstraints, ex.eval tr tt r pub = 0) :
    Inactive (tr.cell tt r) := by
  obtain ⟨hrt, hsg⟩ := field_endpoint_inactive hl h
  obtain ⟨hwf, hwl, hlf, hsf, hsl, hdup, hrep, hgd, hgz⟩ := inactive_flags h hrt hsg
  exact ⟨hrt, hsg, hwf, hwl, hlf, hsf, hsl, hdup, hrep, hgd, hgz⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
/-- A terminal inactive row can change its cyclic successor without changing any
logical source constraint. In particular the final clone may wrap globally. -/
theorem inactive_terminal_retarget (C D E : Nat → Fp) (h : Inactive C)
    (lst lst' : Fp) (pub : Nat → Fp) :
    ∀ ex ∈ DedupTable.constraints,
      ex.evalWith (cellEnv C D 0 lst 0 pub) =
      ex.evalWith (cellEnv C E 0 lst' 0 pub) := by
  simp [or_imp, forall_and, forall_exists_index, and_imp, List.forall_mem_append,
    DedupTable.constraints, DedupTable.patch, DedupTable.additions,
    DedupTable.computedRoot, DedupTable.endRow,
    SrcpV3.constraints, SrcpV3.listConst, SrcpV3.segConst, SrcpV3.actE,
    Expr.evalWith, cellEnv, Dsl.bool, Dsl.mul3, Dsl.sub, Dsl.not, Dsl.c, Dsl.n, Dsl.k,
    Dsl.smul, Dsl.sum, Dsl.mid, h.rt, h.sg, h.wf, h.wl, h.lf, h.sf, h.sl,
    h.dup, h.rep, h.gd, h.gz,
    Lean.Grind.Semiring.natCast_zero, Lean.Grind.Semiring.natCast_one,
    Lean.Grind.Semiring.zero_mul, Lean.Grind.Semiring.mul_zero,
    Lean.Grind.Semiring.one_mul, Lean.Grind.Semiring.mul_one,
    Lean.Grind.Semiring.add_zero, Lean.Grind.AddCommMonoid.zero_add,
    Lean.Grind.AddCommGroup.add_neg_cancel, Lean.Grind.AddCommGroup.neg_zero]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
/-- An inactive terminal row can be extended by its clone. This supplies one
padding row so the joined logical trace has power-of-two height2H. -/
theorem inactive_self_step (C E : Nat → Fp) (h : Inactive C)
    (lst : Fp) (pub : Nat → Fp) :
    ∀ ex ∈ DedupTable.constraints,
      ex.evalWith (cellEnv C C 0 0 1 pub) =
      ex.evalWith (cellEnv C E 0 lst 0 pub) := by
  simp [or_imp, forall_and, forall_exists_index, and_imp, List.forall_mem_append,
    DedupTable.constraints, DedupTable.patch, DedupTable.additions,
    DedupTable.computedRoot, DedupTable.endRow,
    SrcpV3.constraints, SrcpV3.listConst, SrcpV3.segConst, SrcpV3.actE,
    Expr.evalWith, cellEnv, Dsl.bool, Dsl.mul3, Dsl.sub, Dsl.not, Dsl.c, Dsl.n, Dsl.k,
    Dsl.smul, Dsl.sum, Dsl.mid, h.rt, h.sg, h.wf, h.wl, h.lf, h.sf, h.sl,
    h.dup, h.rep, h.gd, h.gz,
    Lean.Grind.Semiring.natCast_zero, Lean.Grind.Semiring.natCast_one,
    Lean.Grind.Semiring.zero_mul, Lean.Grind.Semiring.mul_zero,
    Lean.Grind.Semiring.one_mul, Lean.Grind.Semiring.mul_one,
    Lean.Grind.Semiring.add_zero, Lean.Grind.AddCommMonoid.zero_add,
    Lean.Grind.AddCommGroup.add_neg_cancel, Lean.Grind.AddCommGroup.neg_zero]

end ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable
