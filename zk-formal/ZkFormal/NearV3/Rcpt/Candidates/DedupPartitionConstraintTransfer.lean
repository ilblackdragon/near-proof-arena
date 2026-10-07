import ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable
import ZkFormal.Near.Render.Proof.NodeEv

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable
open ZkFormal.Near ZkFormal.Near.Render.EvI ZkFormal.Air

private def noFirst : Expr → Bool
  | .isFirst => false
  | .add a b | .mul a b => noFirst a && noFirst b
  | .neg a => noFirst a
  | _ => true

private theorem ev_noFirst (e : Expr) (he : noFirst e = true)
    (C D : Nat → Int) (fst lst trn : Int) (pub : Nat → Int) :
    ev C D fst lst trn pub e = ev C D 0 lst trn pub e := by
  induction e with
  | add a b ha hb | mul a b ha hb =>
    have hh : noFirst a = true ∧ noFirst b = true := by
      simpa only [noFirst, Bool.and_eq_true] using he
    simp only [ev, ha hh.1, hb hh.2]
  | neg a ha => simp only [ev, ha he]
  | isFirst => simp [noFirst] at he
  | _ => rfl

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem right_static : rightBaseConstraints.all (fun e =>
    noFirst e && (decide (e = .const 0) || DedupTable.constraints.any (fun x => decide (e = x)))) = true := by
  decide +kernel

/-- Suppressing the four global-first equations is exactly sufficient to start
the second physical table on an arbitrary authenticated logical carry row. -/
theorem right_of_zero_first (C D : Nat → Int) (fst lst trn : Int) (pub : Nat → Int)
    (h : ∀ ex ∈ DedupTable.constraints, ev C D 0 lst trn pub ex = 0)
    (hpad : lst * (C SrcpV3.rt + C SrcpV3.sg) = 0) :
    ∀ ex ∈ rightConstraints, ev C D fst lst trn pub ex = 0 := by
  intro ex hex
  rcases List.mem_append.mp hex with hex | hex
  · have hh := List.all_eq_true.mp right_static ex hex
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hh
    rw [ev_noFirst ex hh.1]
    rcases hh.2 with he | he
    · rw [he]; rfl
    · obtain ⟨x, hx, heq⟩ := List.any_eq_true.mp he
      exact (of_decide_eq_true heq).symm ▸ h x hx

  · have he : ex = rightEndpoint := by simpa using hex
    subst ex
    simpa [rightEndpoint, SrcpV3.actE, Dsl.c, ev] using hpad

/-- Gated left-table constraints preserve every non-endpoint logical row. -/
theorem left_of_not_last (C D : Nat → Int) (fst trn : Int) (pub : Nat → Int)
    (h : ∀ ex ∈ DedupTable.constraints, ev C D fst 0 trn pub ex = 0) :
    ∀ ex ∈ leftConstraints, ev C D fst 0 trn pub ex = 0 := by
  intro ex hex
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hex
  simpa [ev, Dsl.not, Dsl.sub, Dsl.k] using h e he

/-- The left endpoint is only the carried copy: no successor relation wraps there. -/
theorem left_last (C D : Nat → Int) (fst trn : Int) (pub : Nat → Int) :
    ∀ ex ∈ leftConstraints, ev C D fst 1 trn pub ex = 0 := by
  intro ex hex
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hex
  simp [ev, Dsl.not, Dsl.sub, Dsl.k]

private def firstZero : Expr → Bool
  | .const n => decide (n = 0)
  | .isFirst => true
  | .add a b => firstZero a && firstZero b
  | .mul a b => firstZero a || firstZero b
  | .neg a => firstZero a
  | _ => false

private theorem ev_firstZero (e : Expr) (he : firstZero e = true)
    (C D : Nat → Int) (lst trn : Int) (pub : Nat → Int) :
    ev C D 0 lst trn pub e = 0 := by
  induction e with
  | const n => simp only [firstZero, decide_eq_true_eq] at he; subst n; rfl
  | isFirst => rfl
  | add a b ha hb =>
    have hh : firstZero a = true ∧ firstZero b = true := by
      simpa only [firstZero, Bool.and_eq_true] using he
    simp only [ev, ha hh.1, hb hh.2, Int.add_zero]
  | mul a b ha hb =>
    have hh : firstZero a = true ∨ firstZero b = true := by
      simpa only [firstZero, Bool.or_eq_true] using he
    rcases hh with hh | hh
    · simp only [ev, ha hh, Int.zero_mul]
    · simp only [ev, hb hh, Int.mul_zero]
  | neg a ha => simp only [ev, ha he, Int.neg_zero]
  | _ => simp [firstZero] at he

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem reverse_static : DedupTable.constraints.all (fun e =>
    firstZero e || (noFirst e && rightBaseConstraints.any (fun x => decide (e = x)))) = true := by
  decide +kernel

/-- Arbitrary accepted right rows satisfy every logical source equation with
first-selector zero. This reverse direction assumes no honest cell binding. -/
theorem zero_first_of_right (C D : Nat → Int) (fst lst trn : Int) (pub : Nat → Int)
    (h : ∀ ex ∈ rightConstraints, ev C D fst lst trn pub ex = 0) :
    ∀ ex ∈ DedupTable.constraints, ev C D 0 lst trn pub ex = 0 := by
  intro ex hex
  have hh := List.all_eq_true.mp reverse_static ex hex
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hh
  rcases hh with hz | ⟨hn, hm⟩
  · exact ev_firstZero ex hz C D lst trn pub
  · obtain ⟨x, hx, heq⟩ := List.any_eq_true.mp hm
    have he : ex = x := of_decide_eq_true heq
    have hv := h ex (List.mem_append_left _ (he.symm ▸ hx))
    rwa [ev_noFirst ex hn] at hv

/-- At every nonterminal left row, the gate is one and all logical constraints
are recovered from arbitrary accepted physical constraints. -/
theorem base_of_left (C D : Nat → Int) (fst trn : Int) (pub : Nat → Int)
    (h : ∀ ex ∈ leftConstraints, ev C D fst 0 trn pub ex = 0) :
    ∀ ex ∈ DedupTable.constraints, ev C D fst 0 trn pub ex = 0 := by
  intro ex hex
  have hh := h (.mul (Dsl.not .isLast) ex) (List.mem_map.mpr ⟨ex, hex, rfl⟩)
  simpa [ev, Dsl.not, Dsl.sub, Dsl.k] using hh

/-- The added endpoint equation is enforced for arbitrary right traces. -/
theorem endpoint_of_right (C D : Nat → Int) (fst trn : Int) (pub : Nat → Int)
    (h : ∀ ex ∈ rightConstraints, ev C D fst 1 trn pub ex = 0) :
    C SrcpV3.rt + C SrcpV3.sg = 0 := by
  have hh := h rightEndpoint (List.mem_append_right _ (by simp))
  simpa [rightEndpoint, SrcpV3.actE, Dsl.c, ev] using hh

private theorem evalWith_noFirst {F : Type} (env : Env F) (first : F)
    (e : Expr) (he : noFirst e = true) :
    e.evalWith env = e.evalWith { env with isFirst := first } := by
  induction e with
  | add a b ha hb | mul a b ha hb =>
    have hh : noFirst a = true ∧ noFirst b = true := by
      simpa only [noFirst, Bool.and_eq_true] using he
    simp only [Expr.evalWith, ha hh.1, hb hh.2]
  | neg a ha => simp only [Expr.evalWith, ha he]
  | isFirst => simp [noFirst] at he
  | _ => rfl

private theorem evalWith_firstZero {F : Type} [Lean.Grind.CommRing F]
    (tr : Trace F) (tt r : Nat) (pub : List F) (e : Expr) (he : firstZero e = true) :
    e.evalWith { rowEnv tr tt r pub with isFirst := 0 } = 0 := by
  induction e with
  | const n =>
    simp only [firstZero, decide_eq_true_eq] at he
    subst n
    simp only [Expr.evalWith, rowEnv]; grind
  | isFirst => rfl
  | add a b ha hb =>
    have hh : firstZero a = true ∧ firstZero b = true := by
      simpa only [firstZero, Bool.and_eq_true] using he
    change _ + _ = 0
    rw [ha hh.1, hb hh.2]
    grind
  | mul a b ha hb =>
    have hh : firstZero a = true ∨ firstZero b = true := by
      simpa only [firstZero, Bool.or_eq_true] using he
    rcases hh with hh | hh
    · change _ * _ = 0
      rw [ha hh]; grind
    · change _ * _ = 0
      rw [hb hh]; grind
  | neg a ha =>
    change - _ = 0
    rw [ha he]; grind
  | _ => simp [firstZero] at he

/-- Direct reverse transfer in the actual field (indeed any commutative ring),
without lifting a vanishing field polynomial to an integer equality. -/
theorem field_zero_first_of_right {F : Type} [Lean.Grind.CommRing F]
    (tr : Trace F) (tt r : Nat) (pub : List F)
    (h : ∀ ex ∈ rightConstraints, ex.eval tr tt r pub = 0) :
    ∀ ex ∈ DedupTable.constraints,
      ex.evalWith { rowEnv tr tt r pub with isFirst := 0 } = 0 := by
  intro ex hex
  have hh := List.all_eq_true.mp reverse_static ex hex
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hh
  rcases hh with hz | ⟨hn, hm⟩
  · exact evalWith_firstZero tr tt r pub ex hz
  · obtain ⟨x, hx, heq⟩ := List.any_eq_true.mp hm
    have he : ex = x := of_decide_eq_true heq
    have hv := h ex (List.mem_append_left _ (he.symm ▸ hx))
    change ex.evalWith (rowEnv tr tt r pub) = 0 at hv
    rwa [evalWith_noFirst _ 0 ex hn] at hv

/-- All logical equations hold on nonterminal left rows over the actual field. -/
theorem field_base_of_left {tr : Trace ZkFormal.Algebra.Fp} {tt r : Nat}
    {pub : List ZkFormal.Algebra.Fp} (hl : r + 1 ≠ tr.height tt)
    (h : ∀ ex ∈ leftConstraints, ex.eval tr tt r pub = 0) :
    ∀ ex ∈ DedupTable.constraints, ex.eval tr tt r pub = 0 := by
  intro ex hex
  have hh := h (.mul (Dsl.not .isLast) ex) (List.mem_map.mpr ⟨ex, hex, rfl⟩)
  simp only [eval_mul, eval_not, eval_isLast, hl, ite_false] at hh
  grind

/-- Right physical endpoints are inactive in any accepting field trace. -/
theorem field_endpoint_sum {tr : Trace ZkFormal.Algebra.Fp} {tt r : Nat}
    {pub : List ZkFormal.Algebra.Fp} (hl : r + 1 = tr.height tt)
    (h : ∀ ex ∈ rightConstraints, ex.eval tr tt r pub = 0) :
    tr.cell tt r SrcpV3.rt + tr.cell tt r SrcpV3.sg = 0 := by
  have hh := h rightEndpoint (List.mem_append_right _ (by simp))
  simp only [rightEndpoint, SrcpV3.actE, eval_mul, eval_add, eval_c, eval_isLast, hl, ite_true] at hh
  grind

end ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable
