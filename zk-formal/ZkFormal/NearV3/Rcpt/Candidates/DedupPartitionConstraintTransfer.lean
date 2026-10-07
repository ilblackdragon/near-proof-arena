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
private theorem right_static : rightConstraints.all (fun e =>
    noFirst e && (decide (e = .const 0) || DedupTable.constraints.any (fun x => decide (e = x)))) = true := by
  decide +kernel

/-- Suppressing the four global-first equations is exactly sufficient to start
the second physical table on an arbitrary authenticated logical carry row. -/
theorem right_of_zero_first (C D : Nat → Int) (fst lst trn : Int) (pub : Nat → Int)
    (h : ∀ ex ∈ DedupTable.constraints, ev C D 0 lst trn pub ex = 0) :
    ∀ ex ∈ rightConstraints, ev C D fst lst trn pub ex = 0 := by
  intro ex hex
  have hh := List.all_eq_true.mp right_static ex hex
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hh
  rw [ev_noFirst ex hh.1]
  rcases hh.2 with he | he
  · rw [he]; rfl
  · obtain ⟨x, hx, heq⟩ := List.any_eq_true.mp he
    exact (of_decide_eq_true heq).symm ▸ h x hx

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

end ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable
