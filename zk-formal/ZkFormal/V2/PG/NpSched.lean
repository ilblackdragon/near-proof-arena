import ZkFormal.V2.PG.NpStatements

/-!
# ZkFormal.V2.PG.NpSched (P2 copy of `Prover.NpSched` at `dp = pg g`) — the schedule as message/challenge pairs (`SchedFormStmt`)
-/

namespace ZkFormal.Prover.Np.G

variable [AuxG]

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np

theorem slotsOf_append (a b : List (List Part × Bool)) : slotsOf (a ++ b) = slotsOf a ++ slotsOf b := by
  simp [slotsOf, List.flatMap_append]

theorem slotsOf_map {α : Type} (l : List α) (f : α → List Part × Bool) :
    slotsOf (l.map f) = l.flatMap fun a => [.msg (f a).1, .chal (f a).2] := by
  simp [slotsOf, List.flatMap_map]

theorem friSched_eq (A : Air) (tr : Trace Fp) :
    friSchedule A dp (hdr A tr) =
      slotsOf ((kinds A tr).map fun k => (kindParts A tr k, false)) ++ [.msg [.elems 2]] := by
  rw [slotsOf_map]
  unfold friSchedule kinds friChalKinds
  simp only [List.flatMap_append, List.append_assoc]
  congr 1
  · rw [List.flatMap_assoc]
    congr 1; funext i
    rw [List.flatMap_append]
    congr 1
    · split <;> simp [kindParts]
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, kindParts, commits,
        Bool.false_eq_true, ite_false]
      split <;> rename_i h <;> simp [h, n0]
  · congr 1
    split <;> simp [kindParts]

theorem schedForm : SchedFormStmt := by
  intro A tr
  unfold schedule
  rw [friSched_eq]
  have hrep : ∀ n, slotsOf (List.replicate n (([] : List Part), false)) =
      (List.range n).flatMap fun _ => [Slot.msg [], .chal false] := by
    intro n; induction n with
    | zero => rfl
    | succ n ih =>
      rw [List.replicate_succ', slotsOf_append, ih, List.range_succ, List.flatMap_append]; rfl
  unfold slotPairs
  rw [slotsOf_append, slotsOf_append, hrep]
  simp only [List.append_assoc, nB]
  rfl
