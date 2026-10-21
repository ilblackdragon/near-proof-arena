import Mathlib

/-!
# Deterministic transcript checks for the repaired family-proof interface

An output used as a later input is an ordinary chain edge, not a collision.
The bad event must concern a failed extraction (a first verifier flip), not
acceptance itself. These lemmas do not bound the probability of that event.
-/
namespace Qrom.Transcript

structure Entry (S : Type) where
  input : S
  output : S
  deriving DecidableEq

/-- Reusing an output as an input is deliberately absent. Entries must include
all framing needed to identify an oracle input in the actual instantiation. -/
def WideBad {S : Type} (initial : S) (db : List (Entry S)) : Prop :=
  (∃ a ∈ db, ∃ b ∈ db, a ≠ b ∧ a.output = b.output) ∨
    ∃ a ∈ db, a.output = initial

/-- Counterexample to the withdrawn definition: normal chaining is allowed. -/
theorem honest_edge_not_bad :
    ¬ WideBad 0 ([⟨0, 1⟩, ⟨1, 2⟩] : List (Entry Nat)) := by
  simp [WideBad]

/-- Final state of a transcript represented by prover/verifier labels and the
successive partial transcripts. `true` denotes a prover move. -/
def finalState {S : Type} (s : S) : List (Bool × S) → S
  | [] => s
  | (_, s') :: rest => finalState s' rest

/-- Local knowledge condition at a prover flip and absence of verifier flips.
The quantitative argument must prove the latter holds except with small error. -/
def SafeMoves {S W : Type} (doom : S → Bool) (extract : S → Option W) (R : W → Prop) :
    S → List (Bool × S) → Prop
  | _, [] => True
  | s, (prover, s') :: rest =>
      (prover = true → doom s = false → doom s' = true →
        ∃ w, extract s' = some w ∧ R w) ∧
      (prover = false → doom s = false → doom s' = false) ∧
      SafeMoves doom extract R s' rest

/-- A safe accepting transcript yields a witness; honest acceptance is not a
bad database event. This is the deterministic K1/K2/K4 part only. -/
theorem first_flip_extract {S W : Type} (doom : S → Bool) (extract : S → Option W)
    (R : W → Prop) (s : S) (moves : List (Bool × S))
    (hstart : doom s = false) (hend : doom (finalState s moves) = true)
    (hsafe : SafeMoves doom extract R s moves) : ∃ w, R w := by
  induction moves generalizing s with
  | nil => simp [finalState, hstart] at hend
  | cons move rest ih =>
    rcases move with ⟨prover, s'⟩
    rcases hsafe with ⟨hp, hv, ht⟩
    cases hd : doom s' with
    | false => exact ih s' hd hend ht
    | true =>
      cases prover with
      | false => have hf := hv rfl hstart; simp [hd] at hf
      | true => obtain ⟨w, _, hw⟩ := hp rfl hstart hd; exact ⟨w, hw⟩

end Qrom.Transcript
