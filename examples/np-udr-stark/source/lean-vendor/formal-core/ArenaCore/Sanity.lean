import ArenaCore.Admission

/-!
# ArenaCore.Sanity — non-vacuity checks on the obligation shapes

Machine-checked evidence that the obligations cannot be met by degenerate
verifiers.  (These are theorems about the *definitions*; they are part of
the formal-core build so a change that makes an obligation vacuous breaks
the build.)
-/

namespace ArenaCore.Sanity

open Security

/-- The always-accepting verifier. -/
def acceptAll : Verifier := fun _ _ _ => true
/-- The always-rejecting verifier. -/
def rejectAll : Verifier := fun _ _ _ => false

/-- Deterministic soundness fails for the always-accepting verifier as soon
as some claim bytes are outside the language. -/
theorem acceptAll_not_deterministicSound (L : Bytes → Prop) (pub : Bytes)
    (h : ∃ cb, ¬ L cb) : ¬ DeterministicSound L acceptAll pub := by
  intro hs
  obtain ⟨cb, hcb⟩ := h
  exact hcb (hs cb [] rfl)

/-- Verifier completeness fails for the always-rejecting verifier as soon as
some in-domain claim is true. -/
theorem rejectAll_not_complete (S : ChallengeSpec) (pub : Bytes) (m : Nat)
    (h : ∃ c w, S.Domain c ∧ S.Rel c w) : ¬ VerifierComplete S rejectAll pub m := by
  intro hc
  obtain ⟨c, w, hd, hr⟩ := h
  obtain ⟨_, _, hacc⟩ := hc c w hd hr
  exact Bool.false_ne_true hacc

/-- Semantic soundness and completeness together pin `B` between the
relation's domain-restricted language and the relation's language:
`B = False` is impossible when a true in-domain claim exists. -/
theorem backend_false_not_complete (S : ChallengeSpec) (h : ∃ c w, S.Domain c ∧ S.Rel c w) :
    ¬ (Backend.SemComplete ({ Aux := Unit, B := fun _ _ => False } : Backend S)) := by
  intro hc
  obtain ⟨c, w, hd, hr⟩ := h
  obtain ⟨_, hb⟩ := hc c w hd hr
  exact hb

theorem backend_true_not_sound (S : ChallengeSpec) (h : ∃ c, ∀ w, ¬ S.Rel c w) :
    ¬ (Backend.SemSound ({ Aux := Unit, B := fun _ _ => True } : Backend S)) := by
  intro hs
  obtain ⟨c, hc⟩ := h
  obtain ⟨w, hw⟩ := hs c () trivial
  exact hc w hw

/-- The oracle verifier that accepts everything without hashing. -/
def acceptAllO : OracleVerifier := ⟨fun _ hs _ _ _ => (true, hs)⟩

/-- The ROM game is not vacuous: against the always-accepting verifier, the
zero-query adversary that outputs a false claim wins with probability one,
so no bound `num/den < 1` holds (for any tape length and budgets). -/
theorem acceptAll_not_romSound (S : ChallengeSpec) (L : Bytes → Prop) (P : OracleProver S)
    (pub cb : Bytes) (hcb : ¬ L cb) (qH qP n num den : Nat) (hlt : num < den) :
    ¬ RomSound S L acceptAllO P pub qH qP n num den := by
  intro hs
  have h := hs (.pure (cb, [])) (.pure _ _) (.pure _ _)
  have hwin : ∀ t, romWins S L acceptAllO P pub (.pure (cb, [])) t := by
    intro t
    exact Or.inr ⟨rfl, hcb⟩
  have hsure : PrLE n roRange (fun _ => True) num den :=
    PrLE.mono (E := fun _ => True) (fun t _ => hwin t) h
  have := (PrLE.sure_iff n roRange num den (Nat.pow_pos (by decide))).mp hsure
  omega

end ArenaCore.Sanity
