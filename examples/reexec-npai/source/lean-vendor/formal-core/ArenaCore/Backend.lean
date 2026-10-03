import ArenaCore.Relation

/-!
# ArenaCore.Backend — the backend's semantic side

A backend (zkVM, STARK/AIR, SNARK/R1CS, re-execution, …) is described to the
arena only through a *proof-system-independent* predicate

  `B : Claim → Aux → Prop`

("`aux` is a valid backend-level object for claim `c`", e.g. an execution
trace satisfying the AIR, a satisfying R1CS assignment, a re-execution log).
No AIR/R1CS vocabulary appears in the contract.  The two semantic
obligations are

* soundness    : `∀ c aux, B c aux → ∃ w, Rel c w`
* completeness : `∀ c w, Domain c → Rel c w → ∃ aux, B c aux`

Anti-vacuity: `Domain` is a field of the *challenge* (`ChallengeSpec`), not
of the backend, and appears only as a precondition of completeness; soundness
has no precondition at all.  The candidate chooses `Aux` and `B` freely, but
because both directions are required, `B` cannot be `False` (completeness
fails on any in-domain true claim) and cannot be `True` (soundness fails on
any false claim).  How `B` is connected to what the deployed verifier accepts
is the job of `ArenaCore.Verifier` and `ArenaCore.Security`.
-/

namespace ArenaCore

structure Backend (S : ChallengeSpec) where
  /-- Backend-level auxiliary object (trace, assignment, …). -/
  Aux : Type
  /-- Backend semantic predicate. -/
  B : S.Claim → Aux → Prop

namespace Backend

variable {S : ChallengeSpec}

/-- `FORMAL_SEMANTIC_SOUNDNESS` -/
def SemSound (bk : Backend S) : Prop :=
  ∀ c aux, bk.B c aux → ∃ w, S.Rel c w

/-- `FORMAL_SEMANTIC_COMPLETENESS` (domain fixed by the challenge). -/
def SemComplete (bk : Backend S) : Prop :=
  ∀ c w, S.Domain c → S.Rel c w → ∃ aux, bk.B c aux

/-- Claim bytes that decode to a claim with a valid backend object. -/
def InLang (bk : Backend S) (cb : Bytes) : Prop :=
  ∃ c, S.decodeClaim cb = some c ∧ ∃ aux, bk.B c aux

/-- Semantic soundness lifts to languages: the backend language is contained
in the relation's language. -/
theorem inLang_rel (bk : Backend S) (h : bk.SemSound) {cb : Bytes} :
    bk.InLang cb → S.InLang cb := by
  rintro ⟨c, hc, aux, hb⟩
  exact ⟨c, hc, h c aux hb⟩

end Backend

end ArenaCore
