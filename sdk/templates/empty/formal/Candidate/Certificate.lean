/-
  Candidate certificate.

  The judge constructs the *type* of `Candidate.certificate` from the
  challenge (the admission theorem in `formal-core`: semantic soundness,
  semantic completeness, cryptographic soundness at the challenge's security
  profile, and the connection between your production `verify` artifact and
  the formal verifier). You provide the *value*: a proof.

  Rules enforced by the judge (see docs/AGENT_CONTRACT.md §6):
  * no `sorry`/`admit`, no `native_decide`, no `implemented_by`/`extern` in
    the trusted path, no new `axiom` declarations;
  * transitive axioms must be within the challenge's axiom allowlist;
  * cryptographic assumptions only via the approved `formal-core` assumption
    declarations listed in the security profile;
  * you may not shadow or redefine spec / formal-core declarations.

  The placeholder below has the wrong type on purpose: the judge will report
  THEOREM_TYPE_MISMATCH until you replace it with the real admission theorem.
-/
namespace Candidate

/-- Placeholder. Replace with `theorem certificate : <admission type> := ...`. -/
theorem certificate : True := trivial

end Candidate
