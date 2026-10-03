import Candidate.Spec
import Candidate.Backend
import Candidate.Pipeline
import Candidate.Status

/-!
# zkvm-sp1 — PARTIAL certificate structure (EXPERIMENTAL tier)

This project deliberately does **not** define `Candidate.certificate`.
The admission statement `ArenaCore.AdmissionStatement` cannot be proved for
this backend today, and we refuse to fake it with `sorry` or an axiom: the
judge must report `CERTIFICATE_MISSING` / `OBLIGATION_UNDISCHARGED` and must
not admit the candidate under the strict (formal-tier) profile.

What IS here, kernel-checked, with no `sorry`/axioms:
* `Candidate.Spec`     — the challenge's `ArenaCore.ChallengeSpec` assembled from
  `NearSpec.TransferV1.WfClaim` (identical to the spec lane's interface).
* `Candidate.Backend`  — the backend predicate and its semantic soundness and
  completeness (FORMAL_SEMANTIC_SOUNDNESS / _COMPLETENESS at the `B` level).
* `Candidate.Pipeline` — an abstract model of the SP1 pipeline with every open
  obligation as an explicit hypothesis, and the (proved) composition theorem:
  the open obligations together imply deterministic soundness of the modelled
  verifier against the NEAR relation's language.
* `Candidate.Status`   — the obligation table as data (mirrors EVIDENCE.md).
-/
