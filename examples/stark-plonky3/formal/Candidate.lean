import Candidate.Spec
import Candidate.Backend
import Candidate.Pipeline
import Candidate.Status

/-!
# stark-plonky3 — PARTIAL certificate structure (EXPERIMENTAL tier)

This project deliberately does **not** define `Candidate.certificate`. The
admission statement cannot be proved for this backend today and we refuse to
fake it with `sorry` or an axiom: the judge must report
`CERTIFICATE_MISSING` / `OBLIGATION_UNDISCHARGED`.

Kernel-checked here, with no `sorry` / axioms beyond the allowlist:
* `Candidate.Spec`     — the challenge's `ArenaCore.ChallengeSpec`.
* `Candidate.Backend`  — the (honestly vacuous) backend predicate `B := Rel`
  and its semantic soundness / completeness.
* `Candidate.Pipeline` — the STARK pipeline with every open obligation as an
  explicit hypothesis, and the composition theorem `sound_or_forged`.
* `Candidate.Status`   — the obligation table as data (mirrors EVIDENCE.md).
-/
