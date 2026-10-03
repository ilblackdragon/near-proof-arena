import ArenaExpectedInst
import Toy.Certificate

/-- Certificate for the native-lean route: obligations about the candidate model. -/
theorem Candidate.certificate : ArenaExpectedInst.expectedType :=
  ⟨Toy.toyPub, Candidate.Model.verify, by decide +kernel, rfl, Toy.toyBackend, Toy.toyObligations⟩
