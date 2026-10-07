# Isolated log23 protocol candidate

The source partition requires log23 traces. The deployed verifier checks a log22
maximum; increasing only a size model cannot admit those traces.

`ZkFormal.V2.Log23` is an additive candidate family. `Basic` parameterizes table,
AIR and public-segment well-formedness by height, with definitional agreement at
22, monotonicity, extraction facts, and unchanged bus budgets. Candidate parameters
use logBlowup4, maxLogLde27, posBits27, 24 chunks of nine positions, and the same
8 MiB proof cap. Header/layout/query bounds prove every admitted domain fits the
field two-adicity27 and the 243-bit query encoding.

`Verifier` instantiates the existing v2 execution with candidate header checks.
Those checks also enforce public AIR well-formedness, group size1–3, and minimum
query log8. This executable candidate has no inherited soundness certificate.

`TransportBudget` proves the existing chunk-good count is dominated on all
query logs8–27 by its value at8. The actual `Assembly.QueryOk` and BCS numerical
128-bit transport budget therefore continue to pass, conditional on the existing
prover/verifier query budgets and bad-event count. `Budget` separately checks the
largest-domain arithmetic and a coarse FRI degree bound. These arithmetic facts
do not establish the candidate round-by-round soundness obligations.

Validation: four modules build; `test/AuditLog23Candidate.lean` passes21 exact
axiom guards and eight kernel boundary regressions. The regressions include
log23 acceptance, deployed rejection of the same table, log24 rejection, group
bounds, minimum query domain, and rejection of a26-bit position encoding atlog27.

Remaining: candidate transcript/stage and round proofs; subgroup/DEEP/FRI
composition; actual bus multiplicity and fingerprint bounds; RBR and ROM
soundness; actual verifier/prover query counts; honest completeness; proof-byte
accounting and admission of the complete AIR. No frozen protocol or challenge
pin is changed. The candidate is not a replacement certificate.
