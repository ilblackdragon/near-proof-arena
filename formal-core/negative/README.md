# Negative certificate suite

Each `NN_*.lean` file is a candidate certificate (`Candidate.certificate`)
that the formal checker **must reject**. `00_positive_control.lean` must be
accepted. Every file's first line states the expected reason code.
`check_negative.sh` is a minimal reference harness. It builds the
judge-generated wrapper `theorem ArenaJudge.check : <Expected> :=
Candidate.certificate`, then checks elaboration and the transitive axiom set
against `[propext, Classical.choice, Quot.sound]`.

| file | attack | caught by | reason code |
|------|--------|-----------|-------------|
| `00_positive_control` | the real toy certificate | — | PASS |
| `01_sorry` | `sorry` | axiom audit (`sorryAx`) | `SORRY_FOUND` |
| `02_extra_axiom` | candidate `axiom sha256_injective` | axiom audit | `FORBIDDEN_AXIOM` |
| `03_native_decide` | digests "proved" by `native_decide` | axiom audit (`*._native.native_decide.ax_*`) | `NATIVE_EVAL_FOUND` |
| `04_false_premise` | adds premise "SHA-256 is injective" (false) | type check | `THEOREM_TYPE_MISMATCH` |
| `05_false_premise_proved` | sorry-free variant: unsatisfiable premise, clean axioms | type check only | `THEOREM_TYPE_MISMATCH` |
| `06_shadowed_definition` | local `AdmissionStatement := True`, same surface syntax | type check (wrapper uses the judge's constant) | `SHADOWED_DEFINITION` |
| `07_wrong_theorem_type` | true theorem, wrong statement | type check | `THEOREM_TYPE_MISMATCH` |
| `08_wrong_params` | admission for weakened challenge params | type check | `THEOREM_TYPE_MISMATCH` |
| `09_stale_digest` | proof for old bytecode after the judge froze a new digest | kernel digest evaluation fails | `ARTIFACT_BINDING_FAILED` |
| `10_tampered_core` | ships its own `ArenaCore.AdmissionStatement := True` | elaboration against pinned formal-core (redeclaration) | `SHADOWED_DEFINITION` |
| `11_wrong_route_native` | certifies a native model while the judge froze the interpreter route | type check | `THEOREM_TYPE_MISMATCH` |

Notes for the formal-checker lane:

* 05 shows why the type comparison is mandatory: it elaborates with clean
  axioms.
* 10 elaborates fine **on its own**. Rejection depends on the checker
  building against the pinned formal-core and refusing candidate modules in
  reserved namespaces.
* Re-checking with independent kernels (lean4checker, nanoda) is not
  exercised here, because no example forges kernel terms. Add such cases
  (e.g. `debug.skipKernelTC`, hand-crafted `.olean`) to the checker's own
  suite.
