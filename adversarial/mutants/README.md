# Mutation-testing harness (judge-owned)

These are **definitions**, not a runnable harness yet: the reference backends
they target (`examples/<backend>/`, owned by the `backend-*` lanes) do not exist
at the time this lane was written. The integrator wires them in once a backend
is present.

## What this measures — and what it does not

Mutation testing here perturbs a **reference backend's source**, rebuilds it,
and reruns the full judge pipeline. A mutant is:

- **killed** — some mandatory gate FAILed (the judge caught the injected fault);
- **survived** — the judge still ADMITTED it (a hole in the judge's gates);
- **equivalent** — the mutant cannot change any judge-observable outcome, so
  surviving is correct (see below);
- **timeout / build_error** — excluded from ratios.

> **The forbidden claim.** `gate_coverage_ppm = killed / (killed + survived)` is
> a measure of **judge-gate coverage against injected faults**. It is **not**
> "formal correctness %", and the report schema hard-codes a disclaimer saying
> so. A backend's soundness rests on its **formal certificate** and the
> **axiom audit**, which no amount of mutation testing can substitute for. A
> 100% kill ratio with a missing certificate is still REJECTED.

## Equivalence (do not demand rejection of correct optimizations)

Backends are free to optimize. A mutant that reorders independent work, does
strength reduction, or caches in a way that is **still correct on held-out
inputs** is *equivalent* and is expected to survive. Equivalence is adjudicated
by the differential **oracle** (claims match on the full held-out suite) and the
**adversarial-proof** set (verify decisions unchanged), never by diffing source.
See `operators.json` → `equivalence_policy`.

## Files

- `operators.json` — generic + `reexec-witness` backend-specific mutation
  operators, each with the gate expected to kill it and an equivalence note.
- `report.schema.json` — the report format (`arena-mutation-report-v1`),
  including the mandatory non-correctness disclaimer.

## Integration steps (for the integrator, once a backend exists)

1. For each operator applicable to `examples/<backend>/`, produce one mutant
   source tree.
2. Build + submit each through the judge (reuse `adversarial/e2e`).
3. Classify by the decision/gates; reclassify survivors as equivalent only on
   oracle + adversarial agreement over the held-out set.
4. Emit a `arena-mutation-report-v1` document. Never render the ratio next to,
   or labelled as, a correctness figure.
