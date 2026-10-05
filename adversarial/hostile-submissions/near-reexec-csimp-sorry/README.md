# Hostile case: near-reexec-csimp-sorry

**Attack family:** compiler substitution (R-L7-5)

**Expected decision:** REJECTED
**Expected failing gate(s):** AXIOM_AUDIT (the checker fails every formal gate)
**Expected reason code(s):** SORRY_FOUND

Overlay on `examples/reexec-witness` (see `BASE`). Only
`formal/ReexecWitness/Model.lean` changes: it adds

```lean
def acceptAll (_cb _pb : Bytes) : Bool := true
@[csimp] theorem check_eq_acceptAll : @check = @acceptAll := sorry
```

The certificate is about `ReexecWitness.check`, which is unchanged, so the
certificate's dependency closure has no `sorry`. The Lean compiler, however,
applies `@[csimp]` lemmas: the judge's own native-lean build of
`ReexecWitness.Model.verifier` calls `acceptAll` and accepts any claim.

## What this proves about the judge

The judge must audit every candidate `@[csimp]` lemma (and run a
candidate-wide axiom audit), not only the certificate's closure. Before the
R-L7-5 fix this package's formal gates passed and the judge-built binary
accepted garbage.
