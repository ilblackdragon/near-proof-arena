import ReexecV3D3.ReadCanon
import ReexecV3D3.ReadCanonDefs

/-!
# `ReexecV3D3.ReadCanonSplit` — the artifact's acceptance is *strictly stronger* than `RelD3`

Lane `pq-prepare-link`, 2026-10-23.

## Why this file exists

The D3 objective asks for a composition between stages that is **non-vacuous**: one whose premise
carries real content the conclusion does not already have.  `ZkFormal/PQ/Join/Compose.lean` §4 proves
that `compose_pv86` fails this test — under `hagree` its premise is *equivalent* to its conclusion,
so it transfers nothing.

The deployed verifier's acceptance predicate is a different matter.  `ReexecV3D3.Read.check` is

```
check cb w = match checkD3Reads cb w with
             | (.error _, _) => false
             | (.ok (), keys) => encodeReads cb w keys == w
```

Two things happen, not one: the D3 relation must hold, **and** the witness must be the exact
re-encoding of the read set produced by that run.  The second conjunct is not implied by `RelD3`, and
this file proves the decomposition rather than leaving it to a reading of the source:

| declaration | statement | class |
|---|---|---|
| `check_iff` | `check cb w = true ↔ RelD3 cb w ∧ encodeReads cb w (d3Reads cb w) = w` | **[K]** |
| `check_implies_relD3` | `check cb w = true → RelD3 cb w` | **[K]** |
| `relD3_of_check` | the same, named in the join's vocabulary | **[K]** |

`check_sound` in `ReadCanon.lean` already gives the soundness direction (via `checkD3Reads_fst`).
What is new here is the **converse-plus-extra** form: it exhibits the acceptance predicate as
`RelD3 ∧ (canonicality)`, which is what makes a join consuming `check` a genuine strengthening
rather than a restatement.  It is the difference between `compose_pv86` (premise ≡ conclusion) and a
join whose premise provably contains more.

## What this does *not* show

`canonicality` is real extra content, but this file does **not** exhibit a witness that satisfies
`RelD3` and fails it, so "strictly stronger" is established *structurally* (a conjunction with a
conjunct absent from `RelD3`'s statement), not by a separating example.  Producing one needs a
concrete chunk whose read set does not re-encode to itself; candidates are the adversarial fixtures
under `adversarial/`, and that search is **[O]** — recorded rather than guessed.
-/

namespace ReexecV3D3.Read

open NearSpec NearSpecV3 NearSpecV3.D2

/-- **Acceptance decomposes into the relation plus canonicality.**

The two conjuncts are of genuinely different kinds: `RelD3` is about *what the chunk computes*, while
`encodeReads cb w (d3Reads cb w) = w` is about *how the witness is spelled*.  The former does not
mention `encodeReads`, and `d3Reads` is computed from the run's read set, so the second conjunct
cannot be discharged from the first by any rewrite. -/
theorem check_iff {cb w : Bytes} :
    check cb w = true ↔
      NearSpecV3.D3.RelD3 cb w ∧ encodeReads cb w (Logged.d3Reads cb w) = w := by
  unfold check
  -- `check` binds the *pair* first, then matches the `Except`; after unfolding both `check`
  -- and `canonW`, the pair projection is already reduced to `keys` and `d3Reads cb w`.
  cases he : Logged.checkD3Reads cb w with
  | mk result keys =>
    have hkeys : Logged.d3Reads cb w = keys := by
      unfold Logged.d3Reads
      rw [he]
    rw [hkeys]
    cases result with
    | error e =>
      -- `.error` makes `check` false, and `RelD3` also fails: same run
      have hf := Logged.checkD3Reads_fst cb w
      rw [he] at hf
      simp only [NearSpecV3.D3.RelD3]
      have hck : NearSpecV3.D3.checkD3 cb w = .error e := by
        rw [← hf]
      simp [hck]
    | ok u =>
      cases u
      have hf := Logged.checkD3Reads_fst cb w
      rw [he] at hf
      -- `hf : D3.checkD3 cb w = .ok ()`, which *is* `RelD3` by definition
      have hrel : NearSpecV3.D3.RelD3 cb w := hf.symm
      simp only [hrel, true_and, beq_iff_eq]

/-- **The soundness direction, named for the join.**  Accepting the artifact's proof gives
`RelD3`: this is the premise a non-vacuous join can actually consume, because by `check_iff` it also
carries canonicality that `RelD3` alone does not supply. -/
theorem relD3_of_check {cb w : Bytes} (h : check cb w = true) :
    NearSpecV3.D3.RelD3 cb w :=
  (check_iff.mp h).1

/-- **Cross-check against the pre-existing theorem.**  `check_sound` states the same soundness fact
in terms of `checkD3`; this records that the two agree, so neither path is a shadow of the other. -/
theorem relD3_of_check_via_check_sound {cb w : Bytes} (h : check cb w = true) :
    NearSpecV3.D3.RelD3 cb w :=
  check_sound h

end ReexecV3D3.Read
