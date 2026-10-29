import NearSpecV3.ChunkValidationD1
import NearSpecV3.D0SubD1.Work.Root.Rel
import NearSpecV3.D0SubD1.Work.Root.Phases

/-! Proof notes (the statement and route this lemma was proved against):

Phase A of the D0 ⊆ D1 lockstep (the root assembly). `d0PA`/`d1PA` are the first slice of `checkD0`/`checkD1CoreObs` (claim decode, witness-file decode, the two domain checks) — the two slices are the SAME do-block, only the answer type of the continuation differs (`Unit` vs `Observable`), and `Phases.d0_chain`/`d1_chain` are `rfl` so they are verbatim slices of the source checkers.

GOAL SHAPE: `SIM x y` is `∀ a, x = .ok a → ∃ b, y = .ok b` (`NearSpecV3.D0SubD1.Work.Root.Rel`).

PROOF: `unfold NearSpecV3.D0SubD1.Work.Root.d0PA NearSpecV3.D0SubD1.Work.Root.d1PA`, then peel the four binds with `apply NearSpecV3.D0SubD1.Work.Root.sim_bind_same` (the scrutinee terms of the two sides are *syntactically the same term* — that is the point of the cut), `intro` at each step, and finish with `exact hk _ _`. The two `check` statements are `check b m >>= fun _ => …` on both sides, so `sim_bind_same` covers them.

USEFUL FACTS (`NearSpecV3.D0SubD1.Work.Root.Rel`): `sim_bind_same`, `sim_bind`, `sim_congr`, `sim_check`, `sim_of_eq`, `sim_pure_right`; `NearSpecV3.D0SubD1.Work.Root.Basic`: `bind_ok_exists`.
DO NOT use `dsimp` after `unfold` (it makes no progress); `simp only []` after an `intro` is the way to beta-reduce `let`s. `split` and `trace_state` are available.

This lemma is the cheapest of the five phases: keep it short and general (do not specialise `k`/`k'`).
-/

namespace Work.Phases

open NearSpecV3.D0SubD1.Work.Root (SIM)

/-- **Phase A of the D0 ⊆ D1 lockstep.**  The first slice of `checkD0`/`checkD1CoreObs` — the
claim decode, the witness-file decode and the two domain `check`s — is *literally the same
do-block* on the two sides (`d0PA`/`d1PA` in `NearSpecV3.D0SubD1.Work.Root.Phases` are verbatim slices,
and `d0_chain`/`d1_chain` are `rfl`): only the answer type of the continuation differs (`Unit` on
the D0 side, `Observable` on the D1 side).  So the slice simulates itself as soon as the
continuations do, and the proof is the peeling of its four binds, each of which has *syntactically
the same scrutinee* on the two sides — exactly `NearSpecV3.D0SubD1.Work.Root.sim_bind_same`. -/
theorem PhaseA (cb : NearSpec.Bytes) (wb : NearSpec.Bytes)
    (k : NearSpecV3.Claim → NearSpec.Bytes → Except String Unit)
    (k' : NearSpecV3.Claim → NearSpec.Bytes → Except String NearSpecV3.Observable)
    (hk : ∀ (c : NearSpecV3.Claim) (s : NearSpec.Bytes),
      NearSpecV3.D0SubD1.Work.Root.SIM (k c s) (k' c s)) :
    NearSpecV3.D0SubD1.Work.Root.SIM (NearSpecV3.D0SubD1.Work.Root.d0PA cb wb k)
      (NearSpecV3.D0SubD1.Work.Root.d1PA cb wb k') := by
  unfold NearSpecV3.D0SubD1.Work.Root.d0PA NearSpecV3.D0SubD1.Work.Root.d1PA
  -- statement 1: the claim decode, the same term on both sides
  apply NearSpecV3.D0SubD1.Work.Root.sim_bind_same
  intro c hc
  -- statement 2: the witness-file decode, the same term on both sides
  apply NearSpecV3.D0SubD1.Work.Root.sim_bind_same
  intro sw hsw
  -- statement 3: `check codes.isEmpty …` (its `Unit` value is discarded on both sides)
  apply NearSpecV3.D0SubD1.Work.Root.sim_bind_same
  intro u hu
  -- statement 4: `check (lenT swBytes ≤ 8388608) …`, the same term on both sides
  apply NearSpecV3.D0SubD1.Work.Root.sim_bind_same
  intro u' hu'
  -- the two slices end with `k c swBytes` resp. `k' c swBytes`: the incoming hypothesis
  exact hk c sw.fst hu'

end Work.Phases
