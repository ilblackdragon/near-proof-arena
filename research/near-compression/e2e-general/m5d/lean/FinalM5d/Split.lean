import FinalM5d.HbWhole
import NearSpecV3.E2E.Templates

/-!
# FinalM5d.Split — the FINAL and INIT leaves as joins of lane B's and lane G's parts

Lane E's T1 template system (`NearSpecV3.E2E.Templates`) has one premise per template,
`TmplSound V A Bad k`. The `final` and `init` leaves are each a join of two lanes' tables in one
trace (leaf spec §3, §4 option (a)): FINAL = lane B's FINAL root / M5c (`finK`: post-state root,
implicit transitions, outgoing reassignment) + lane G's tables (`tailNew` + `headerOk`), joined by
the `FinIn` record on a bus; INIT = lane G's INIT (the boundary digests) + lane B's INTAKE (the
intake step), joined by the claim / witness bytes.

**The split (this file's proposal, pending lane E's M11i split in plan §3.5).**

* `FinReach I out t`: `finK`, the checker's `FINAL` first part, succeeds and calls its
  continuation on `t = (root, congestion, outgoing)` (`∀ k, finK … k = k t`) — the split at `t`,
  with no change to the checker.
* **FINAL.** Lane B's premise `FinalBPart`: an accepted joint trace opens its input digest to
  `fin I out` (a non-genesis segment, `I.d2 = none`), `FinReach I out t`, and its `FinIn` bus
  carries `fi` with `FinInOK fi I out t`. Lane G's premise `FinalGPart`: given the `FinIn` bus
  value `fi` and any `(I, out, t)` with `FinInOK`, its output digest opens to `done I.H o` with
  `tailNew afDriver I out t = .ok o` (and `headerOk I.H o`, FinalOut). **`segSoundFinal_join`**:
  both ⇒ lane E's `SegSoundFinal V A Bad` (through `CM.step (.fin I out) = .ok (.done I.H o)`).
  `finalG_of_template` shows what lane G's tables give toward `FinalGPart`
  (`final_template_sound_holds`; open: `ClassF1`/`Computed` from `Holds`, and the `B_out`
  digest — `BOut.lean`).
* **INIT.** Lane G's premise `InitGPart`: the input digest opens to `init cb wb` for the bytes
  `(cb, wb)` its byte stream carries. Lane B's premise `InitBPart`: for the same bytes, `CM.step
  (init cb wb) = .ok c` and the output digest opens to `c`. **`segSoundInit_join`** ⇒
  `SegSoundInit V A Bad`.

The joins are pure logic over lane E's definitions; the two parts are each lane's obligation.
-/

namespace FinalM5d.Split

open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.E2E NearSpecV3.E2E.Bnd NearSpecV3.E2E.T1

/-! ## `finK` splits at `t` -/

/-- **`finK` reaches `t`**: the checker's `FINAL` first part (storage bound, gas cap, main
post-state root, implicit transitions, outgoing reassignment) succeeds and calls its continuation on
`t = (root, congestion, outgoing)` — whatever the continuation. This is lane B's FINAL-root / M5c
obligation; it splits `finK` at `t` with no change to the checker. -/
def FinReach (I : Intake) (out : MainOutD2) (t : Bytes × Congestion × List Rcpt) : Prop :=
  ∀ (β : Type) (k : Bytes × Congestion × List Rcpt → Except String β),
    finK afDriver afCfg.gasCap I out k = k t

/-- A non-genesis `fin` configuration steps to `done I.H o` when `finK` reaches `t` and
`tailNew` computes `o` from it. -/
theorem step_fin {I : Intake} {out : MainOutD2} {t : Bytes × Congestion × List Rcpt} {o : Outputs}
    (hd : I.d2 = none) (hK : FinReach I out t)
    (hT : tailNew afDriver I out t = .ok o) :
    CM.step (.fin I out) = .ok (.done I.H o) := by
  show (finStep I out).map (Conf.done I.H) = _
  unfold finStep
  rw [hd]
  show (finK afDriver afCfg.gasCap I out (tailNew afDriver I out)).map (Conf.done I.H) = _
  rw [hK, hT]; rfl

theorem mfinal_of {I : Intake} {out : MainOutD2} {t : Bytes × Congestion × List Rcpt} {o : Outputs}
    (hd : I.d2 = none) (hK : FinReach I out t)
    (hT : tailNew afDriver I out t = .ok o) :
    MFinal (.base (.fin I out)) (.base (.done I.H o)) :=
  .run trivial (.step (step_fin hd hK hT) (.refl _))

/-! ## FINAL: the two parts and the join -/

section
variable (V : ViewImpl) (A : Airs) (Bad : Prop)
  -- the `FinIn` record carried by the joint trace's `FinIn` bus (the two lanes' tables agree on
  -- it by bus balance; its encoding is leaf spec §2)
  (FinBus : A.Tr .final → (Nat → Nat) → Prop)

/-- **Lane B's part of FINAL** (FINAL root + M5c): the input digest opens to a non-genesis
`fin I out`, `finK` reaches `t`, and the `FinIn` bus carries the projection of `(I, out, t)`. -/
def FinalBPart : Prop :=
  ∀ d d' tr, A.Holds .final d d' tr → Bad ∨ ∃ I out t fi,
    bndOf V.bnd (.base (.fin I out)) = d ∧ I.d2 = none ∧
    FinReach I out t ∧ FinBus tr fi ∧ Tail.FinInOK fi I out t

/-- **Lane G's part of FINAL** (M5d tables): from the `FinIn` bus value and any `(I, out, t)` it
is the projection of, the output digest opens to `done I.H o` with `o` the checker's `tailNew`
output, and FinalOut holds. -/
def FinalGPart : Prop :=
  ∀ d d' tr fi I out t, A.Holds .final d d' tr → FinBus tr fi → Tail.FinInOK fi I out t →
    Bad ∨ ∃ o, tailNew afDriver I out t = .ok o ∧ headerOk I.H o = true ∧
      bndOf V.bnd (.base (.done I.H o)) = d'

/-- **The FINAL leaf is sound** (lane E's `SegSoundFinal`) given both lanes' parts. -/
theorem segSoundFinal_join (hB : FinalBPart V A Bad FinBus) (hG : FinalGPart V A Bad FinBus) :
    SegSoundFinal V A Bad := by
  intro d d' tr h
  rcases hB d d' tr h with hb | ⟨I, out, t, fi, hd, hd2, hK, hbus, hfi⟩
  · exact .inl hb
  rcases hG d d' tr fi I out t h hbus hfi with hb | ⟨o, hT, -, hd'⟩
  · exact .inl hb
  exact .inr ⟨_, _, hd, hd', mfinal_of hd2 hK hT⟩

/-- The FINAL leaf also gives FinalOut on its output configuration (the wrap checks only
`phase = done`, rec. 1(b)(ii)): every opened `done H o` passes `headerOk`. -/
theorem final_join_headerOk (hB : FinalBPart V A Bad FinBus) (hG : FinalGPart V A Bad FinBus)
    {d d' : Bytes} {tr : A.Tr .final} (h : A.Holds .final d d' tr) :
    Bad ∨ ∃ I out o, bndOf V.bnd (.base (.fin I out)) = d ∧
      bndOf V.bnd (.base (.done I.H o)) = d' ∧ MFinal (.base (.fin I out)) (.base (.done I.H o)) ∧
      headerOk I.H o = true := by
  rcases hB d d' tr h with hb | ⟨I, out, t, fi, hd, hd2, hK, hbus, hfi⟩
  · exact .inl hb
  rcases hG d d' tr fi I out t h hbus hfi with hb | ⟨o, hT, hok, hd'⟩
  · exact .inl hb
  exact .inr ⟨I, out, o, hd, hd', mfinal_of hd2 hK hT, hok⟩

end

/-! ## INIT: the two parts and the join -/

section
variable (V : ViewImpl) (A : Airs) (Bad : Prop)
  -- the claim / witness bytes carried by the joint trace's byte stream (INIT's `CLM` rows feed
  -- both INIT's digests and INTAKE's decoder)
  (InitBus : A.Tr .init → Bytes → Bytes → Prop)

/-- **Lane G's part of INIT**: the input digest opens to `init cb wb` for the bytes on the stream
(`claimDigest` and `ctxRoot = ctxD (.raw cb wb)` computed in-circuit; the view's constants for the
other `init` fields). -/
def InitGPart : Prop :=
  ∀ d d' tr, A.Holds .init d d' tr → Bad ∨ ∃ cb wb, InitBus tr cb wb ∧
    bndOf V.bnd (.base (.init cb wb)) = d

/-- **Lane B's part of INIT** (INTAKE): for the bytes on the stream, the intake step succeeds
and the output digest opens to its result. -/
def InitBPart : Prop :=
  ∀ d d' tr cb wb, A.Holds .init d d' tr → InitBus tr cb wb →
    Bad ∨ ∃ c, CM.step (.init cb wb) = .ok c ∧ bndOf V.bnd (.base c) = d'

theorem segSoundInit_join (hG : InitGPart V A Bad InitBus) (hB : InitBPart V A Bad InitBus) :
    SegSoundInit V A Bad := by
  intro d d' tr h
  rcases hG d d' tr h with hb | ⟨cb, wb, hbus, hd⟩
  · exact .inl hb
  rcases hB d d' tr cb wb h hbus with hb | ⟨c, hs, hd'⟩
  · exact .inl hb
  exact .inr ⟨_, _, hd, hd', .intake hs⟩

end

end FinalM5d.Split
