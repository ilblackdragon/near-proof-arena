import WasmBase.Main.TmplPrep

/-!
# Lane E: (H2) a call-machine step keeps a canonical configuration canonical

M12 reduced "honest runs are store-canonical" to two store facts (`E2E/Glue.lean` §6): (H1) every
honest query has store `sfE I`, and **(H2) the call machine keeps stores**. This file proves (H2)
for the whole call machine from lane A's segment-level lemmas (`SegStore.step_resOK`,
`enter_setSt`, `TmplPrep.preConf_canon`, `resetSt_setSt`):

* `run_canon`, `runFrom_canon`: the interpreter keeps the store;
* `sync_canon`, `entPost_canon`: the exit keeps it;
* `afterMethod_canon`, `afterStart_canon`: the call's result `Run` is canonical;
* **`cstep_canon`**: `setArgs σ q = q → setConf σ cc = cc → setConf σ (cstep q cc) = cstep q cc`;
* **`canon_cstep`**: `Glue.canon_wasm`'s premise discharged — `Canon sf (.call I c K q cc) →
  Canon sf (.call I c K q (cstep q cc))`, so every `RStep.wasm` edge keeps canonicity, and with
  `Glue.canon_enter` / `canon_next` an `RCM` run from a canonical configuration whose entered
  queries are canonical (H1) stays canonical (the `.fin r` answers recorded by `next` are
  produced by `cstep`, hence canonical).

Not a lake module (lane E's join file); checked with
`cd research/near-compression/wasm-base-lean && lake env lean ../e2e-general/join/CanonH2.lean`.
Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace LaneE.CanonH2

open NearSpecV3.Wasm hiding P
open NearSpecV3.Wasm.CallCut NearSpecV3.Logged.W
open NearSpecV3.E2E NearSpecV3.E2E.Bnd NearSpecV3.E2E.T1
open NearSpecV3.E2E.SB (setArgs setSt setConf setRes setRun setK setR Canon)

variable {σ : TTN.Store}

theorem step_canon (cfg : NearCfg) (p : Prepared) {s : St} (hs : setSt σ s = s) :
    setRes σ (step cfg p s) = step cfg p s := by
  rw [WasmBase.SegStore.setRes_eq_mapRes]
  exact WasmBase.SegStore.step_resOK cfg p (WasmBase.SegStore.stOK_of σ hs)

theorem run_canon (cfg : NearCfg) (p : Prepared) :
    ∀ (n : Nat) {s : St}, setSt σ s = s → setRes σ (run cfg p n s) = run cfg p n s
  | 0, s, _ => rfl
  | n + 1, s, hs => by
    have h := step_canon cfg p hs
    simp only [run]
    generalize step cfg p s = r at h ⊢
    cases r with
    | cont s' =>
      have hs' : setSt σ s' = s' := by simp only [setRes] at h; injection h
      exact run_canon cfg p n hs'
    | _ => exact h

theorem runFrom_canon (cfg : NearCfg) (p : Prepared) {r : Res} (hr : setRes σ r = r) (n : Nat) :
    setRes σ (runFrom cfg p r n) = runFrom cfg p r n := by
  cases r with
  | cont s =>
    have hs : setSt σ s = s := by simp only [setRes] at hr; injection hr
    exact run_canon cfg p n hs
  | _ => exact hr

theorem sync_canon {s s' : St} (hs : setSt σ s = s) (h : sync s = .ok s') : setSt σ s' = s' := by
  unfold sync at h
  dsimp only at h
  split at h
  · cases h; exact hs
  · split at h
    · cases h
      have hr : s.real.map (NearSpecV3.E2E.SB.setRS σ) = s.real := congrArg St.real hs
      simp only [setSt, hr]
    · cases h

theorem entPost_canon {r : Res} (hr : setRes σ r = r) {s : St} {e : Option String}
    (h : entPost r = .ok (s, e)) : setSt σ s = s := by
  unfold entPost at h
  split at h
  · rename_i s0
    have hs0 : setSt σ s0 = s0 := by simp only [setRes] at hr; injection hr
    cases hsy : sync s0 with
    | error _ => rw [hsy] at h; cases h
    | ok s1 =>
      rw [hsy] at h; cases h
      exact sync_canon hs0 hsy
  · rename_i s0 e0
    have hs0 : setSt σ s0 = s0 := by simp only [setRes] at hr; injection hr
    cases hsy : sync s0 with
    | error _ => rw [hsy] at h; cases h
    | ok s1 =>
      rw [hsy] at h; cases h
      exact sync_canon hs0 hsy
  · cases h
  · cases h

theorem afterMethod_canon {er : Except String (St × Option String)}
    (h : ∀ s e, er = .ok (s, e) → setSt σ s = s) : setRun σ (afterMethod er) = afterMethod er := by
  unfold afterMethod
  split
  · rfl
  · rename_i s e
    simp only [setRun, h s e rfl]

theorem callEntry_canon (cfg : NearCfg) (p : Prepared) (fuel : Nat) {s : St} (hs : setSt σ s = s)
    (fi : Nat) : ∀ s' e, callEntry cfg p fuel s fi = .ok (s', e) → setSt σ s' = s' := by
  intro s' e h
  rw [CallCut.callEntry_eq] at h
  have hr : setSt σ (resetSt s) = resetSt s := by rw [WasmBase.TmplPrep.resetSt_setSt, hs]
  exact entPost_canon (runFrom_canon cfg p (WasmBase.SegStore.enter_setSt p fi hr) fuel) h

theorem afterStart_canon (cfg : NearCfg) (p : Prepared) (fuel mi : Nat)
    {er : Except String (St × Option String)} (h : ∀ s e, er = .ok (s, e) → setSt σ s = s) :
    setRun σ (afterStart cfg p fuel mi er) = afterStart cfg p fuel mi er := by
  unfold afterStart
  split
  · rfl
  · rename_i s e
    simp only [setRun, h s (some e) rfl]
  · rename_i s
    exact afterMethod_canon (callEntry_canon cfg p fuel (h s none rfl) mi)

/-- **(H2) One call-machine step keeps a canonical configuration canonical.** -/
theorem cstep_canon {q : CallArgs} (hq : setArgs σ q = q) {cc : CallConf} (hc : setConf σ cc = cc) :
    setConf σ (cstep q cc) = cstep q cc := by
  cases cc with
  | pre => exact WasmBase.TmplPrep.preConf_canon σ q hq
  | fin r => exact hc
  | ent p k r n =>
    have hr : setRes σ r = r := by simp only [setConf] at hc; injection hc
    cases k with
    | start mi =>
      cases r with
      | cont s =>
        cases n with
        | succ n =>
          have hs : setSt σ s = s := by simp only [setRes] at hr; injection hr
          simp only [cstep, setConf, step_canon q.cfg p hs]
        | zero =>
          simp only [cstep]
          have hr' := runFrom_canon q.cfg p hr 0
          split
          · rename_i s heq
            have hs := entPost_canon hr' heq
            have hs' : setSt σ (resetSt s) = resetSt s := by
              rw [WasmBase.TmplPrep.resetSt_setSt, hs]
            simp only [setConf, WasmBase.SegStore.enter_setSt p mi hs']
          · rename_i er _
            simp only [setConf]
            exact congrArg _ (afterStart_canon q.cfg p q.fuel mi
              (fun s e h => entPost_canon hr' h))
      | _ =>
        simp only [cstep]
        have hr' := runFrom_canon q.cfg p hr n
        split
        · rename_i s heq
          have hs := entPost_canon hr' heq
          have hs' : setSt σ (resetSt s) = resetSt s := by
            rw [WasmBase.TmplPrep.resetSt_setSt, hs]
          simp only [setConf, WasmBase.SegStore.enter_setSt p mi hs']
        · rename_i er _
          simp only [setConf]
          exact congrArg _ (afterStart_canon q.cfg p q.fuel mi (fun s e h => entPost_canon hr' h))
    | method =>
      cases r with
      | cont s =>
        cases n with
        | succ n =>
          have hs : setSt σ s = s := by simp only [setRes] at hr; injection hr
          simp only [cstep, setConf, step_canon q.cfg p hs]
        | zero =>
          simp only [cstep, setConf]
          exact congrArg _ (afterMethod_canon (fun s e h => entPost_canon (runFrom_canon q.cfg p hr 0) h))
      | _ =>
        simp only [cstep, setConf]
        exact congrArg _ (afterMethod_canon (fun s e h => entPost_canon (runFrom_canon q.cfg p hr n) h))

/-- **(H2) in `Glue.canon_wasm`'s form**: an `RStep.wasm` edge keeps canonicity. -/
theorem canon_cstep (sf : NearSpecV3.E2E.Intake → TTN.Store) {I : NearSpecV3.E2E.Intake}
    {c : NearSpecV3.E2E.EConf} {K : List (CallArgs × Run)} {q : CallArgs} {cc : CallConf}
    (hx : Canon sf (.call I c K q cc)) : Canon sf (.call I c K q (cstep q cc)) := by
  simp only [Canon, setR, NearSpecV3.E2E.RConf.call.injEq, true_and] at hx ⊢
  exact ⟨hx.1, hx.2.1, cstep_canon hx.2.1 hx.2.2⟩

end LaneE.CanonH2

#print axioms LaneE.CanonH2.run_canon
#print axioms LaneE.CanonH2.cstep_canon
#print axioms LaneE.CanonH2.canon_cstep
