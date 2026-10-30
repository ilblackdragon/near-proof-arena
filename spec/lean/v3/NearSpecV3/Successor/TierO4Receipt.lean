import NearSpecV3.Successor.TierO4Engine

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-!
# W12 / O4 — the per-receipt simulation (`PWISim`), given the per-action one

`TierO4Engine.lean` reduced O4 to `EngineObligations`, whose open field is `PWISim`: the recorder's
`processWithInstant` simulates the legacy one. This module walks the receipt level
(`processWithInstant`, its `drain`, `processWithTotals`, `processReceipt`, `applyActionReceipt`,
`actionLoop`, `emitReceipts`) and reduces `PWISim` to the per-action obligation `ActSim`
(`pwiSim_of_actSim`). The recorder-only steps are bookkeeping (`Book`): `startReceipt`,
`curFail`/`vmErr`/`detail` updates, `pushAttrib`, `modifyPipe`.
-/

namespace NearSpecV3.Successor.O4E
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Logged
open NearSpecV3.Successor
open NearSpecV3.Successor.StorageExecution (M Recording)

/-- The per-action obligation: the recorder's `applyAction` simulates the legacy one. -/
def ActSim (e : Env) (P : Recording → Prop) (cfg : Wasm.NearCfg) : Prop :=
  ∀ (c : ActCtx) (st : ActSt) (act : Act), c.env = e →
    Sim e P (fun p => (p.1.wt (T e), p.2)) (D2.applyAction (D3.d3Hooks cfg) c (st.wt (T e)) act)
      (StorageExecution.applyAction fl0 cfg c st act)

namespace Book
variable {e : Env}

theorem modify_frame (f : Recording → Recording) (h1 : ∀ r, (f r).recorder = r.recorder)
    (h2 : ∀ r, (f r).softLimit = r.softLimit) : Book e (modify f : M Unit) () :=
  fun r => ⟨f r, rfl, h1 r, h2 r⟩

theorem startReceipt : Book e StorageExecution.startReceipt () := modify_frame _ (fun _ => rfl) (fun _ => rfl)

theorem modify_bind {β : Type} (f : Recording → Recording) (h1 : ∀ r, (f r).recorder = r.recorder)
    (h2 : ∀ r, (f r).softLimit = r.softLimit) {g : Unit → M β} {b : β} (hg : Book e (g ()) b) :
    Book e ((modify f : M Unit) >>= g) b := bind (modify_frame f h1 h2) hg

end Book

namespace Sim
variable {e : Env} {P : Recording → Prop}

/-- A recorder-only `if` (its condition is not visible to the legacy side). -/
theorem ite_right {α β : Type} {φ : β → α} (c : Prop) [Decidable c] {x : Except String α} {y y' : M β}
    (h : c → Sim e P φ x y) (h' : ¬c → Sim e P φ x y') : Sim e P φ x (if c then y else y') := by
  by_cases hc : c
  · simp only [hc, ite_true]; exact h hc
  · simp only [hc, ite_false]; exact h' hc

theorem book_modify {α β : Type} {ψ : β → α} {x : Except String α} (hP : PFrame P) (f : Recording → Recording)
    (h1 : ∀ r, (f r).recorder = r.recorder) (h2 : ∀ r, (f r).softLimit = r.softLimit) {g : Unit → M β}
    (h : Sim e P ψ x (g ())) : Sim e P ψ x ((modify f : M Unit) >>= g) :=
  book hP (Book.modify_frame f h1 h2) h

/-- A legacy exclusion is simulated by anything. -/
theorem excl {α β : Type} {φ : β → α} {y : M β} (err : String) (he : isExclusion err = true) :
    Sim e P φ (Except.error err : Except String α) y := fun _ _ => Or.inl he

theorem excl_bind {α α' β : Type} {φ : β → α'} {f : α → Except String α'} {y : M β} (err : String)
    (he : isExclusion err = true) : Sim e P φ ((Except.error err : Except String α) >>= f) y :=
  fun _ _ => Or.inl he

end Sim


set_option hygiene false in
/-- Walk a receipt-level body against its legacy original. -/
macro "o4r_walk" : tactic => `(tactic|
  repeat (first
    | (exact Sim.pure rfl)
    | (exact Sim.ok rfl)
    | (exact Sim.throw _)
    | (exact Sim.error _)
    | (exact throw_bind _)
    | (exact ih _ _ _ (by rfl))
    | (exact ih _ _ (by rfl))
    | (refine Sim.bind_id (Sim.okR _ _) fun _ => ?_)
    | (with_reducible refine Sim.bind (Sim.pure (φ := fun p : Ovl × Nat => (p.1.wt (T e), p.2)) (by with_unfolding_all exact rfl)) fun _ => ?_)
    | (with_reducible refine Sim.bind_id (α := List Rcpt × List Rcpt) (Sim.pure (by with_unfolding_all exact rfl)) fun _ => ?_)
    | (refine Sim.bind_id (Sim.liftE _) fun _ => ?_)
    | (refine Sim.book (c := ()) hP (Book.modify_frame _ (fun _ => rfl) (fun _ => rfl)) ?_)
    | (with_reducible refine Sim.get_all fun _ => ?_)
    | (refine Sim.bind_id (Sim.logged (R_get' _ (by rfl) _ _) hRec) fun _ => ?_)
    | (refine Sim.bind_id (Sim.logged (R_getAcct' _ (by first | rfl | (split <;> rfl)) _) hRec) fun _ => ?_)
    | (refine Sim.bind_id (Sim.logged (R_contains' _ (by rfl) _ _) hRec) fun _ => ?_)
    | (refine Sim.book (c := ()) hP Book.startReceipt ?_)
    | (refine Sim.book (c := ()) hP (Book.modifyPipe _) ?_)
    | (refine Sim.book (c := ()) hP (Book.modifyDetail _) ?_)
    | (refine Sim.bind (sim_actionLoop cfg hP hAct _ _ _ _ _ _ _ _ _ (by rfl)) fun _ => ?_)
    | (with_reducible refine Sim.bind (Sim.pure (φ := fun o : Ovl => o.wt (T e)) (by with_unfolding_all exact rfl)) fun _ => ?_)
    | (refine Sim.bind (Sim.foldlM' (φ := fun p : Ovl × Nat => (p.1.wt (T e), p.2)) (fun _ _ => ?_) _ rfl) fun _ => ?_)
    | (refine Sim.bind (sim_applyActionReceipt cfg hP hRec hAct _ _ _ _ (by rfl)) fun _ => ?_)
    | (exact Sim.excl _ (by decide))
    | (exact Sim.excl_bind _ (by decide))
    | (refine Sim.bind (sim_emitReceipts hRec _ _ _ _ _ (by rfl)) fun _ => ?_)
    | (refine Sim.ite _ (fun _ => ?_) (fun _ => ?_))
    | (refine Sim.ite_right _ (fun _ => ?_) (fun _ => ?_))
    | (split <;> (rename_i hsplit; (try dsimp only at hsplit); (try simp only [hsplit]); (try dsimp only)))))

section walk
variable {e : Env} {P : Recording → Prop}

theorem sim_emitReceipts
    (hRec : ∀ r keys, P r → P { r with recorder := recordReads e keys r.recorder }) (parent : Bytes) :
    ∀ (rs rsO : RS) (k : Nat) (l : List Rcpt), rsO = rs.wt (T e) →
    Sim e P (fun p => (p.1.wt (T e), p.2)) (D2.emitReceipts e parent rsO k l)
      (StorageExecution.emitReceipts false e parent rs k l)
  | rs, rsO, k, [], h => by
    subst h; unfold D2.emitReceipts StorageExecution.emitReceipts; exact Sim.ok rfl
  | rs, rsO, k, nr :: rest, h => by
    subst h
    have ih := fun rs k => sim_emitReceipts hRec parent rs (rs.wt (T e)) k rest rfl
    unfold D2.emitReceipts StorageExecution.emitReceipts
    simp only [StorageExecution.forwardOrBufferR, Bool.false_eq_true, ↓reduceIte]
    refine Sim.ite _ (fun _ => ?_) (fun _ => ?_)
    · refine Sim.bind (φ := fun x : RS => x.wt (T e)) (Sim.pure rfl) fun rs' => ?_
      refine Sim.bind (ih rs' (k + 1)) fun p => ?_
      exact Sim.pure rfl
    · refine Sim.bind (Sim.logged (R_forwardOrBuffer' _ (by rfl) _ (by rfl) _) hRec) fun rs' => ?_
      refine Sim.bind (ih rs' (k + 1)) fun p => ?_
      exact Sim.pure rfl

theorem sim_actionLoop (cfg : Wasm.NearCfg) (hP : PFrame P) (hAct : ActSim e P cfg)
    (r : Rcpt) (a : ActionR) (inputs : List (Option Bytes)) (deployed attempted : List Bytes) :
    ∀ (i : Nat) (acts : List Act) (acc : ActSt × AR) (accO : ActSt × AR), accO = (acc.1.wt (T e), acc.2) →
    Sim e P (fun p => (p.1.wt (T e), p.2))
      (D2.actionLoop (D3.d3Hooks cfg) e r a inputs deployed attempted i acts accO)
      (StorageExecution.actionLoop fl0 cfg e r a inputs deployed attempted i acts acc)
  | i, [], acc, accO, h => by
    subst h; unfold D2.actionLoop StorageExecution.actionLoop; exact Sim.ok rfl
  | i, act :: rest, (st, res), accO, h => by
    subst h
    have ih := sim_actionLoop cfg hP hAct r a inputs deployed attempted (i + 1) rest
    unfold D2.actionLoop StorageExecution.actionLoop
    simp only []
    refine Sim.book (c := ()) hP (Book.modify_frame _ (fun _ => rfl) (fun _ => rfl)) ?_
    refine Sim.bind (hAct _ _ _ rfl) fun p => ?_
    rcases p with ⟨st', ar⟩
    dsimp only
    o4r_walk
    all_goals done

theorem sim_applyActionReceipt (cfg : Wasm.NearCfg) (hP : PFrame P)
    (hRec : ∀ r keys, P r → P { r with recorder := recordReads e keys r.recorder }) (hAct : ActSim e P cfg)
    (rs rsO : RS) (r : Rcpt) (a : ActionR) (h : rsO = rs.wt (T e)) :
    Sim e P (fun p => (p.1.wt (T e), p.2)) (D2.applyActionReceipt (D3.d3Hooks cfg) e rsO r a)
      (StorageExecution.applyActionReceipt fl0 cfg e rs r a) := by
  subst h
  unfold D2.applyActionReceipt StorageExecution.applyActionReceipt
  simp only [StorageExecution.getR, StorageExecution.getAcctR]
  refine Sim.bind (φ := fun p : Ovl × List (Option Bytes) => (p.1.wt (T e), p.2))
    (Sim.foldlM' (fun b c => ?_) _ rfl) fun p => ?_
  · rcases b with ⟨o, ins⟩
    dsimp only
    o4r_walk
    all_goals done
  · rcases p with ⟨o, ins⟩
    dsimp only
    o4r_walk
    all_goals done

theorem sim_processReceipt (cfg : Wasm.NearCfg) (hP : PFrame P)
    (hRec : ∀ r keys, P r → P { r with recorder := recordReads e keys r.recorder }) (hAct : ActSim e P cfg)
    (rs rsO : RS) (r : Rcpt) (h : rsO = rs.wt (T e)) :
    Sim e P (fun p => (p.1.wt (T e), p.2)) (D2.processReceipt (D3.d3Hooks cfg) e rsO r)
      (StorageExecution.processReceipt fl0 cfg e rs r) := by
  subst h
  unfold D2.processReceipt StorageExecution.processReceipt
  simp only [StorageExecution.getR, StorageExecution.containsR, StorageExecution.decodeStoredRcptR,
    Bool.false_eq_true, ↓reduceIte, Bool.not_false]
  o4r_walk
  all_goals o4r_walk
  all_goals done

theorem sim_processWithTotals (cfg : Wasm.NearCfg) (hP : PFrame P)
    (hRec : ∀ r keys, P r → P { r with recorder := recordReads e keys r.recorder }) (hAct : ActSim e P cfg)
    (rs rsO : RS) (r : Rcpt) (h : rsO = rs.wt (T e)) :
    Sim e P (·.wt (T e)) (D2.processWithTotals (D3.d3Hooks cfg) e rsO r)
      (StorageExecution.processWithTotals fl0 cfg e rs r) := by
  subst h
  unfold D2.processWithTotals StorageExecution.processWithTotals
  refine Sim.book (c := ()) hP (Book.modifyPipe _) ?_
  refine Sim.bind (sim_processReceipt cfg hP hRec hAct _ _ _ rfl) fun p => ?_
  rcases p with ⟨rs', o⟩
  dsimp only
  o4r_walk
  all_goals done

theorem sim_drain (cfg : Wasm.NearCfg) (hP : PFrame P)
    (hRec : ∀ r keys, P r → P { r with recorder := recordReads e keys r.recorder }) (hAct : ActSim e P cfg) :
    ∀ (fuel : Nat) (rs rsO : RS), rsO = rs.wt (T e) →
    Sim e P (·.wt (T e)) (D2.processWithInstant.drain (D3.d3Hooks cfg) e fuel rsO)
      (StorageExecution.processWithInstant.drain fl0 cfg e fuel rs)
  | 0, rs, rsO, h => by
    unfold D2.processWithInstant.drain StorageExecution.processWithInstant.drain; exact Sim.error _
  | fuel + 1, rs, rsO, h => by
    subst h
    unfold D2.processWithInstant.drain StorageExecution.processWithInstant.drain
    dsimp only
    have hi : (rs.wt (T e)).instant = rs.instant := rfl
    rw [hi]
    cases rs.instant with
    | nil => exact Sim.ok rfl
    | cons ir more =>
      exact Sim.bind (sim_processWithTotals cfg hP hRec hAct _ _ _ rfl) fun rs' =>
        sim_drain cfg hP hRec hAct fuel rs' _ rfl

/-- **Step 1.** The per-receipt obligation `PWISim` from the per-action one. -/
theorem pwiSim_of_actSim (cfg : Wasm.NearCfg) (hP : PFrame P)
    (hRec : ∀ r keys, P r → P { r with recorder := recordReads e keys r.recorder }) (hAct : ActSim e P cfg) :
    PWISim e P cfg := by
  intro rs rsO r h
  subst h
  unfold D2.processWithInstant StorageExecution.processWithInstant
  exact Sim.bind (sim_processWithTotals cfg hP hRec hAct _ _ _ rfl) fun rs' =>
    sim_drain cfg hP hRec hAct _ rs' _ rfl


/-! ## Step 2: the action dispatch

`StorageExecution.applyAction` against `D2.applyAction (D3.d3Hooks cfg)`: non-call, non-global
actions are `ordinaryAction` = the logged D2 action (`R_applyAction` with the D2 hooks, which agree
with the D3 hooks off the `FunctionCall` arm) followed by `accountRemovals`, which raises the
recorder size by `2000 ·` the ContractData removals of the step (G1). The function call is the
hook obligation `FCSim`; the global actions are `GlobalSim` (finding G7). -/

/-- The hook obligation of a `FunctionCall` (step 3). -/
def FCSim (e : Env) (P : Recording → Prop) (cfg : Wasm.NearCfg) : Prop :=
  ∀ (c : ActCtx) (st : ActSt) (res : AR) (m args : Bytes) (g d : Nat), c.env = e →
    Sim e P (fun p => (p.1.wt (T e), p.2)) (D3.functionCallD3 cfg c (st.wt (T e)) res (.fcall m args g d))
      (try StorageExecution.functionCallRecorded fl0 cfg c st res (.fcall m args g d)
       catch err => throw (if err.startsWith "unmodeled" then D3.oodE err else err) : M (ActSt × AR))

/-- **G7.** A global action (`deployGlobal`, `useGlobal`, `stateInit`). The legacy engine first runs
the existence and permission checks (a failed check is an action failure, `(st, res.fail)`) and only
then excludes (`w.shape`); the recorder with `globalActions = false` excludes at once
(`applyGlobal`). Where a check fails the two differ, so this is not provable for every value; it
holds on every reachable value because the D2 decoders, `finishActs` and the transaction
conversion never build a global action (`pBase` rejects the tags with a `w.shape` exclusion). -/
def GlobalSim (e : Env) (P : Recording → Prop) (cfg : Wasm.NearCfg) : Prop :=
  ∀ (c : ActCtx) (st : ActSt) (raw : Bytes) (b : Base), c.env = e →
    (b matches .deployGlobal _ | .useGlobal _ | .stateInit _) →
    Sim e P (fun p => (p.1.wt (T e), p.2)) (D2.applyAction (D3.d3Hooks cfg) c (st.wt (T e)) (.base ⟨raw, b⟩))
      (StorageExecution.applyGlobal false c st (.base ⟨raw, b⟩) b)

/-- `P` is kept by raising the recorder size (the removal accounting, G1). -/
def RemClosed (P : Recording → Prop) : Prop :=
  ∀ r (n : Nat), P r → P { r with recorder := { r.recorder with size := r.recorder.size + n } }

theorem actCtx_ws {c : ActCtx} {e : Env} (hc : c.env = e) : c.ws e.store = c := by
  cases c; simp only at hc; subst hc; rfl

/-- A non-call, non-global action: the logged D2 action plus the removal accounting. -/
theorem sim_ordinary (hRec : ∀ r keys, P r → P { r with recorder := recordReads e keys r.recorder })
    (hRem : RemClosed P) (c : ActCtx) (st : ActSt) (act : Act) (hc : c.env = e) :
    Sim e P (fun p => (p.1.wt (T e), p.2)) (D2.applyAction D2.d2Hooks c (st.wt (T e)) act)
      (StorageExecution.ordinaryAction c st act) := by
  have hR := R_applyAction (s := e.store) (root := e.preRoot) D2.d2Hooks D2.d2HooksL e.store
    (HooksR_d2 e.store) c st act
  rw [actCtx_ws hc] at hR
  intro r hr
  have h1 := Sim.logged (P := P) hR hRec r hr
  unfold SimAt at h1 ⊢
  unfold StorageExecution.ordinaryAction
  rw [Sim.run_bind]
  cases hx : D2.applyAction D2.d2Hooks c (st.wt (T e)) act with
  | error err =>
    rw [hx] at h1
    rcases h1 with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [h]; rfl)
  | ok a =>
    rw [hx] at h1
    obtain ⟨b, r', hy, hab, hr'⟩ := h1
    rw [hy]
    exact ⟨b, _, rfl, hab, hRem r' _ hr'⟩

/-- **Step 2.** The per-action obligation from the hook obligation, the global-action obligation
(G7) and the removal closure (G1). -/
theorem actSim_of (cfg : Wasm.NearCfg)
    (hRec : ∀ r keys, P r → P { r with recorder := recordReads e keys r.recorder })
    (hRem : RemClosed P) (hFC : FCSim e P cfg) (hGl : GlobalSim e P cfg) : ActSim e P cfg := by
  intro c st act hc
  cases act with
  | delegate raw d =>
    exact Sim.congr_left rfl (sim_ordinary hRec hRem c st _ hc)
  | base ba =>
    rcases ba with ⟨raw, b⟩
    cases b with
    | fcall m args g d =>
      unfold D2.applyAction StorageExecution.applyAction
      dsimp only
      refine Sim.ite _ (fun _ => Sim.pure rfl) (fun _ => ?_)
      refine Sim.ite _ (fun _ => Sim.pure rfl) (fun _ => ?_)
      exact hFC c st _ m args g d hc
    | deployGlobal x =>
      unfold StorageExecution.applyAction; exact hGl c st raw _ hc rfl
    | useGlobal x =>
      unfold StorageExecution.applyAction; exact hGl c st raw _ hc rfl
    | stateInit x =>
      unfold StorageExecution.applyAction; exact hGl c st raw _ hc rfl
    | _ => exact Sim.congr_left rfl (sim_ordinary hRec hRem c st _ hc)


/-- **The obligations' design flaw (G1), formally.** The removal closure that the per-action step needs
(`RemClosed`, a ContractData removal raises the recorder size by `2000 ·` its count, for every value)
and the soft-limit field `soft` of `EngineObligations` cannot hold together for an inhabited `P`. A
receipt that removes enough ContractData keys exists for every bound, so `PWISim` with a `P` bounded
by `soft` is false: §12's `EngineObligations` is unsatisfiable, and its tier theorem vacuous. The
soft-limit argument needs the coupling of the recorder size with the value's `cdRemovals`, or a
run-level premise (README §13). -/
theorem remClosed_soft_absurd {P : Recording → Prop} (hRem : RemClosed P)
    (hSoft : ∀ r, P r → r.recorder.size ≤ r.softLimit) (r : Recording) (hr : P r) : False := by
  have h := hSoft _ (hRem r (r.softLimit + 1) hr)
  simp only at h
  omega

/-- Steps 1–2 composed: `PWISim` from the hook (`FCSim`), global-action (`GlobalSim`, G7) and
removal (`RemClosed`, G1) obligations. -/
theorem pwiSim_of (cfg : Wasm.NearCfg) (hP : PFrame P)
    (hRec : ∀ r keys, P r → P { r with recorder := recordReads e keys r.recorder })
    (hRem : RemClosed P) (hFC : FCSim e P cfg) (hGl : GlobalSim e P cfg) : PWISim e P cfg :=
  pwiSim_of_actSim cfg hP hRec (actSim_of cfg hRec hRem hFC hGl)

end walk

#print axioms pwiSim_of_actSim
#print axioms actSim_of
#print axioms pwiSim_of
#print axioms remClosed_soft_absurd

end NearSpecV3.Successor.O4E
