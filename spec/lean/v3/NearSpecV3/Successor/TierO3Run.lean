import NearSpecV3.Successor.TierO3Walk

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-!
# W12 / O3 step 5g — the engine walk, finished: delayed loop, yield timeouts, main transition, `run`

Continues `TierO3Walk.lean` (`MRQ` with `ND rs.outgoing`, on `env.ctx.layout.WF`):

* `MRX.get_pipe_step`: a `get` whose continuation only updates the pipe (by `FL`, resp. `FU`, with
  `PipeFn FL FU`) before a common continuation. `processDelayedLoop`'s `match (← get).pipe.next`
  is such a read (`pdl_succ`: the loop body with that read as `modifyPipe (stepF ga env rs)`,
  `pipeFn_step`).
* `processDelayedLoop_rr`, `processDelayed_rr`, `yieldLoop_rr`, `applyNewChunkD2_rr`.
* **`run_global`**: `Refines (run w … false p) (run { w with globalActions := true } … true p)` on an
  environment with `env.ctx.layout.WF`, and `run_global_nd`: the lower output's `outgoing` carries
  no distribution receipt.
-/

namespace NearSpecV3.Successor
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Logged NearSpecV3.Wasm StorageExecution HostComm Pipeline

/-! ## A `get` that only steers a pipe update -/

/-- A `get` whose continuation, run from the state it read, is a pipe update followed by a fixed
continuation: the two runs' updates need only be `PipeFn`-related. -/
theorem MRX.get_pipe_step {X : String → Prop} {E : Env → Prop} {α : Type} {Q : α → Prop}
    {f g : Recording → M α} (FL FU : Pipe → Pipe) (k k' : Unit → M α)
    (hf : ∀ r env, f r r env = (StorageExecution.modifyPipe FL >>= k) r env)
    (hg : ∀ r env, g r r env = (StorageExecution.modifyPipe FU >>= k') r env)
    (hF : PipeFn FL FU) (hk : MRX X E Q (k ()) (k' ())) :
    MRX X E Q (get >>= f) (get >>= g) := by
  intro rL rU env hr he
  show ResQ X Q (f rL rL env) (g rU rU env)
  rw [hf, hg]
  exact MRX.bind (MRX.modifyPipe hF) (fun _ _ => hk) rL rU env hr he

/-- The pipe update of `processDelayedLoop`'s `pipe.next` read. -/
def stepF (ga : Bool) (env : Env) (rs : RS) (p : Pipe) : Pipe :=
  match p.next with
  | some n =>
    if (n - 1 == 0) = true then
      schedFn (if ga then fun b => GlobalCodecs.decodeStoredRcptGlobal b "stored receipt"
          else fun b => decodeStoredRcpt b "stored receipt")
        (if ga then globalQueuePolicy.decodeStored else decodeStored)
        env.ctx.layout env.ctx.own rs.o (rs.dq.next - rs.dq.first + 1) rs.dq.first rs.dq.next p
    else { p with next := some (n - 1) }
  | none => p

theorem stepF_unc (ga : Bool) (env : Env) (rs : RS) (p : Pipe) (h : p.uncertain = true) :
    (stepF ga env rs p).uncertain = true := by
  unfold stepF
  split
  · split
    · exact schedFn_unc _ _ _ _ _ _ _ _ p h
    · exact h
  · exact h

theorem pipeFn_step (env : Env) (rs : RS) : PipeFn (stepF false env rs) (stepF true env rs) := by
  refine PipeFn.of_unc (fun p h => stepF_unc false env rs p h) fun p => ?_
  unfold stepF
  split
  · split
    · exact pipeFn_sched _ _ (decLe_storedRcpt _) _ _ decLe_stored _ _ _ _ _ _ p p (PipeRel.refl p)
    · exact Or.inl rfl
  · exact Or.inl rfl

/-- The delayed loop's `pipe.next` read, as one pipe update (both values of `ga`). -/
theorem pdl_get_step (ga : Bool) (env : Env) (rs : RS) {α : Type} (k : Unit → M α) (s : Recording) (e : Env) :
    (match s.pipe.next with
      | some n => if (n - 1 == 0) = true then scheduleDelayed ga env rs >>= k
          else StorageExecution.modifyPipe (fun p => { p with next := some (n - 1) }) >>= k
      | none => k ()) s e =
    (StorageExecution.modifyPipe (stepF ga env rs) >>= k) s e := by
  show _ = k () { s with pipe := stepF ga env rs s.pipe } e
  unfold stepF
  cases hn : s.pipe.next with
  | none => rfl
  | some n =>
    dsimp only
    by_cases hz : (n - 1 == 0) = true
    · rw [if_pos hz, if_pos hz]
      unfold scheduleDelayed pipeDecode schedFn
      cases ga <;> rfl
    · rw [if_neg hz, if_neg hz]; rfl

/-- `processDelayedLoop`'s body with the `pipe.next` read as one pipe update. -/
theorem pdl_succ (fl : Flags) (hooks : NearCfg) (env : Env) (fuel : Nat) (x : RS) :
    processDelayedLoop fl hooks env (fuel + 1) x = (do
      if x.compute ≥ env.ctx.gasLimit || (← softExceeded) then return x
      let (rs, r) ← delayPopR fl.globalActions env (x.dq.next - x.dq.first + 1) x
      match r with
      | none => pure rs
      | some r =>
        StorageExecution.modifyPipe (stepF fl.globalActions env rs)
        if !validReceipt false r then throw (inconsistent "Delayed receipt in the state is invalid")
        let rs ← processWithInstant fl hooks env rs r
        processDelayedLoop fl hooks env fuel rs) := by
  rw [processDelayedLoop.eq_2]
  congr 1; funext b
  split
  · rfl
  congr 1; funext ⟨rs, r⟩
  cases r with
  | none => rfl
  | some r =>
    funext s e
    exact pdl_get_step fl.globalActions env rs _ s e

macro_rules | `(tactic| mrx_close) => `(tactic| with_reducible exact MRX.modifyPipe (pipeFn_step _ _))

/-! ## The delayed loop -/

section walk
variable {E : Env → Prop} (w : NearCfg) (hg : w.globalActions = false) (p : CodeWitnessPolicy)
include hg

theorem processDelayedLoop_rr (env : Env) (hwf : env.ctx.layout.WF) :
    ∀ (fuel : Nat) (rs : RS), ND rs.outgoing →
    MRQ E (fun x : RS => ND x.outgoing)
      (processDelayedLoop ⟨false, p⟩ w env fuel rs)
      (processDelayedLoop ⟨true, p⟩ { w with globalActions := true } env fuel rs)
  | 0, rs, h => by
    rw [processDelayedLoop.eq_1, processDelayedLoop.eq_1]
    exact MRX.pure _ h
  | fuel + 1, rs, h => by
    rw [pdl_succ, pdl_succ]
    mrw
    all_goals exact processDelayedLoop_rr env hwf fuel _ ‹_›

theorem processDelayed_rr (env : Env) (hwf : env.ctx.layout.WF) (fuel : Nat) (rs : RS) (h : ND rs.outgoing) :
    MRQ E (fun x : RS => ND x.outgoing)
      (StorageExecution.processDelayed ⟨false, p⟩ w env fuel rs)
      (StorageExecution.processDelayed ⟨true, p⟩ { w with globalActions := true } env fuel rs) := by
  unfold StorageExecution.processDelayed
  exact MRX.bind (scheduleDelayed_rr env rs) fun _ _ => processDelayedLoop_rr w hg p env hwf fuel rs h

#print axioms MRX.get_pipe_step
#print axioms processDelayedLoop_rr
#print axioms processDelayed_rr

end walk

/-! ## The yield timeouts -/

macro_rules | `(tactic| mrx_close) => `(tactic| with_reducible exact fob_rr _ ‹_› _ _ (by assumption) (nd_data _ _ _ _ _ _))

theorem yieldLoop_rr {E : Env → Prop} (env : Env) (hwf : env.ctx.layout.WF) (next : Nat) :
    ∀ (fuel : Nat) (x : RS × Nat × Nat), ND x.1.outgoing →
    MRQ E (fun y : RS × Nat => ND y.1.outgoing) (StorageExecution.yieldLoop false env next fuel x) (StorageExecution.yieldLoop true env next fuel x)
  | 0, (rs, i, _), h => by
    rw [StorageExecution.yieldLoop.eq_1, StorageExecution.yieldLoop.eq_1]
    exact MRX.pure _ h
  | fuel + 1, (rs, i, k), h => by
    rw [StorageExecution.yieldLoop.eq_2, StorageExecution.yieldLoop.eq_2]
    dsimp only at h
    mrw
    all_goals exact yieldLoop_rr env hwf next fuel _ ‹_›

#print axioms yieldLoop_rr

/-! ## The main transition -/

macro_rules | `(tactic| mrx_close) => `(tactic| with_reducible exact ffb_rr _ ‹_› _ ND.nil)
macro_rules | `(tactic| mrx_close) => `(tactic| with_reducible exact processLocals_rr _ ‹_› _ _ ‹_› _ _ (by assumption))
macro_rules | `(tactic| mrx_close) => `(tactic| with_reducible exact processDelayed_rr _ ‹_› _ _ ‹_› _ _ (by assumption))
macro_rules | `(tactic| mrx_close) => `(tactic| with_reducible exact processIncoming_rr _ ‹_› _ _ ‹_› _ _ (by assumption))
macro_rules | `(tactic| mrx_close) => `(tactic| with_reducible exact yieldLoop_rr _ ‹_› _ _ _ (by assumption))

section main
variable {E : Env → Prop} (w : NearCfg) (hg : w.globalActions = false) (p : CodeWitnessPolicy)
include hg

theorem applyNewChunkD2_rr (prims : Prims) (env : Env) (hwf : env.ctx.layout.WF) (t : PTrie)
    (vu : Option ValidatorUpdateFacts) (props : List (Bytes × Nat)) (incoming : List Rcpt)
    (txs : List (TxD2 × Bool)) (cong : Congestion) :
    MRQ E (fun out : MainOutD2 => ND out.outgoing)
      (StorageExecution.applyNewChunkD2 ⟨false, p⟩ w prims env t vu props incoming txs cong)
      (StorageExecution.applyNewChunkD2 ⟨true, p⟩ { w with globalActions := true } prims env t vu props incoming txs cong) := by
  unfold StorageExecution.applyNewChunkD2
  mrw

#print axioms applyNewChunkD2_rr

/-- The run-level result of `applyNewChunkD2_rr`, from equal initial states. -/
theorem run_resQ (prims : Prims) (env : Env) (hwf : env.ctx.layout.WF) (t : PTrie)
    (vu : Option ValidatorUpdateFacts) (props : List (Bytes × Nat)) (incoming : List Rcpt)
    (txs : List (TxD2 × Bool)) (cong : Congestion) :
    ResQ Exc (fun out : MainOutD2 => ND out.outgoing)
      ((StorageExecution.applyNewChunkD2 ⟨false, p⟩ w prims env t vu props incoming txs cong).run
        { observe := w.observeDetail } env)
      ((StorageExecution.applyNewChunkD2 ⟨true, p⟩ { w with globalActions := true } prims env t vu props incoming txs
        cong).run { observe := w.observeDetail } env) :=
  applyNewChunkD2_rr (E := fun _ => True) w hg p prims env hwf t vu props incoming txs cong _ _ env
    (RecRel.refl _) trivial

/-- **O3, the engine.** On a well-formed layout, the recorder engine with global actions off is
refined by the engine with them on (configuration and flag both switched). -/
theorem run_global (prims : Prims) (env : Env) (hwf : env.ctx.layout.WF) (t : PTrie)
    (vu : Option ValidatorUpdateFacts) (props : List (Bytes × Nat)) (incoming : List Rcpt)
    (txs : List (TxD2 × Bool)) (cong : Congestion) :
    Refines (StorageExecution.run w prims env t vu props incoming txs cong false p)
      (StorageExecution.run { w with globalActions := true } prims env t vu props incoming txs cong true p) := by
  unfold StorageExecution.run
  rcases run_resQ w hg p prims env hwf t vu props incoming txs cong with
    ⟨e, h1, h2⟩ | ⟨e, h1, h2⟩ | ⟨a, sL, sU, h1, h2, _, _⟩
  · right; exact ⟨e, by rw [h1]; rfl, h2⟩
  · left; show Except.map _ _ = Except.map _ _; rw [h1, h2]
  · left; show Except.map _ _ = Except.map _ _; rw [h1, h2]; rfl

/-- **O3, the engine's outgoing receipts.** The lower run's output carries no distribution receipt. -/
theorem run_global_nd (prims : Prims) (env : Env) (hwf : env.ctx.layout.WF) (t : PTrie)
    (vu : Option ValidatorUpdateFacts) (props : List (Bytes × Nat)) (incoming : List Rcpt)
    (txs : List (TxD2 × Bool)) (cong : Congestion) (out : MainOutD2)
    (h : StorageExecution.run w prims env t vu props incoming txs cong false p = .ok out) : ND out.outgoing := by
  unfold StorageExecution.run at h
  rcases run_resQ w hg p prims env hwf t vu props incoming txs cong with
    ⟨e, h1, _⟩ | ⟨e, h1, _⟩ | ⟨a, sL, sU, h1, _, _, hq⟩
  · rw [h1] at h; cases h
  · rw [h1] at h; cases h
  · rw [h1] at h; cases h; exact hq

#print axioms run_global
#print axioms run_global_nd

end main

end NearSpecV3.Successor
