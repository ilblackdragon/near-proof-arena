import NearSpecV3.Successor.TierWhole

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-! # W12 — the walk of the recorder engine (`MRef`) -/

namespace NearSpecV3.Successor
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Wasm StorageExecution

/-! ## The walk -/

/-- `applyAction`'s handler keeps an exclusion an exclusion. -/
theorem unmodeledHandler_ex (e : String) (he : isExclusion e = true) (r : Recording) (env : Env) :
    ∃ e', (throw (if e.startsWith "unmodeled" then D3.oodE e else e) : StorageExecution.M (ActSt × AR))
      r env = .error e' ∧ isExclusion e' = true := by
  split
  · exact ⟨_, rfl, oodE_isExclusion e⟩
  · exact ⟨_, rfl, he⟩

syntax "rk_close" : tactic
macro_rules | `(tactic| rk_close) => `(tactic| exact (‹RecRefine _ _› _ _ _ _))

macro "rec_lockstep" : tactic => `(tactic|
  repeat (first
    | (with_reducible exact MRef.refl _)
    | (exact MRef.throw_bind_same _ _ _)
    | rk_close
    | (refine MRef.tryCatch _ (by rk_close) (fun e he => unmodeledHandler_ex e he))
    | ((refine MRef.bind (by rk_close) fun (_, _) => ?_); try dsimp only)
    | ((refine MRef.bind (by rk_close) fun _ => ?_); try dsimp only)
    | ((refine MRef.bind (MRef.foldlM _ _ fun _ _ => ?_) fun _ => ?_); try dsimp only)
    | ((refine MRef.foldlM _ _ fun _ _ => ?_); try dsimp only)
    | ((refine MRef.bind (by with_reducible exact MRef.refl _) fun (_, _) => ?_); try dsimp only)
    | ((refine MRef.bind (by with_reducible exact MRef.refl _) fun _ => ?_); try dsimp only)
    | (refine MRef.ite_congr _ (fun _ => ?_) (fun _ => ?_))
    | (split <;> (rename_i hsplit; (try simp only [hsplit]); (try dsimp only)))))

theorem applyAction_rec_mono {cfg cfg' : NearCfg} (hh : RecRefine cfg cfg') (c : ActCtx) (st : ActSt)
    (a : Act) : MRef (StorageExecution.applyAction cfg c st a) (StorageExecution.applyAction cfg' c st a) := by
  unfold StorageExecution.applyAction
  rec_lockstep
  all_goals rec_lockstep
  all_goals first | with_reducible exact MRef.refl _

macro_rules | `(tactic| rk_close) => `(tactic| with_reducible exact applyAction_rec_mono ‹_› _ _ _)

theorem actionLoop_rec_mono {cfg cfg' : NearCfg} (hh : RecRefine cfg cfg') (env : Env) (r : Rcpt)
    (a : ActionR) (inputs : List (Option Bytes)) (deployed attempted : List Bytes) (i : Nat)
    (acts : List Act) (acc : ActSt × AR) :
    MRef (StorageExecution.actionLoop cfg env r a inputs deployed attempted i acts acc)
      (StorageExecution.actionLoop cfg' env r a inputs deployed attempted i acts acc) := by
  induction acts generalizing i acc with
  | nil => exact MRef.refl _
  | cons act rest ih =>
    obtain ⟨st, res⟩ := acc
    unfold StorageExecution.actionLoop
    rec_lockstep
    all_goals rec_lockstep
    all_goals first | exact ih _ _ | with_reducible exact MRef.refl _

macro_rules | `(tactic| rk_close) => `(tactic| with_reducible exact actionLoop_rec_mono ‹_› _ _ _ _ _ _ _ _ _)

theorem applyActionReceipt_rec_mono {cfg cfg' : NearCfg} (hh : RecRefine cfg cfg') (env : Env)
    (rs : RS) (r : Rcpt) (a : ActionR) :
    MRef (StorageExecution.applyActionReceipt cfg env rs r a)
      (StorageExecution.applyActionReceipt cfg' env rs r a) := by
  unfold StorageExecution.applyActionReceipt
  rec_lockstep
  all_goals rec_lockstep
  all_goals first | with_reducible exact MRef.refl _

macro_rules | `(tactic| rk_close) => `(tactic| with_reducible exact applyActionReceipt_rec_mono ‹_› _ _ _ _)

theorem processReceipt_rec_mono {cfg cfg' : NearCfg} (hh : RecRefine cfg cfg') (env : Env)
    (rs : RS) (r : Rcpt) :
    MRef (StorageExecution.processReceipt cfg env rs r) (StorageExecution.processReceipt cfg' env rs r) := by
  unfold StorageExecution.processReceipt
  rec_lockstep
  all_goals rec_lockstep
  all_goals first | with_reducible exact MRef.refl _

macro_rules | `(tactic| rk_close) => `(tactic| with_reducible exact processReceipt_rec_mono ‹_› _ _ _)

theorem processWithTotals_rec_mono {cfg cfg' : NearCfg} (hh : RecRefine cfg cfg') (env : Env)
    (rs : RS) (r : Rcpt) :
    MRef (StorageExecution.processWithTotals cfg env rs r)
      (StorageExecution.processWithTotals cfg' env rs r) := by
  unfold StorageExecution.processWithTotals
  rec_lockstep
  all_goals rec_lockstep
  all_goals first | with_reducible exact MRef.refl _

macro_rules | `(tactic| rk_close) => `(tactic| with_reducible exact processWithTotals_rec_mono ‹_› _ _ _)

theorem processWithInstant_drain_rec_mono {cfg cfg' : NearCfg} (hh : RecRefine cfg cfg') (env : Env)
    (fuel : Nat) (rs : RS) :
    MRef (StorageExecution.processWithInstant.drain cfg env fuel rs)
      (StorageExecution.processWithInstant.drain cfg' env fuel rs) := by
  induction fuel generalizing rs with
  | zero => exact MRef.refl _
  | succ n ih =>
    unfold StorageExecution.processWithInstant.drain
    rec_lockstep
    all_goals rec_lockstep
    all_goals first | exact ih _ | with_reducible exact MRef.refl _

macro_rules | `(tactic| rk_close) => `(tactic| with_reducible exact processWithInstant_drain_rec_mono ‹_› _ _ _)

theorem processWithInstant_rec_mono {cfg cfg' : NearCfg} (hh : RecRefine cfg cfg') (env : Env)
    (rs : RS) (r : Rcpt) :
    MRef (StorageExecution.processWithInstant cfg env rs r)
      (StorageExecution.processWithInstant cfg' env rs r) := by
  unfold StorageExecution.processWithInstant
  rec_lockstep
  all_goals rec_lockstep
  all_goals first | with_reducible exact MRef.refl _

macro_rules | `(tactic| rk_close) => `(tactic| with_reducible exact processWithInstant_rec_mono ‹_› _ _ _)

theorem processLocals_rec_mono {cfg cfg' : NearCfg} (hh : RecRefine cfg cfg') (env : Env)
    (rs : RS) (l : List Rcpt) :
    MRef (StorageExecution.processLocals cfg env rs l) (StorageExecution.processLocals cfg' env rs l) := by
  unfold StorageExecution.processLocals
  rec_lockstep
  all_goals rec_lockstep
  all_goals first | with_reducible exact MRef.refl _

theorem processDelayedLoop_rec_mono {cfg cfg' : NearCfg} (hh : RecRefine cfg cfg') (env : Env)
    (fuel : Nat) (rs : RS) :
    MRef (StorageExecution.processDelayedLoop cfg env fuel rs)
      (StorageExecution.processDelayedLoop cfg' env fuel rs) := by
  induction fuel generalizing rs with
  | zero => exact MRef.refl _
  | succ n ih =>
    unfold StorageExecution.processDelayedLoop
    rec_lockstep
    all_goals rec_lockstep
    all_goals first | exact ih _ | with_reducible exact MRef.refl _

macro_rules | `(tactic| rk_close) => `(tactic| with_reducible exact processDelayedLoop_rec_mono ‹_› _ _ _)

theorem processDelayed_rec_mono {cfg cfg' : NearCfg} (hh : RecRefine cfg cfg') (env : Env)
    (fuel : Nat) (rs : RS) :
    MRef (StorageExecution.processDelayed cfg env fuel rs)
      (StorageExecution.processDelayed cfg' env fuel rs) := by
  unfold StorageExecution.processDelayed
  rec_lockstep
  all_goals rec_lockstep
  all_goals first | with_reducible exact MRef.refl _

theorem processIncoming_rec_mono {cfg cfg' : NearCfg} (hh : RecRefine cfg cfg') (env : Env)
    (rs : RS) (l : List Rcpt) :
    MRef (StorageExecution.processIncoming cfg env rs l)
      (StorageExecution.processIncoming cfg' env rs l) := by
  unfold StorageExecution.processIncoming
  rec_lockstep
  all_goals rec_lockstep
  all_goals first | with_reducible exact MRef.refl _

macro_rules | `(tactic| rk_close) => `(tactic| with_reducible exact processLocals_rec_mono ‹_› _ _ _)
macro_rules | `(tactic| rk_close) => `(tactic| with_reducible exact processDelayed_rec_mono ‹_› _ _ _)
macro_rules | `(tactic| rk_close) => `(tactic| with_reducible exact processIncoming_rec_mono ‹_› _ _ _)

theorem applyNewChunkD2_rec_mono {cfg cfg' : NearCfg} (hh : RecRefine cfg cfg') (prims : Prims)
    (env : Env) (t : PTrie) (vu : Option ValidatorUpdateFacts) (lastProps : List (Bytes × Nat))
    (incoming : List Rcpt) (txs : List (TxD2 × Bool)) (ownCong : Congestion) :
    MRef (StorageExecution.applyNewChunkD2 cfg prims env t vu lastProps incoming txs ownCong)
      (StorageExecution.applyNewChunkD2 cfg' prims env t vu lastProps incoming txs ownCong) := by
  unfold StorageExecution.applyNewChunkD2
  rec_lockstep
  all_goals rec_lockstep
  all_goals first | with_reducible exact MRef.refl _

/-- **The recorder engine is monotone in its recorded call.** -/
theorem run_rec_mono {cfg cfg' : NearCfg} (hh : RecRefine cfg cfg') (prims : Prims) (env : Env)
    (t : PTrie) (vu : Option ValidatorUpdateFacts) (props : List (Bytes × Nat)) (incoming : List Rcpt)
    (txs : List (TxD2 × Bool)) (congestion : Congestion) (globals : Bool) (policy : CodeWitnessPolicy) :
    Refines (StorageExecution.run cfg prims env t vu props incoming txs congestion globals policy)
      (StorageExecution.run cfg' prims env t vu props incoming txs congestion globals policy) :=
  Refines.map _ (applyNewChunkD2_rec_mono hh prims env t vu props incoming txs congestion _ env)

/-! ## Shells: monotone in the driver's main transition

The whole-state shells pass the hooks to `driver.apply` and nowhere else. Replacing `apply` by a
refining one (`ApplyRefine`) refines the shell. -/

/-- The type of `ExecutionDriver.apply`. -/
abbrev ApplyFn := ActionHooks → Prims → Env → PTrie → Option ValidatorUpdateFacts →
    List (Bytes × Nat) → List Rcpt → List (TxD2 × Bool) → Congestion → Except String MainOutD2

def ApplyRefine (ap ap' : ApplyFn) (h h' : ActionHooks) : Prop :=
  ∀ p e t vu ps rs txs cg, Refines (ap h p e t vu ps rs txs cg) (ap' h' p e t vu ps rs txs cg)

macro "shell_lockstep" : tactic => `(tactic|
  repeat (first
    | (with_reducible exact Refines.refl _)
    | (exact Refines.throw_bind _ _ _)
    | ((refine Refines.bind (‹ApplyRefine _ _ _ _› _ _ _ _ _ _ _ _) fun _ => ?_); try dsimp only)
    | (exact ‹ApplyRefine _ _ _ _› _ _ _ _ _ _ _ _)
    | ((refine Refines.bind' (by with_reducible rfl) fun (_, _) => ?_); try dsimp only)
    | ((refine Refines.bind' (by with_reducible rfl) fun _ => ?_); try dsimp only)
    | (refine Refines.ite_bind_join _ _ _ fun _ => ?_)
    | (refine Refines.ite_bind_skip _ _ ?_)
    | (refine Refines.ite_congr _ (fun _ => ?_) (fun _ => ?_))
    | ((refine Refines.bind (by with_reducible assumption) fun _ => ?_); try dsimp only)
    | ((refine Refines.bind (Refines.forIn_congr _ _ fun _ _ => ?_) fun _ => ?_); try dsimp only)
    | ((refine Refines.bind' (by rfl) fun (_, _) => ?_); try dsimp only)
    | ((refine Refines.bind' (by rfl) fun _ => ?_); try dsimp only)
    | (split <;> (rename_i hsplit; (try simp only [hsplit]); (try dsimp only)))))

theorem checkD2CoreWithObs_apply_mono (d : ExecutionDriver) (ap' : ApplyFn) (h h' : ActionHooks)
    (hap : ApplyRefine d.apply ap' h h') (a : Bool) (c w : Bytes) (g : Option Nat) :
    Refines (checkD2CoreWithObs d h a c w g) (checkD2CoreWithObs { d with apply := ap' } h' a c w g) := by
  unfold checkD2CoreWithObs
  dsimp only
  shell_lockstep
  all_goals shell_lockstep

theorem checkD2CoreWith_apply_mono (d : ExecutionDriver) (ap' : ApplyFn) (h h' : ActionHooks)
    (hap : ApplyRefine d.apply ap' h h') (a : Bool) (c w : Bytes) (g : Option Nat) :
    Refines (checkD2CoreWith d h a c w g) (checkD2CoreWith { d with apply := ap' } h' a c w g) :=
  Refines.map _ (checkD2CoreWithObs_apply_mono d ap' h h' hap a c w g)

set_option maxHeartbeats 16000000 in
theorem checkD2CoreGWith_apply_mono (d : ExecutionDriver) (ap' : ApplyFn) (h h' : ActionHooks)
    (hap : ApplyRefine d.apply ap' h h') (a : Bool) (c w : Bytes) (g : Option Nat) :
    Refines (checkD2CoreGWith d h a c w g) (checkD2CoreGWith { d with apply := ap' } h' a c w g) := by
  have hW := checkD2CoreWith_apply_mono d ap' h h' hap a c w g
  obtain ⟨ap, so, dw, rsh, vr, ogr, rs, seg, wu, lu, crc, cw, bl, ik, sa⟩ := d
  dsimp only at hW hap
  unfold checkD2CoreGWith
  dsimp only
  refines_lockstep
  all_goals shell_lockstep

set_option maxHeartbeats 16000000 in
theorem checkReshardCoreObs_apply_mono (d : ExecutionDriver) (ap' : ApplyFn) (h h' : ActionHooks)
    (hap : ApplyRefine d.apply ap' h h') (a : Bool) (c w : Bytes) (g : Option Nat) :
    Refines (checkReshardCoreObs d h a c w g) (checkReshardCoreObs { d with apply := ap' } h' a c w g) := by
  unfold checkReshardCoreObs
  dsimp only
  shell_lockstep
  all_goals shell_lockstep

theorem checkReshardCore_apply_mono (d : ExecutionDriver) (ap' : ApplyFn) (h h' : ActionHooks)
    (hap : ApplyRefine d.apply ap' h h') (a : Bool) (c w : Bytes) (g : Option Nat) :
    Refines (checkReshardCore d h a c w g) (checkReshardCore { d with apply := ap' } h' a c w g) :=
  Refines.map _ (checkReshardCoreObs_apply_mono d ap' h h' hap a c w g)

/-! ## Configuration level: the whole-state engine -/

/-- The recorder engine's `apply` refines when its recorded calls do. -/
theorem recorder_applyRefine {w w' : NearCfg} (hh : RecRefine w w') (g : Bool) (p : CodeWitnessPolicy)
    (h h' : ActionHooks) :
    ApplyRefine (recorderDriver w g p).apply (recorderDriver w' g p).apply h h' :=
  fun prims e t vu ps rs txs cg => run_rec_mono hh prims e t vu ps rs txs cg g p

theorem recRefine_floats (w : NearCfg) : RecRefine w { w with floats := true } := by
  refine recRefine_of_vmRel fun code => ?_
  rcases Wasm.prepare_floats w code true with hp | ⟨x, hp⟩
  · left
    refine ⟨?_, fun m ctx real => ?_⟩
    · unfold D3.contractOOD; rw [hp]
    · have hc : fuelCertified w code = fuelCertified { w with floats := true } code := by
        unfold fuelCertified; rw [hp]; rfl
      show vmCall wasmFuel w code m ctx real = vmCall wasmFuel { w with floats := true } code m ctx real
      unfold vmCall
      rw [hc, Wasm.runCallWithLimits_floats w true code m ctx _ true false (some real) hp.symm]
      rfl
  · right
    exact ⟨x, by unfold D3.contractOOD; rw [hp]⟩

/-- **O1, every configuration.** Switching floats on never changes a decided verdict: on the legacy
engine through the hooks (`Lift.floats_legacy`), on the whole-state engine through the recorded
call (`recRefine_floats`, `run_rec_mono`, the `*_apply_mono` shells). -/
theorem Lift.floats (cfg : ProtocolCfg) : Lift cfg { cfg with floats := true } := by
  intro c w
  cases hf : cfg.floats
  case true =>
    rw [ProtocolCfg.floats_true_eq cfg hf]
    exact Refines.refl _
  have hh : RecRefine cfg.wasm ({ cfg with floats := true } : ProtocolCfg).wasm := by
    rw [ProtocolCfg.wasm_floats cfg hf]
    exact recRefine_floats _
  have hk : HooksRefine (D3.d3Hooks cfg.wasm)
      (D3.d3Hooks ({ cfg with floats := true } : ProtocolCfg).wasm) := by
    rw [ProtocolCfg.wasm_floats cfg hf]
    exact d3Hooks_floats _
  obtain ⟨pv, fl, gc, gen, ll, sr, ga, cc, ch, rs, seg, wu, lu⟩ := cfg
  simp only at hf
  subst hf
  unfold checkSuccessor
  dsimp only
  split
  · refine Refines.ite_congr _ (fun _ => ?_) (fun _ => ?_)
    · cases rs
      · simp only [Bool.false_and, Bool.false_eq_true] at *
      · exact checkReshardCore_apply_mono _ _ _ _ (fun p e t vu ps rs txs cg => run_rec_mono hh p e t vu ps rs txs cg _ _) _ _ _ _
    · refine Refines.ite_congr _ (fun _ => ?_) (fun _ => ?_)
      · refine Refines.ite_congr _ (fun _ => ?_) (fun _ => ?_)
        · cases rs
          · exact checkD2CoreGWith_apply_mono _ _ _ _ (fun p e t vu ps rs txs cg => run_rec_mono hh p e t vu ps rs txs cg _ _) _ _ _ _
          · exact checkD2CoreGWith_apply_mono _ _ _ _ (fun p e t vu ps rs txs cg => run_rec_mono hh p e t vu ps rs txs cg _ _) _ _ _ _
        · cases rs
          · exact checkD2CoreWith_apply_mono _ _ _ _ (fun p e t vu ps rs txs cg => run_rec_mono hh p e t vu ps rs txs cg _ _) _ _ _ _
          · exact checkD2CoreWith_apply_mono _ _ _ _ (fun p e t vu ps rs txs cg => run_rec_mono hh p e t vu ps rs txs cg _ _) _ _ _ _
      · exact Refines.ite_congr _ (fun _ => checkD2CoreG_hooks_mono hk _ _ _ _)
          (fun _ => checkD2Core_hooks_mono hk _ _ _ _)
  · exact Refines.refl _

/-- `.storageResolution`-style whole-state pairs differing only in floats are covered by
`Lift.floats`; no named pair needs it, since every whole-state tier sets floats. -/
theorem Lift.floats_whole_example :
    Lift { Tier.cfg .storageResolution with floats := false } (Tier.cfg .storageResolution) :=
  Lift.floats _

#print axioms run_rec_mono
#print axioms checkD2CoreWithObs_apply_mono
#print axioms checkD2CoreGWith_apply_mono
#print axioms checkReshardCoreObs_apply_mono
#print axioms Lift.floats

end NearSpecV3.Successor
