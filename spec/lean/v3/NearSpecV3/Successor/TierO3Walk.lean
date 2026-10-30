import NearSpecV3.Successor.TierO3Rec

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-!
# W12 / O3 step 5f — the engine walk, `globalActions` off against on

`MRQ` with the non-distribution invariant `ND rs.outgoing` on every `RS`, on a well-formed layout
(`env.ctx.layout.WF` of the explicit environment), function by function as in `TierWholeWalk.lean`:

* queue and decoding steps: `fob_rr` (`forwardOrBuffer_eq` + `forwardOrBufferL_nd`), `delayPop_rr`,
  `ffb_rr`, `decRcpt_rr` (`decodeStoredRcpt_ref`), `processTxR_rr`, `liftE_refunds`;
* `actionLoop_rr`, `emitReceipts_rr`, `applyActionReceipt_rr`, `processReceipt_rr` (the lower run's
  distribution arm is `oodGcd`), `processWithTotals_rr`, `drain_rr`, `processWithInstant_rr`.

The walk tactic `mrw` extends `mrx` (`TierO3Rec.lean`) with `foldlM`, `bind_assoc` and a generic
bind (no value fact); closers are guarded (`with_reducible`, `lower_head`) so the unifier never
unfolds the two runs' programs.
-/

namespace NearSpecV3.Successor
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Logged NearSpecV3.Wasm StorageExecution HostComm

/-! ## The walk tactic of the engine -/

macro "mrw1" : tactic => `(tactic|
  (first
    | (lower_head Pure.pure; refine MRX.pure _ ?_; focus ((try dsimp only); ndc; done))
    | (lower_head MonadExcept.throw; exact MRX.throw_same _)
    | (lower_head throwThe; exact MRX.throwThe_same _)
    | mrx_close
    | (lower_head List.foldlM; refine MRX.foldlM (Q := fun x : RS => ND x.outgoing) _ _ (by assumption) fun _ _ _ => ?_)
    | (lower_head Bind.bind; first
        | (exact MRX.throw_bind_same _ _ _)
        | (simp only [pure_bind])
        | (simp only [bind_assoc])
        | ((refine MRX.bind (by mrx_close) fun _ _ => ?_); try dsimp only)
        | ((refine MRX.get_bind' fun _ _ _ => ?_); try dsimp only)
        | (lower_bind_has List.foldlM; first
            | ((refine MRX.bind (MRX.foldlM (Q := fun x : RS × List Bytes => ND x.1.outgoing) _ _ (by assumption)
                  fun _ _ _ => ?_) fun _ _ => ?_); try dsimp only)
            | ((refine MRX.bind (MRX.foldlM (Q := fun x : RS => ND x.outgoing) _ _ (by assumption)
                  fun _ _ _ => ?_) fun _ _ => ?_); try dsimp only)
            | ((refine MRX.bind (MRX.foldlM (Q := fun _ => True) _ _ trivial fun _ _ _ => ?_) fun _ _ => ?_);
                try dsimp only))
        | ((refine MRX.bind (Q := fun _ => True) ?_ fun _ _ => ?_); try dsimp only))
    | (lower_head ite; refine MRX.ite _ (fun _ => ?_) (fun _ => ?_))
    | (dsimp only)
    | (simp only [getR, getAcctR, getIndicesR, containsR, finalizeR, trieFindR, validatorUpdateR, schedOvlR, okR,
        softExceeded, modifyDetail, pushAttrib, setVmErr, startReceipt, accountRemovals, pipeDecode,
        bandwidthRequestsR, Bool.false_eq_true, Bool.not_false, Bool.not_true, ↓reduceIte])
    | (split <;> ((try simp_last_eq); (try dsimp only)))))

macro "mrw" : tactic => `(tactic| repeat' mrw1)

/-! ## The queue and decoding steps -/

section prims
variable {E : Env → Prop}

theorem fob_rr (env : Env) (hwf : env.ctx.layout.WF) (rs : RS) (r : Rcpt) (h : ND rs.outgoing)
    (hr : rcptIsDistribution r = false) :
    MRQ E (fun x : RS => ND x.outgoing) (forwardOrBufferR false env rs r) (forwardOrBufferR true env rs r) := by
  unfold forwardOrBufferR
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [forwardOrBuffer_eq env hwf rs r hr]
  exact MRX.loggedQ Exc.hX (LRQ.refl_of (forwardOrBufferL_nd env rs r h hr))

theorem delayPop_rr (env : Env) (hwf : env.ctx.layout.WF) (fuel : Nat) (rs : RS) (h : ND rs.outgoing) :
    MRQ E (fun x : RS × Option Rcpt => ND x.1.outgoing) (delayPopR false env fuel rs) (delayPopR true env fuel rs) := by
  unfold delayPopR
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact MRX.loggedQ Exc.hX (LRQ.of_LR (delayPop_rel env hwf fuel rs) (delayPopL_nd env fuel rs h))

theorem ffb_rr (env : Env) (hwf : env.ctx.layout.WF) (rs : RS) (h : ND rs.outgoing) :
    MRQ E (fun x : RS => ND x.outgoing) (forwardFromBufferR false env rs) (forwardFromBufferR true env rs) := by
  unfold forwardFromBufferR
  simp only [Bool.false_eq_true, ↓reduceIte]
  split
  · exact MRX.loggedQ Exc.hX (LRQ.of_LR (forwardFromBufferV3_rel env hwf rs) (forwardFromBufferV3L_nd env rs h))
  · exact MRX.loggedQ Exc.hX (LRQ.of_LR (forwardFromBuffer_rel env hwf rs) (forwardFromBufferL_nd env rs h))

theorem decRcpt_rr (b : Bytes) (what : String) :
    MRQ E (fun _ => True) (decodeStoredRcptR false b what) (decodeStoredRcptR true b what) := by
  unfold decodeStoredRcptR
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine MRX.liftE_ref (fun a h => ⟨(Codec.decodeStoredRcpt_ref b what).ok a h, trivial⟩) fun e h => ?_
  rcases Codec.decodeStoredRcpt_ref b what with h1 | ⟨e', h1, hX⟩
  · exact Or.inr (h1 ▸ h)
  · rw [h1] at h; cases h; exact Or.inl (Codec.shape_excl _ hX)

theorem processTxR_rr (env : Env) (rs : RS × List Bytes) (tf : TxD2 × Bool) (h : ND rs.1.outgoing) :
    MRQ E (fun x : RS × List Bytes => ND x.1.outgoing) (processTxR env rs tf) (processTxR env rs tf) := by
  unfold processTxR
  refine MRX.bind (MRX.loggedQ Exc.hX (LRQ.refl_of (processTxD2L_nd env rs tf h))) fun out hout => ?_
  mrw

end prims

theorem liftE_refunds {E : Env → Prop} (r : Rcpt) (a : ActionR) (res : AR) (purchase burn : Nat) (created : Bool) :
    MRQ E (fun x : List Rcpt × Nat => ND x.1) (StorageExecution.liftE (refunds r a res purchase burn created))
      (StorageExecution.liftE (refunds r a res purchase burn created)) :=
  MRX.liftE_ref (fun x hx => ⟨hx, refunds_nd r a res purchase burn created x hx⟩) fun _ h => Or.inr h

theorem ND.set {l : List Rcpt} (h : ND l) (k : Nat) {x : Rcpt} (hx : rcptIsDistribution x = false) :
    ND (l.set k x) := by
  intro r hr
  rcases List.mem_or_eq_of_mem_set hr with h1 | rfl
  · exact h r h1
  · exact hx

macro_rules | `(tactic| mrx_close) => `(tactic| with_reducible exact fob_rr _ ‹_› _ _ (by assumption) (by assumption))
macro_rules | `(tactic| mrx_close) => `(tactic| with_reducible exact delayPop_rr _ ‹_› _ _ (by assumption))
macro_rules | `(tactic| mrx_close) => `(tactic| with_reducible exact ffb_rr _ ‹_› _ (by assumption))
macro_rules | `(tactic| mrx_close) => `(tactic| with_reducible exact decRcpt_rr _ _)
macro_rules | `(tactic| mrx_close) => `(tactic| with_reducible exact processTxR_rr _ _ _ (by assumption))
macro_rules | `(tactic| mrx_close) => `(tactic| with_reducible exact applyAction_global _ ‹_› _ _ _ _)
macro_rules | `(tactic| mrx_close) => `(tactic| with_reducible exact liftE_refunds _ _ _ _ _ _)
macro_rules | `(tactic| mrx_close) => `(tactic| with_reducible exact MRX.loggedQ Exc.hX (LRQ.refl_of (delayPushL_nd _ _ (by assumption))))
macro_rules | `(tactic| mrx_close) => `(tactic| with_reducible exact MRX.modifyPipe pipeFn_startReceipt)
macro_rules | `(tactic| mrx_close) => `(tactic| with_reducible exact MRX.modifyPipe (pipeFn_recordDeploys _))
macro_rules | `(tactic| mrx_close) => `(tactic| with_reducible exact MRX.modifyPipe (pipeFn_startList _ _ (decLe_storedRcpt _) _ _))
macro_rules | `(tactic| mrx_close) => `(tactic| with_reducible exact MRX.modifyPipe (pipeFn_stepList _ _ (decLe_storedRcpt _) _))
macro_rules | `(tactic| mrx_close) => `(tactic| with_reducible exact MRX.modifyPipe (pipeFn_next _))
theorem exc_gcd : Exc oodGcd := Codec.shape_excl _ Codec.shape_gcd

macro_rules | `(tactic| mrx_close) => `(tactic| with_reducible exact MRX.throw_bind _ exc_gcd _ _)

/-- Leaf `ND` facts of the walk. -/
macro "ndw" : tactic => `(tactic| ((try simp only [AR.fail, List.append_nil, List.nil_append] at *); repeat' (first | assumption | exact ND.nil | exact ND.single rfl | exact ND.map (fun _ => rfl) _ | refine ND.set ?_ _ rfl | refine ND.append ?_ ?_)))

/-! ## The walk -/

section walk
variable {E : Env → Prop} (w : NearCfg) (hg : w.globalActions = false) (p : CodeWitnessPolicy)
include hg

theorem actionLoop_rr (env : Env) (r : Rcpt) (a : ActionR) (inputs : List (Option Bytes))
    (deployed attempted : List Bytes) :
    ∀ (acts : List Act) (i : Nat) (acc : ActSt × AR), ND acc.2.newReceipts →
    MRQ E (fun x : ActSt × AR => ND x.2.newReceipts)
      (StorageExecution.actionLoop ⟨false, p⟩ w env r a inputs deployed attempted i acts acc)
      (StorageExecution.actionLoop ⟨true, p⟩ { w with globalActions := true } env r a inputs deployed attempted i acts acc)
  | [], _, _, h => MRX.pure _ h
  | act :: rest, i, (st, res), h => by
    unfold StorageExecution.actionLoop
    dsimp only at h
    mrw
    all_goals refine actionLoop_rr env r a inputs deployed attempted rest _ _ ?_
    all_goals simp only [AR.fail, List.append_nil]
    all_goals first | exact h | exact ND.append h ‹_›

macro_rules | `(tactic| mrx_close) => `(tactic| with_reducible exact actionLoop_rr _ ‹_› _ _ _ _ _ _ _ _ _ _ (by first | exact ND.nil | assumption))

omit hg in
theorem emitReceipts_rr (env : Env) (hwf : env.ctx.layout.WF) (parent : Bytes) :
    ∀ (l : List Rcpt) (rs : RS) (k : Nat), ND rs.outgoing → ND l →
    MRQ E (fun x : RS × List Bytes => ND x.1.outgoing)
      (StorageExecution.emitReceipts false env parent rs k l) (StorageExecution.emitReceipts true env parent rs k l)
  | [], _, _, h, _ => MRX.pure _ h
  | nr :: rest, rs, k, h, hl => by
    have hr : rcptIsDistribution { nr with rid := receiptIdFrom parent env.ctx.height k } = false :=
      hl nr List.mem_cons_self
    have hrest : ND rest := hl.sub fun x hx => List.mem_cons_of_mem _ hx
    unfold StorageExecution.emitReceipts
    dsimp only
    refine MRX.ite _ (fun _ => ?_) (fun _ => ?_)
    · simp only [pure_bind]
      exact MRX.bind (emitReceipts_rr env hwf parent rest _ (k + 1) h hrest) fun x hx => MRX.pure _ hx
    · exact MRX.bind (fob_rr env hwf rs _ h hr) fun rs' h' =>
        MRX.bind (emitReceipts_rr env hwf parent rest rs' (k + 1) h' hrest) fun x hx => MRX.pure _ hx

macro_rules | `(tactic| mrx_close) => `(tactic| with_reducible exact emitReceipts_rr _ ‹_› _ _ _ _ (by assumption) (by ndw))

theorem applyActionReceipt_rr (env : Env) (hwf : env.ctx.layout.WF) (rs : RS) (r : Rcpt) (a : ActionR)
    (h : ND rs.outgoing) :
    MRQ E (fun x : RS × OutD1 × Nat => ND x.1.outgoing)
      (StorageExecution.applyActionReceipt ⟨false, p⟩ w env rs r a)
      (StorageExecution.applyActionReceipt ⟨true, p⟩ { w with globalActions := true } env rs r a) := by
  unfold StorageExecution.applyActionReceipt
  mrw

macro_rules | `(tactic| mrx_close) => `(tactic| with_reducible exact applyActionReceipt_rr _ ‹_› _ _ ‹_› _ _ _ (by assumption))

theorem processReceipt_rr (env : Env) (hwf : env.ctx.layout.WF) (rs : RS) (r : Rcpt) (h : ND rs.outgoing) :
    MRQ E (fun x : RS × Option (OutD1 × Nat) => ND x.1.outgoing)
      (StorageExecution.processReceipt ⟨false, p⟩ w env rs r)
      (StorageExecution.processReceipt ⟨true, p⟩ { w with globalActions := true } env rs r) := by
  unfold StorageExecution.processReceipt
  mrw

macro_rules | `(tactic| mrx_close) => `(tactic| with_reducible exact processReceipt_rr _ ‹_› _ _ ‹_› _ _ (by assumption))

theorem processWithTotals_rr (env : Env) (hwf : env.ctx.layout.WF) (rs : RS) (r : Rcpt) (h : ND rs.outgoing) :
    MRQ E (fun x : RS => ND x.outgoing)
      (StorageExecution.processWithTotals ⟨false, p⟩ w env rs r)
      (StorageExecution.processWithTotals ⟨true, p⟩ { w with globalActions := true } env rs r) := by
  unfold StorageExecution.processWithTotals
  mrw

macro_rules | `(tactic| mrx_close) => `(tactic| with_reducible exact processWithTotals_rr _ ‹_› _ _ ‹_› _ _ (by assumption))

theorem drain_rr (env : Env) (hwf : env.ctx.layout.WF) :
    ∀ (fuel : Nat) (rs : RS), ND rs.outgoing →
    MRQ E (fun x : RS => ND x.outgoing)
      (StorageExecution.processWithInstant.drain ⟨false, p⟩ w env fuel rs)
      (StorageExecution.processWithInstant.drain ⟨true, p⟩ { w with globalActions := true } env fuel rs)
  | 0, _, _ => MRX.throw_same _
  | fuel + 1, rs, h => by
    unfold StorageExecution.processWithInstant.drain
    mrw
    all_goals exact drain_rr env hwf fuel _ ‹_›

theorem processWithInstant_rr (env : Env) (hwf : env.ctx.layout.WF) (rs : RS) (r : Rcpt) (h : ND rs.outgoing) :
    MRQ E (fun x : RS => ND x.outgoing)
      (StorageExecution.processWithInstant ⟨false, p⟩ w env rs r)
      (StorageExecution.processWithInstant ⟨true, p⟩ { w with globalActions := true } env rs r) := by
  unfold StorageExecution.processWithInstant
  exact MRX.bind (processWithTotals_rr w hg p env hwf rs r h) fun x hx => drain_rr w hg p env hwf _ x hx

#print axioms applyActionReceipt_rr
#print axioms processWithInstant_rr

end walk

end NearSpecV3.Successor
