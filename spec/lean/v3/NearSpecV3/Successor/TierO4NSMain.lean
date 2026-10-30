import NearSpecV3.Successor.TierO4NSSim

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-!
# W12 / O4 — the `NS` receipt loops, forwarding, main transition and the final theorem (README §14)

Continues `TierO4NSSim.lean`: the four receipt loops without the soft-limit test, the V3 forwarding
(G4), the main transition, the bridge to `EngineAgreeX`, and
`relSuccessor_runtimeLimits_storageResolution` under the two per-witness premises.
-/

namespace NearSpecV3.Successor.O4E
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Logged
open NearSpecV3.Successor
open NearSpecV3.Successor.StorageExecution (M Recording)
open NearSpecV3.Wasm NearSpecV3.D3

/-! ## The receipt loops, without the soft-limit test (G1 is the `NS` premise) -/

set_option hygiene false in
/-- `recv_walk` for `SimX` and `NS`. -/
macro "recvx_walk" : tactic => `(tactic|
  repeat (first
    | (exact SimX.of (Sim.pure rfl))
    | (exact SimX.of (Sim.ok rfl))
    | (exact SimX.of (Sim.throw _))
    | (exact SimX.of (Sim.error _))
    | (refine SimX.of (err_bind rfl fun _ => ?_); rfl)
    | (exact simx_processWithInstant cfg _ _ _ (by rfl))
    | (exact ih _ _ (by rfl))
    | (exact ih _ _ _ (by rfl))
    | (refine SimX.bind (simx_processWithInstant cfg _ _ _ (by rfl)) fun _ => ?_)
    | (exact SimX.of (Sim.logged (R_delayPush' _ (by rfl) _) pt_rec))
    | (exact SimX.of (Sim.logged (R_forwardOrBuffer' _ (by rfl) _ (by rfl) _) pt_rec))
    | (refine SimX.bind (SimX.of (Sim.logged (R_forwardOrBuffer' _ (by rfl) _ (by rfl) _) pt_rec)) fun _ => ?_)
    | (refine SimX.bind (SimX.of (Sim.logged (R_delayPop' _ (by rfl) _ _ (by rfl)) pt_rec)) fun _ => ?_; dsimp only)
    | (with_reducible refine SimX.get_all fun _ => ?_)
    | (refine SimX.bind_id (SimX.of (Sim.logged (R_get' _ (by rfl) _ _) pt_rec)) fun _ => ?_)
    | (refine SimX.bind_id (SimX.of (Sim.logged (R_contains' _ (by rfl) _ _) pt_rec)) fun _ => ?_)
    | (refine SimX.bind_id (SimX.of (Sim.okR _ _)) fun _ => ?_)
    | (refine SimX.book pt_frame (Book.modifyPipe _) ?_)
    | (refine SimX.book pt_frame Book.pipeDecode ?_)
    | (refine SimX.book pt_frame (Book.scheduleDelayed _ _) ?_)
    | (refine SimX.ite _ (fun _ => ?_) (fun _ => ?_))
    | (split <;> (rename_i hsplit; (try simp only [hsplit]); (try dsimp only)))))

section loops
variable {e : Env}

theorem simx_processLocals (cfg : NearCfg) (rs rsO : RS) (l : List Rcpt) (h : rsO = rs.wt (T e)) :
    SimX e PT (·.wt (T e)) (D2.processLocals (D3.d3Hooks cfg) e rsO l)
      (StorageExecutionNS.processLocals cfg e rs l) := by
  subst h
  unfold D2.processLocals StorageExecutionNS.processLocals
  refine SimX.book pt_frame Book.pipeDecode ?_
  refine SimX.book pt_frame (Book.modifyPipe _) ?_
  refine SimX.foldlM' (fun b c => ?_) l rfl
  recvx_walk
  all_goals done

theorem simx_processIncoming (cfg : NearCfg) (rs rsO : RS) (l : List Rcpt) (h : rsO = rs.wt (T e)) :
    SimX e PT (·.wt (T e)) (D2.processIncoming (D3.d3Hooks cfg) e rsO l)
      (StorageExecutionNS.processIncoming cfg e rs l) := by
  subst h
  unfold D2.processIncoming StorageExecutionNS.processIncoming
  refine SimX.book pt_frame Book.pipeDecode ?_
  refine SimX.book pt_frame (Book.modifyPipe _) ?_
  refine SimX.foldlM' (fun b c => ?_) l rfl
  recvx_walk
  all_goals done

theorem simx_processDelayedLoop (cfg : NearCfg) :
    ∀ (fuel : Nat) (rs rsO : RS), rsO = rs.wt (T e) →
    SimX e PT (·.wt (T e)) (D2.processDelayed (D3.d3Hooks cfg) e fuel rsO)
      (StorageExecutionNS.processDelayedLoop cfg e fuel rs)
  | 0, rs, rsO, h => by
    subst h
    unfold D2.processDelayed StorageExecutionNS.processDelayedLoop
    exact SimX.of (Sim.ok rfl)
  | fuel + 1, rs, rsO, h => by
    subst h
    have ih := simx_processDelayedLoop cfg fuel
    unfold D2.processDelayed StorageExecutionNS.processDelayedLoop
    simp only [StorageExecution.delayPopR]
    recvx_walk
    all_goals done

theorem simx_processDelayed (cfg : NearCfg) (fuel : Nat) (rs rsO : RS) (h : rsO = rs.wt (T e)) :
    SimX e PT (·.wt (T e)) (D2.processDelayed (D3.d3Hooks cfg) e fuel rsO)
      (StorageExecutionNS.processDelayed cfg e fuel rs) := by
  unfold StorageExecutionNS.processDelayed
  exact SimX.book pt_frame (Book.scheduleDelayed _ _) (simx_processDelayedLoop cfg fuel rs rsO h)

theorem simx_yieldLoop (cfg : NearCfg) (next : Nat) :
    ∀ (fuel : Nat) (acc accO : RS × Nat × Nat), accO = (acc.1.wt (T e), acc.2) →
    SimX e PT (fun p => (p.1.wt (T e), p.2)) (D2.yieldLoop e next fuel accO)
      (StorageExecutionNS.yieldLoop e next fuel acc)
  | 0, (rs, i, k), accO, h => by
    subst h
    unfold D2.yieldLoop StorageExecutionNS.yieldLoop
    exact SimX.of (Sim.ok rfl)
  | fuel + 1, (rs, i, k), accO, h => by
    subst h
    have ih := simx_yieldLoop cfg next fuel
    unfold D2.yieldLoop StorageExecutionNS.yieldLoop
    simp only [StorageExecution.getR, StorageExecution.containsR, StorageExecution.forwardOrBufferR]
    recvx_walk
    all_goals done

end loops

#print axioms simx_processLocals
#print axioms simx_yieldLoop

/-! ## The main transition and the bridge -/

/-- The forwarding obligation up to the escapes. -/
def FwdSimX (e : Env) : Prop :=
  ∀ rs rsO, rsO = rs.wt (T e) → SimX e PT (·.wt (T e)) (forwardFromBuffer e rsO)
    (StorageExecution.forwardFromBufferR false e rs)

set_option hygiene false in
/-- `main_walk` for `SimX` and `NS`. -/
macro "mainx_walk" : tactic => `(tactic|
  repeat (first
    | (exact SimX.of (Sim.pure rfl))
    | (exact SimX.of (Sim.ok rfl))
    | (exact SimX.of (Sim.throw _))
    | (exact SimX.of (Sim.error _))
    | (exact SimX.of (throw_bind _))
    | (refine SimX.of (err_bind rfl fun _ => ?_); rfl)
    | (refine SimX.of (Sim.get fun r0 hr0 => ⟨_, r0, rfl, rfl, hr0⟩))
    | (refine SimX.bind (SimX.of (Sim.pure (φ := fun o : Ovl => o.wt (T _)) rfl)) fun _ => ?_)
    | (refine SimX.bind_id (SimX.of (Sim.logged (R_getIndices' _ (by rfl) _ _) pt_rec)) fun _ => ?_)
    | (refine SimX.bind (SimX.of (Sim.logged (R_schedOvl _ _ _ (by rfl)) pt_rec)) fun _ => ?_)
    | (refine SimX.bind_id (SimX.of (Sim.logged (R_bandwidthRequests' _ (by rfl) _ (by rfl)) pt_rec)) fun _ => ?_)
    | (refine SimX.bind_id (SimX.of (Sim.logged (R_finalize' hs _ (by rfl)) pt_rec)) fun _ => ?_)
    | (refine SimX.bind (hFwd _ _ (by rfl)) fun _ => ?_)
    | (refine SimX.bind (simx_processLocals cfg _ _ _ (by rfl)) fun _ => ?_)
    | (refine SimX.bind (simx_processDelayed cfg _ _ _ (by rfl)) fun _ => ?_)
    | (refine SimX.bind (simx_processIncoming cfg _ _ _ (by rfl)) fun _ => ?_)
    | (refine SimX.bind (simx_yieldLoop cfg _ _ _ _ (by rfl)) fun _ => ?_)
    | (refine SimX.bind (SimX.foldlM' (fun b c => SimX.of (sim_processTxR pt_frame pt_rec b c)) _ rfl) fun _ => ?_)
    | (refine SimX.bind_id (SimX.foldlM' (φ := id) (fun b c => ?_) _ rfl) fun _ => ?_)
    | (refine SimX.logged_ok_bind (ev_trieFindL _) pt_rec ?_; try simp only [ovl_wt_trie, T])
    | (refine SimX.bind_id (SimX.of (Sim.liftE _)) fun _ => ?_)
    | (refine SimX.bind_id (SimX.of (Sim.okR _ _)) fun _ => ?_)
    | (refine SimX.ite _ (fun _ => ?_) (fun _ => ?_))
    | (split <;> (rename_i hsplit; (try simp only [hsplit]); (try dsimp only)))))

set_option maxHeartbeats 16000000 in
/-- **The main transition of `NS`**, up to the escapes, given the forwarding step. -/
theorem simx_applyNewChunkD2 {e : Env} (cfg : NearCfg) (hs : HInv e.store) (prims : Prims)
    (vu : Option ValidatorUpdateFacts) (ps : List (Bytes × Nat))
    (inc : List Rcpt) (txs : List (TxD2 × Bool)) (cg : Congestion) (hFwd : FwdSimX e) :
    SimX e PT obsClear (D2.applyNewChunkD2 (D3.d3Hooks cfg) prims e (T e) vu ps inc txs cg)
      (StorageExecutionNS.applyNewChunkD2 cfg prims e (T e) vu ps inc txs cg) := by
  unfold D2.applyNewChunkD2 StorageExecutionNS.applyNewChunkD2
  simp only [StorageExecution.validatorUpdateR, StorageExecution.getIndicesR, StorageExecution.schedOvlR,
    StorageExecution.trieFindR, StorageExecution.finalizeR, bandwidthRequestsR_eq]
  cases vu with
  | none =>
    dsimp only
    mainx_walk
    all_goals done
  | some f =>
    dsimp only
    refine SimX.bind (SimX.of (Sim.logged (R_validatorUpdate' _ _ _ (by rfl) _ _) pt_rec)) fun _ => ?_
    mainx_walk
    all_goals done

#print axioms simx_applyNewChunkD2

end NearSpecV3.Successor.O4E
