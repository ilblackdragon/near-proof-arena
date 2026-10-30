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

namespace NearSpecV3.Successor.O4E
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Logged
open NearSpecV3.Successor
open NearSpecV3.Successor.StorageExecution (M Recording)

/-! ## Forwarding (G4) -/

/-- A logged program whose result is a logged mirror's result followed by a check that can only
fail with an escape. -/
theorem SimX.logged_post {α β : Type} {e : Env} {P : Recording → Prop} {φ : β → α} {x : Except String α}
    {n n0 : LM β} (hR : R e.store e.preRoot n0 x φ) (post : β → Except String β)
    (heq : LM.ev e.store e.preRoot n = LM.ev e.store e.preRoot n0 >>= post)
    (hpost : ∀ a, post a = .ok a ∨ ∃ s, esc s = true ∧ post a = .error s)
    (hRec : ∀ r keys, P r → P { r with recorder := recordReads e keys r.recorder }) :
    SimX e P φ x (StorageExecution.logged n) := by
  intro r hr
  unfold R at hR
  subst hR
  unfold SimAtX SimAt
  rw [logged_run, heq]
  cases h0 : LM.ev e.store e.preRoot n0 with
  | error err => exact Or.inl (Or.inr rfl)
  | ok a =>
    rcases hpost a with h | ⟨s, hs, h⟩
    · refine Or.inl ⟨a, _, ?_, rfl, hRec r (Logged.SM.reads (hGet e.store) (n e.preRoot)) hr⟩
      show (post a).map _ = _
      rw [h]; rfl
    · refine Or.inr ⟨s, hs, ?_⟩
      show (post a).map _ = _
      rw [h]; rfl

/-- An empty buffer forwards nothing. -/
theorem ev_fwdToShard_empty (s : HStore) (root : Bytes) (env : Env) (rs : RS) (p : Nat)
    (h : ¬ (bufGet rs.bufIdx p).1 < (bufGet rs.bufIdx p).2) :
    LM.ev s root (forwardFromBufferToShardL env rs p) = .ok rs := by
  unfold forwardFromBufferToShardL
  rcases hb : bufGet rs.bufIdx p with ⟨f, n⟩
  rw [hb] at h
  have hz : n - f = 0 := by simp only at h; omega
  simp only [hb, hz, fwdLoopL, LM.ev_bind, LM.ev_pure]
  rfl

theorem bufGet_outside {l : List (Nat × Nat × Nat)} {ids : List Nat} {p : Nat}
    (hany : ¬ (l.any (fun (s, f, n) => !ids.contains s && decide (f < n))) = true)
    (hp : ids.contains p = false) : ¬ (bufGet l p).1 < (bufGet l p).2 := by
  unfold bufGet
  cases hf : l.find? (·.1 == p) with
  | none => simp
  | some x =>
    rcases x with ⟨s, f, n⟩
    have hm := List.mem_of_find?_eq_some hf
    have hs := List.find?_some hf
    simp only [beq_iff_eq] at hs
    subst hs
    intro hlt
    simp only at hlt
    apply hany
    rw [List.any_eq_true]
    exact ⟨_, hm, by show (!ids.contains s && decide (f < n)) = true; rw [hp]; simp [hlt]⟩

theorem ite_post (c : Bool) (a : RS) :
    (if c = true then (Except.error escG4 : Except String RS) else .ok a) = .ok a ∨
      ∃ s, esc s = true ∧ (if c = true then (Except.error escG4 : Except String RS) else .ok a) = .error s := by
  cases c
  · exact Or.inl rfl
  · exact Or.inr ⟨escG4, esc_escG4, rfl⟩

/-- **G4.** Forwarding on every layout, up to the escape `escG4`. -/
theorem fwdSimX (e : Env) : FwdSimX e := by
  intro rs rsO h
  subst h
  unfold StorageExecution.forwardFromBufferR
  cases hl : e.ctx.layout.lastSplit with
  | none =>
    simp only [hl, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    exact SimX.of (Sim.logged (R_forwardFromBuffer' e rfl rs rfl) pt_rec)
  | some p =>
    simp only [hl, Option.isSome_some, ↓reduceIte]
    by_cases hany : (rs.bufIdx.any (fun (s, f, n) => !e.ctx.layout.shardIds.contains s && decide (f < n))) = true
    · have hx : forwardFromBuffer e (rs.wt (T e)) =
          .error "out of domain (c.same_layout): outgoing buffer to a shard outside the layout" := by
        unfold forwardFromBuffer
        simp only [RS.wt] at hany ⊢
        simp only [hany, ↓reduceIte]; rfl
      rw [hx]
      exact SimX.excl' _ (by ood_tac)
    · refine SimX.logged_post (R_forwardFromBuffer' e rfl rs rfl)
        (fun rs' => if ((match e.ctx.layout.lastSplit with
            | some p => if e.ctx.layout.shardIds.contains p then [] else [p]
            | none => []) ++ e.ctx.layout.shardIds).all (fun s => (bufGet rs'.bufIdx s).2 ≤ (bufGet rs'.bufIdx s).1)
            && rs'.cong.bufferedGas != 0 then .error escG4 else .ok rs') ?_ ?_ pt_rec
      · have hL : LM.ev e.store e.preRoot (forwardFromBufferL e rs) =
            LM.ev e.store e.preRoot (e.ctx.layout.shardIds.foldlM (forwardFromBufferToShardL e) rs) := by
          unfold forwardFromBufferL
          simp only [hany, Bool.false_eq_true, ↓reduceIte]
        rw [hL]
        unfold StorageExecution.forwardFromBufferV3L
        simp only [hl, Bool.false_eq_true, ↓reduceIte, LM.ev_bind]
        cases hc : e.ctx.layout.shardIds.contains p
        · simp only [Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append, List.foldlM_cons,
            LM.ev_bind, ev_fwdToShard_empty _ _ e rs p (bufGet_outside hany hc)]
          congr 1
          funext rs'
          split <;> rfl
        · simp only [↓reduceIte, List.nil_append]
          congr 1
          funext rs'
          split <;> rfl
      · exact fun a => ite_post _ a

#print axioms fwdSimX

/-! ## The bridge and the final theorem -/

/-- **`EngineAgreeX` holds**: the legacy engine is simulated by `NS` up to the escapes, on every
shell input. No premise. -/
theorem engineAgreeX (cfg : Wasm.NearCfg) : EngineAgreeX cfg := by
  refine engineAgreeX_of_simX cfg PT trivial fun merged p e vu ps rs txs cg he => ?_
  have hs : HInv e.store := by rw [he]; exact HInv_mkHStore merged
  exact simx_applyNewChunkD2 cfg hs p vu ps rs txs cg (fwdSimX e)

/-- **O4 (W12 item 5), under per-witness premises only.** On a witness file in the original format
whose codes fit one code response (`O4Witness`), `.runtimeLimits ⊑ .storageResolution` provided

* `hNS` (G1 soft limit, G6 VM recorder state): the storage-resolution checker's result equals the
  `NS` reference shell's on this witness;
* `hX` (G2, G3, G3b, G4, G7): the storage-resolution result is not one of the named escapes `esc`.

Both premises are decidable functions of `(c, w)`; `--o4-premises` reports them per case. -/
theorem relSuccessor_runtimeLimits_storageResolution (c w : Bytes) (hw : O4Witness w)
    (hNS : Tier.checker .storageResolution c w = checkNS c w)
    (hX : ∀ s, Tier.checker .storageResolution c w = .error s → esc s = false) :
    Refines (Tier.checker .runtimeLimits c w) (Tier.checker .storageResolution c w) :=
  refines_of_x (runtimeLimits_ns_of (engineAgreeX _) c w hw) hNS hX

/-- The verdict-level reading. -/
theorem verdict_runtimeLimits_storageResolution (c w : Bytes) (hw : O4Witness w)
    (hNS : Tier.checker .storageResolution c w = checkNS c w)
    (hX : ∀ s, Tier.checker .storageResolution c w = .error s → esc s = false)
    (hd : (checkVerdict (Tier.checker .runtimeLimits) c w).inDomain = true) :
    checkVerdict (Tier.checker .storageResolution) c w = checkVerdict (Tier.checker .runtimeLimits) c w :=
  Refines.verdict (relSuccessor_runtimeLimits_storageResolution c w hw hNS hX) hd

#print axioms engineAgreeX
#print axioms relSuccessor_runtimeLimits_storageResolution
#print axioms verdict_runtimeLimits_storageResolution

end NearSpecV3.Successor.O4E

namespace NearSpecV3.Successor.O4E
open NearSpec NearSpecV3 NearSpecV3.D2
open NearSpecV3.Successor

/-! ## Non-vacuity: a witness on which every premise holds

The premises are per witness, so the theorem is not vacuous as soon as one witness satisfies them.
The checks below run in the kernel (`decide +kernel`, no `ofReduceBool`). The witness is the empty
claim and witness file: both checkers stop at the same claim-decoding error. The measured data
(README §14) show the premises holding on real chunk witnesses as well. -/

/-- Boolean equality of `Except String Unit` results. -/
def eqU : Except String Unit → Except String Unit → Bool
  | .ok _, .ok _ => true
  | .error a, .error b => a == b
  | _, _ => false

theorem eqU_eq {x y : Except String Unit} (h : eqU x y = true) : x = y := by
  cases x <;> cases y <;> simp_all [eqU]

def decodesW (w : Bytes) : Bool :=
  match decodeWitnessFile w with
  | .ok _ => true
  | .error _ => false

theorem o4Witness_of {w : Bytes} (hc : isCWitnessFile w = false) (hd : decodesW w = false) : O4Witness w := by
  refine ⟨hc, fun sw codes h => ?_⟩
  simp [decodesW, h] at hd

theorem nv_sr : eqU (Tier.checker .storageResolution [] []) (.error "invalid claim: decode: truncated claim format") = true := by
  decide +kernel

theorem nv_ns : eqU (checkNS [] []) (.error "invalid claim: decode: truncated claim format") = true := by
  decide +kernel

theorem nv_esc : esc "invalid claim: decode: truncated claim format" = false := by decide +kernel

/-- **The premises of `relSuccessor_runtimeLimits_storageResolution` are satisfiable.** -/
theorem o4_premises_nonvacuous :
    ∃ c w : Bytes, O4Witness w ∧ Tier.checker .storageResolution c w = checkNS c w ∧
      ∀ s, Tier.checker .storageResolution c w = .error s → esc s = false := by
  refine ⟨[], [], o4Witness_of (by decide +kernel) (by decide +kernel), ?_, ?_⟩
  · rw [eqU_eq nv_sr, eqU_eq nv_ns]
  · intro s h
    rw [eqU_eq nv_sr] at h
    cases h
    exact nv_esc

#print axioms o4_premises_nonvacuous

end NearSpecV3.Successor.O4E
