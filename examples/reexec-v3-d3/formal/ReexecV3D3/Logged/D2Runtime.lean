import ReexecV3D3.Logged.Runtime.D2Runtime
import ReexecV3D3.Logged.D2ReceiptsProc
import NearSpecV3.D2.RuntimeD2

/-!
# Mirror of `D2/Validators.lean` and `D2/RuntimeD2.lean` in `LM`

The mirrors start from an overlay over a dummy trie (`dummyT`, never read): the pre-state is read
lazily from the root given to `LM`.
-/

namespace ReexecV3D3.Logged

open NearSpec NearSpecV3 NearSpecV3.D2

section
variable {s : HStore} {root : Bytes}

theorem R_validatorUpdate (l : Layout) (own : Nat) (o : Ovl) (f : ValidatorUpdateFacts) (last : List (Bytes × Nat)) :
    R s root (validatorUpdateL l own o f last) (validatorUpdate l own (o.wt (preT s root)) f last)
      (·.wt (preT s root)) := by
  unfold validatorUpdate validatorUpdateL; lk

theorem R_validatorUpdate' (l : Layout) (own : Nat) (o : Ovl) {oO : Ovl} (h : oO = o.wt (preT s root))
    (f : ValidatorUpdateFacts) (last : List (Bytes × Nat)) :
    R s root (validatorUpdateL l own o f last) (validatorUpdate l own oO f last) (·.wt (preT s root)) :=
  h ▸ R_validatorUpdate l own o f last

theorem R_schedOvl (prims : Prims) (ctx : ApplyCtx) (o : Ovl) {oO : Ovl} (h : oO = o.wt (preT s root)) :
    R s root (schedOvlL prims ctx o) (schedOvl prims ctx oO) (fun p => (p.1.wt (preT s root), p.2)) := by
  subst h; unfold schedOvl schedOvlL; lk

end

macro_rules | `(tactic| lk_call) => `(tactic| apply R_validatorUpdate')
macro_rules | `(tactic| lk_call) => `(tactic| apply R_schedOvl)

section
variable {s : HStore} {root : Bytes}

theorem R_processTxD2 (env : Env) (es : HStore) (rsSeen : RS × List Bytes) (tf : TxD2 × Bool) :
    R s root (processTxD2L env rsSeen tf) (processTxD2 (env.ws es) (rsSeen.1.wt (preT s root), rsSeen.2) tf)
      (fun p => (p.1.wt (preT s root), p.2)) := by
  unfold processTxD2 processTxD2L; lk

theorem R_processTxD2' (env : Env) {envO : Env} {es : HStore} (he : envO = env.ws es) (rsSeen : RS × List Bytes)
    {rsO : RS × List Bytes} (h : rsO = (rsSeen.1.wt (preT s root), rsSeen.2)) (tf : TxD2 × Bool) :
    R s root (processTxD2L env rsSeen tf) (processTxD2 envO rsO tf) (fun p => (p.1.wt (preT s root), p.2)) := by
  subst he h; exact R_processTxD2 env es rsSeen tf

end

macro_rules | `(tactic| lk_call) => `(tactic| apply R_processTxD2')

section
variable {s : HStore} {root : Bytes} (H : ActionHooks) (HL : ActionHooksL) (es : HStore)
  (hH : HooksR s root es H HL)
include hH

theorem R_processLocals (env : Env) (rs : RS) (locals : List Rcpt) :
    R s root (processLocalsL HL env rs locals) (processLocals H (env.ws es) (rs.wt (preT s root)) locals)
      (·.wt (preT s root)) := by
  unfold processLocals processLocalsL; lk

theorem R_processDelayed (env : Env) : ∀ (fuel : Nat) (rs : RS),
    R s root (processDelayedL HL env fuel rs) (processDelayed H (env.ws es) fuel (rs.wt (preT s root)))
      (·.wt (preT s root))
  | 0, rs => by unfold processDelayed processDelayedL; lk
  | fuel + 1, rs => by
    have ih := R_processDelayed env fuel
    unfold processDelayed processDelayedL; lk

theorem R_processIncoming (env : Env) (rs : RS) (incoming : List Rcpt) :
    R s root (processIncomingL HL env rs incoming) (processIncoming H (env.ws es) (rs.wt (preT s root)) incoming)
      (·.wt (preT s root)) := by
  unfold processIncoming processIncomingL; lk

end

section
variable {s : HStore} {root : Bytes}

theorem R_yieldLoop (env : Env) (es : HStore) (next : Nat) : ∀ (fuel : Nat) (acc : RS × Nat × Nat),
    R s root (yieldLoopL env next fuel acc) (yieldLoop (env.ws es) next fuel (acc.1.wt (preT s root), acc.2))
      (fun p => (p.1.wt (preT s root), p.2))
  | 0, (rs, i, k) => by unfold yieldLoop yieldLoopL; lk
  | fuel + 1, (rs, i, k) => by
    have ih := R_yieldLoop env es next fuel
    unfold yieldLoop yieldLoopL; lk

end

section
variable {s : HStore} {root : Bytes}
theorem R_processLocals' (H : ActionHooks) (HL : ActionHooksL) {es : HStore} (hH : HooksR s root es H HL)
    (env : Env) {envO : Env} (he : envO = env.ws es) (rs : RS) {rsO : RS} (h : rsO = rs.wt (preT s root))
    (l : List Rcpt) :
    R s root (processLocalsL HL env rs l) (processLocals H envO rsO l) (·.wt (preT s root)) := by
  subst he h; exact R_processLocals H HL es hH env rs l
theorem R_processDelayed' (H : ActionHooks) (HL : ActionHooksL) {es : HStore} (hH : HooksR s root es H HL)
    (env : Env) {envO : Env} (he : envO = env.ws es) (fuel : Nat) (rs : RS) {rsO : RS}
    (h : rsO = rs.wt (preT s root)) :
    R s root (processDelayedL HL env fuel rs) (processDelayed H envO fuel rsO) (·.wt (preT s root)) := by
  subst he h; exact R_processDelayed H HL es hH env fuel rs
theorem R_processIncoming' (H : ActionHooks) (HL : ActionHooksL) {es : HStore} (hH : HooksR s root es H HL)
    (env : Env) {envO : Env} (he : envO = env.ws es) (rs : RS) {rsO : RS} (h : rsO = rs.wt (preT s root))
    (l : List Rcpt) :
    R s root (processIncomingL HL env rs l) (processIncoming H envO rsO l) (·.wt (preT s root)) := by
  subst he h; exact R_processIncoming H HL es hH env rs l
theorem R_yieldLoop' (env : Env) {envO : Env} {es : HStore} (he : envO = env.ws es) (next fuel : Nat)
    (acc : RS × Nat × Nat) {accO : RS × Nat × Nat} (h : accO = (acc.1.wt (preT s root), acc.2)) :
    R s root (yieldLoopL env next fuel acc) (yieldLoop envO next fuel accO) (fun p => (p.1.wt (preT s root), p.2)) := by
  subst he h; exact R_yieldLoop env es next fuel acc
end

macro_rules | `(tactic| lk_call) => `(tactic| apply R_processLocals')
macro_rules | `(tactic| lk_call) => `(tactic| apply R_processDelayed')
macro_rules | `(tactic| lk_call) => `(tactic| apply R_processIncoming')
macro_rules | `(tactic| lk_call) => `(tactic| apply R_yieldLoop')
set_option hygiene false in
macro_rules | `(tactic| lk_ih) => `(tactic| apply R_finalize' hs)
macro_rules | `(tactic| lk_step) => `(tactic| apply R_bind_ok (ev_trieFindL _))

section
variable {s : HStore} {root : Bytes}

set_option maxHeartbeats 20000000 in
theorem R_applyNewChunkD2 (H : ActionHooks) (HL : ActionHooksL) (es : HStore) (hH : HooksR s root es H HL)
    (hs : HInv s) (prims : Prims) (env : Env) (vu : Option ValidatorUpdateFacts) (lp : List (Bytes × Nat))
    (inc : List Rcpt) (txs : List (TxD2 × Bool)) (oc : Congestion) :
    R s root (applyNewChunkD2L HL prims env vu lp inc txs oc)
      (applyNewChunkD2 H prims (env.ws es) (preT s root) vu lp inc txs oc) id := by
  unfold applyNewChunkD2 applyNewChunkD2L; lk

theorem R_applyMissingChunkD2 (hs : HInv s) (prims : Prims) (env : Env) (vu : Option ValidatorUpdateFacts)
    (lp : List (Bytes × Nat)) :
    R s root (applyMissingChunkD2L prims env vu lp) (applyMissingChunkD2 prims env (preT s root) vu lp) id := by
  unfold applyMissingChunkD2 applyMissingChunkD2L; lk

end

end ReexecV3D3.Logged
