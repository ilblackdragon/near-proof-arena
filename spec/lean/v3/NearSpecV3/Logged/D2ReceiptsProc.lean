import NearSpecV3.Logged.D2ReceiptsAAR

/-! # `process_receipt` and the instant-receipt loop: mirror = original -/

namespace NearSpecV3.Logged

open NearSpec NearSpecV3 NearSpecV3.D2

macro_rules | `(tactic| lk_call) => `(tactic| apply R_applyActionReceipt')

section
variable {s : HStore} {root : Bytes} (H : ActionHooks) (HL : ActionHooksL) (es : HStore)
  (hH : HooksR s root es H HL)
include hH

set_option maxHeartbeats 20000000 in
theorem R_processReceipt (env : Env) (rs : RS) (r : Rcpt) :
    R s root (processReceiptL HL env rs r) (processReceipt H (env.ws es) (rs.wt (preT s root)) r)
      (fun p => (p.1.wt (preT s root), p.2)) := by
  unfold processReceipt processReceiptL; lk

end

section
variable {s : HStore} {root : Bytes}
theorem R_processReceipt' (H : ActionHooks) (HL : ActionHooksL) {es : HStore} (hH : HooksR s root es H HL)
    (env : Env) {envO : Env} (he : envO = env.ws es) (rs : RS) {rsO : RS} (h : rsO = rs.wt (preT s root))
    (r : Rcpt) :
    R s root (processReceiptL HL env rs r) (processReceipt H envO rsO r) (fun p => (p.1.wt (preT s root), p.2)) := by
  subst he h; exact R_processReceipt H HL es hH env rs r
end

macro_rules | `(tactic| lk_call) => `(tactic| apply R_processReceipt')

section
variable {s : HStore} {root : Bytes} (H : ActionHooks) (HL : ActionHooksL) (es : HStore)
  (hH : HooksR s root es H HL)
include hH

theorem R_processWithTotals (env : Env) (rs : RS) (r : Rcpt) :
    R s root (processWithTotalsL HL env rs r) (processWithTotals H (env.ws es) (rs.wt (preT s root)) r)
      (·.wt (preT s root)) := by
  unfold processWithTotals processWithTotalsL; lk

end

section
variable {s : HStore} {root : Bytes}
theorem R_processWithTotals' (H : ActionHooks) (HL : ActionHooksL) {es : HStore} (hH : HooksR s root es H HL)
    (env : Env) {envO : Env} (he : envO = env.ws es) (rs : RS) {rsO : RS} (h : rsO = rs.wt (preT s root))
    (r : Rcpt) :
    R s root (processWithTotalsL HL env rs r) (processWithTotals H envO rsO r) (·.wt (preT s root)) := by
  subst he h; exact R_processWithTotals H HL es hH env rs r
end

macro_rules | `(tactic| lk_call) => `(tactic| apply R_processWithTotals')

section
variable {s : HStore} {root : Bytes} (H : ActionHooks) (HL : ActionHooksL) (es : HStore)
  (hH : HooksR s root es H HL)
include hH

theorem R_drain (env : Env) : ∀ (fuel : Nat) (rs : RS),
    R s root (processWithInstantL.drain HL env fuel rs)
      (processWithInstant.drain H (env.ws es) fuel (rs.wt (preT s root))) (·.wt (preT s root))
  | 0, rs => by unfold processWithInstant.drain processWithInstantL.drain; lk
  | fuel + 1, rs => by
    have ih := R_drain env fuel
    unfold processWithInstant.drain processWithInstantL.drain; lk

theorem R_processWithInstant (env : Env) (rs : RS) (r : Rcpt) :
    R s root (processWithInstantL HL env rs r) (processWithInstant H (env.ws es) (rs.wt (preT s root)) r)
      (·.wt (preT s root)) := by
  unfold processWithInstant processWithInstantL
  apply R_bind (R_processWithTotals H HL es hH env rs r)
  intro b
  exact R_drain H HL es hH env 100000 b

end

section
variable {s : HStore} {root : Bytes}
theorem R_processWithInstant' (H : ActionHooks) (HL : ActionHooksL) {es : HStore} (hH : HooksR s root es H HL)
    (env : Env) {envO : Env} (he : envO = env.ws es) (rs : RS) {rsO : RS} (h : rsO = rs.wt (preT s root))
    (r : Rcpt) :
    R s root (processWithInstantL HL env rs r) (processWithInstant H envO rsO r) (·.wt (preT s root)) := by
  subst he h; exact R_processWithInstant H HL es hH env rs r
end

macro_rules | `(tactic| lk_call) => `(tactic| apply R_processWithInstant')

end NearSpecV3.Logged
