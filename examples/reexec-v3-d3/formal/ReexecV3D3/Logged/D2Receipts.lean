import ReexecV3D3.Logged.Runtime.D2Receipts
import ReexecV3D3.Logged.D2Actions
import NearSpecV3.D2.Receipts

/-!
# Mirror of `D2/Receipts.lean` in `LM`
-/

namespace ReexecV3D3.Logged

open NearSpec NearSpecV3 NearSpecV3.D2

macro_rules | `(tactic| lk_call) => `(tactic| apply R_applyAction)
macro_rules | `(tactic| lk_call) => `(tactic| apply R_forwardOrBuffer')

section
variable {s : HStore} {root : Bytes} (H : ActionHooks) (HL : ActionHooksL) (es : HStore)
  (hH : HooksR s root es H HL)
include hH

theorem R_actionLoop (env : Env) (r : Rcpt) (a : ActionR) (inputs : List (Option Bytes))
    (deployed attempted : List Bytes) : ∀ (i : Nat) (acts : List Act) (acc : ActSt × AR),
    R s root (actionLoopL HL env r a inputs deployed attempted i acts acc)
      (actionLoop H (env.ws es) r a inputs deployed attempted i acts (acc.1.wt (preT s root), acc.2))
      (fun p => (p.1.wt (preT s root), p.2))
  | i, [], acc => by unfold actionLoop actionLoopL; lk
  | i, act :: rest, (st, res) => by
    have ih := R_actionLoop env r a inputs deployed attempted (i + 1) rest
    unfold actionLoop actionLoopL; lk

end

section
variable {s : HStore} {root : Bytes}

theorem R_emitReceipts (env : Env) (es : HStore) (parent : Bytes) : ∀ (rs : RS) (k : Nat) (l : List Rcpt),
    R s root (emitReceiptsL env parent rs k l) (emitReceipts (env.ws es) parent (rs.wt (preT s root)) k l)
      (fun p => (p.1.wt (preT s root), p.2))
  | rs, k, [] => by unfold emitReceipts emitReceiptsL; lk
  | rs, k, nr :: rest => by
    have ih := fun rs k => R_emitReceipts env es parent rs k rest
    unfold emitReceipts emitReceiptsL; lk

end


section
variable {s : HStore} {root : Bytes}
theorem R_actionLoop' (H : ActionHooks) (HL : ActionHooksL) {es : HStore} (hH : HooksR s root es H HL)
    (env : Env) {envO : Env} (he : envO = env.ws es) (r : Rcpt) (a : ActionR) (inputs : List (Option Bytes))
    (deployed attempted : List Bytes) (i : Nat) (acts : List Act) (acc : ActSt × AR) {accO : ActSt × AR}
    (h : accO = (acc.1.wt (preT s root), acc.2)) :
    R s root (actionLoopL HL env r a inputs deployed attempted i acts acc)
      (actionLoop H envO r a inputs deployed attempted i acts accO) (fun p => (p.1.wt (preT s root), p.2)) := by
  subst he h; exact R_actionLoop H HL es hH env r a inputs deployed attempted i acts acc
theorem R_emitReceipts' (env : Env) {envO : Env} {es : HStore} (he : envO = env.ws es) (parent : Bytes)
    (rs : RS) {rsO : RS} (h : rsO = rs.wt (preT s root)) (k : Nat) (l : List Rcpt) :
    R s root (emitReceiptsL env parent rs k l) (emitReceipts envO parent rsO k l)
      (fun p => (p.1.wt (preT s root), p.2)) := by
  subst he h; exact R_emitReceipts env es parent rs k l
end
macro_rules | `(tactic| lk_call) => `(tactic| apply R_actionLoop')
macro_rules | `(tactic| lk_call) => `(tactic| apply R_emitReceipts')

end ReexecV3D3.Logged
