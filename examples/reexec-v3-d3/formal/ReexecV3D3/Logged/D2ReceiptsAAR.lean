import ReexecV3D3.Logged.D2Receipts

/-! # `applyActionReceipt` mirror = original (lockstep; the largest D2 function) -/

namespace ReexecV3D3.Logged

open NearSpec NearSpecV3 NearSpecV3.D2

section
variable {s : HStore} {root : Bytes} (H : ActionHooks) (HL : ActionHooksL) (es : HStore)
  (hH : HooksR s root es H HL)
include hH

set_option maxHeartbeats 40000000 in
theorem R_applyActionReceipt (env : Env) (rs : RS) (r : Rcpt) (a : ActionR) :
    R s root (applyActionReceiptL HL env rs r a) (applyActionReceipt H (env.ws es) (rs.wt (preT s root)) r a)
      (fun p => (p.1.wt (preT s root), p.2)) := by
  unfold applyActionReceipt applyActionReceiptL; lk

end

section
variable {s : HStore} {root : Bytes}
theorem R_applyActionReceipt' (H : ActionHooks) (HL : ActionHooksL) {es : HStore} (hH : HooksR s root es H HL)
    (env : Env) {envO : Env} (he : envO = env.ws es) (rs : RS) {rsO : RS} (h : rsO = rs.wt (preT s root))
    (r : Rcpt) (a : ActionR) :
    R s root (applyActionReceiptL HL env rs r a) (applyActionReceipt H envO rsO r a)
      (fun p => (p.1.wt (preT s root), p.2)) := by
  subst he h; exact R_applyActionReceipt H HL es hH env rs r a
end

end ReexecV3D3.Logged
