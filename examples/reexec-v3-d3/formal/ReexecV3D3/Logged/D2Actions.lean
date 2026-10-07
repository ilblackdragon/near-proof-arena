import ReexecV3D3.Logged.Runtime.D2Actions
import ReexecV3D3.Logged.D2QueuesSpec
import NearSpecV3.D2.Actions

/-!
# Mirror of `D2/Actions.lean` in `LM`
-/

namespace ReexecV3D3.Logged

open NearSpec NearSpecV3 NearSpecV3.D2


/-- The hooks are related: the mirror hook computes the original one on the related states. -/
def HooksR (s : HStore) (root : Bytes) (es : HStore) (H : ActionHooks) (HL : ActionHooksL) : Prop :=
  ∀ (c : ActCtx) (st : ActSt) (ar : AR) (b : Base),
    R s root (HL.functionCall c st ar b) (H.functionCall (c.ws es) (st.wt (preT s root)) ar b)
      (fun p => (p.1.wt (preT s root), p.2))

section
variable {s : HStore} {root : Bytes}

theorem HooksR_d2 (es : HStore) : HooksR s root es d2Hooks d2HooksL := by
  intro c st ar b; exact R_error _

theorem R_contractUsage (o : Ovl) (a : Bytes) (x : Acct) :
    R s root (contractUsageL o a x) (contractUsage (o.wt (preT s root)) a x) id := by
  unfold contractUsage contractUsageL; lk

theorem R_needAcct (st : ActSt) : R s root (needAcctL st) (needAcct (st.wt (preT s root))) id := by
  unfold needAcct needAcctL; lk

theorem R_akKeysOf (o : Ovl) (a : Bytes) :
    R s root (akKeysOfL o a) (akKeysOf (o.wt (preT s root)) a) id := by
  unfold akKeysOf akKeysOfL; lk

end

section
variable {s : HStore} {root : Bytes}
theorem R_contractUsage' (o : Ovl) {oO : Ovl} (h : oO = o.wt (preT s root)) (a : Bytes) (x : Acct) :
    R s root (contractUsageL o a x) (contractUsage oO a x) id := h ▸ R_contractUsage o a x
theorem R_needAcct' (st : ActSt) {stO : ActSt} (h : stO = st.wt (preT s root)) :
    R s root (needAcctL st) (needAcct stO) id := h ▸ R_needAcct st
theorem R_akKeysOf' (o : Ovl) {oO : Ovl} (h : oO = o.wt (preT s root)) (a : Bytes) :
    R s root (akKeysOfL o a) (akKeysOf oO a) id := h ▸ R_akKeysOf o a
end
macro_rules | `(tactic| lk_call) => `(tactic| apply R_contractUsage')
macro_rules | `(tactic| lk_call) => `(tactic| apply R_needAcct')
macro_rules | `(tactic| lk_call) => `(tactic| apply R_akKeysOf')

section
variable {s : HStore} {root : Bytes}

theorem R_gasKeyBalanceSum (o : Ovl) (a : Bytes) :
    R s root (gasKeyBalanceSumL o a) (gasKeyBalanceSum (o.wt (preT s root)) a) id := by
  unfold gasKeyBalanceSum gasKeyBalanceSumL; lk

end

section
variable {s : HStore} {root : Bytes}
theorem R_gasKeyBalanceSum' (o : Ovl) {oO : Ovl} (h : oO = o.wt (preT s root)) (a : Bytes) :
    R s root (gasKeyBalanceSumL o a) (gasKeyBalanceSum oO a) id := h ▸ R_gasKeyBalanceSum o a
end
macro_rules | `(tactic| lk_call) => `(tactic| apply R_gasKeyBalanceSum')

section
variable {s : HStore} {root : Bytes} (es : HStore)


theorem R_actDeleteAccount (c : ActCtx) (st : ActSt) (res : AR) (ben : Bytes) :
    R s root (actDeleteAccountL c st res ben) (actDeleteAccount (c.ws es) (st.wt (preT s root)) res ben) (fun p => (p.1.wt (preT s root), p.2)) := by
  unfold actDeleteAccount actDeleteAccountL; lk

theorem R_actAddKey (c : ActCtx) (st : ActSt) (res : AR) (pk : PublicKey) (ak : AK) :
    R s root (actAddKeyL c st res pk ak) (actAddKey (c.ws es) (st.wt (preT s root)) res pk ak) (fun p => (p.1.wt (preT s root), p.2)) := by
  unfold actAddKey actAddKeyL; lk

theorem R_actDeleteKey (c : ActCtx) (st : ActSt) (res : AR) (pk : PublicKey) :
    R s root (actDeleteKeyL c st res pk) (actDeleteKey (c.ws es) (st.wt (preT s root)) res pk) (fun p => (p.1.wt (preT s root), p.2)) := by
  unfold actDeleteKey actDeleteKeyL; lk

theorem R_actStake (c : ActCtx) (st : ActSt) (res : AR) (stake : Nat) (pk : PublicKey) :
    R s root (actStakeL c st res stake pk) (actStake (c.ws es) (st.wt (preT s root)) res stake pk) (fun p => (p.1.wt (preT s root), p.2)) := by
  unfold actStake actStakeL; lk

theorem R_actTransfer (c : ActCtx) (st : ActSt) (res : AR) (dep : Nat) :
    R s root (actTransferL c st res dep) (actTransfer (c.ws es) (st.wt (preT s root)) res dep) (fun p => (p.1.wt (preT s root), p.2)) := by
  unfold actTransfer actTransferL; lk

theorem R_actDeploy (c : ActCtx) (st : ActSt) (res : AR) (code : Bytes) :
    R s root (actDeployL c st res code) (actDeploy (c.ws es) (st.wt (preT s root)) res code) (fun p => (p.1.wt (preT s root), p.2)) := by
  unfold actDeploy actDeployL; lk

theorem R_actToGasKey (c : ActCtx) (st : ActSt) (res : AR) (pk : PublicKey) (dep : Nat) :
    R s root (actToGasKeyL c st res pk dep) (actToGasKey (c.ws es) (st.wt (preT s root)) res pk dep) (fun p => (p.1.wt (preT s root), p.2)) := by
  unfold actToGasKey actToGasKeyL; lk

theorem R_actFromGasKey (c : ActCtx) (st : ActSt) (res : AR) (pk : PublicKey) (amt : Nat) :
    R s root (actFromGasKeyL c st res pk amt) (actFromGasKey (c.ws es) (st.wt (preT s root)) res pk amt) (fun p => (p.1.wt (preT s root), p.2)) := by
  unfold actFromGasKey actFromGasKeyL; lk

theorem R_actCreateAccount (c : ActCtx) (st : ActSt) (res : AR) :
    R s root (actCreateAccountL c st res) (actCreateAccount (c.ws es) (st.wt (preT s root)) res) (fun p => (p.1.wt (preT s root), p.2)) := by
  unfold actCreateAccount actCreateAccountL; lk

set_option maxHeartbeats 2000000 in
theorem R_actDelegate (c : ActCtx) (st : ActSt) (res : AR) (d : Delegate) :
    R s root (actDelegateL c st res d) (actDelegate (c.ws es) (st.wt (preT s root)) res d) (fun p => (p.1.wt (preT s root), p.2)) := by
  unfold actDelegate actDelegateL; lk

end

macro_rules | `(tactic| lk_call) => `(tactic| apply R_actDeleteAccount)
macro_rules | `(tactic| lk_call) => `(tactic| apply R_actAddKey)
macro_rules | `(tactic| lk_call) => `(tactic| apply R_actDeleteKey)
macro_rules | `(tactic| lk_call) => `(tactic| apply R_actStake)
macro_rules | `(tactic| lk_call) => `(tactic| apply R_actTransfer)
macro_rules | `(tactic| lk_call) => `(tactic| apply R_actDeploy)
macro_rules | `(tactic| lk_call) => `(tactic| apply R_actToGasKey)
macro_rules | `(tactic| lk_call) => `(tactic| apply R_actFromGasKey)
macro_rules | `(tactic| lk_call) => `(tactic| apply R_actCreateAccount)
macro_rules | `(tactic| lk_call) => `(tactic| apply R_actDelegate)

section
variable {s : HStore} {root : Bytes}

theorem R_applyAction (H : ActionHooks) (HL : ActionHooksL) (es : HStore) (hH : HooksR s root es H HL)
    (c : ActCtx) (st : ActSt) (act : Act) :
    R s root (applyActionL HL c st act) (applyAction H (c.ws es) (st.wt (preT s root)) act)
      (fun p => (p.1.wt (preT s root), p.2)) := by
  unfold applyAction applyActionL; lk

end

end ReexecV3D3.Logged
