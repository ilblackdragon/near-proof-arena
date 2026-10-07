import ReexecV3D3.Logged.WasmCR

/-! # `CR` for the non-storage host helpers -/

namespace ReexecV3D3.Logged.W

open NearSpecV3.Wasm

theorem CR_withGas (σ : TTN.Store) (f : Gas → Gas × Option String) : CR σ (withGas f) (withGas f) := by
  unfold withGas; cr

macro_rules | `(tactic| cr_call) => `(tactic| apply CR_withGas)

theorem CR_payBaseH (σ : TTN.Store) (c : Cost) : CR σ (payBaseH c) (payBaseH c) := by
  unfold payBaseH; cr

macro_rules | `(tactic| cr_call) => `(tactic| apply CR_payBaseH)

theorem CR_payPerH (σ : TTN.Store) (c : Cost) (n : Nat) : CR σ (payPerH c n) (payPerH c n) := by
  unfold payPerH; cr

macro_rules | `(tactic| cr_call) => `(tactic| apply CR_payPerH)

theorem CR_payActionH (σ : TTN.Store) (b bc u : Nat) : CR σ (payActionH b bc u) (payActionH b bc u) := by
  unfold payActionH; cr

macro_rules | `(tactic| cr_call) => `(tactic| apply CR_payActionH)

theorem CR_burnH (σ : TTN.Store) (x : Nat) : CR σ (burnH x) (burnH x) := by
  unfold burnH; cr

macro_rules | `(tactic| cr_call) => `(tactic| apply CR_burnH)

theorem CR_hErr (σ : TTN.Store) {α : Type} (e : String) : CR σ ((hErr e : HM α)) ((hErr e : HM α)) := by
  unfold hErr; cr

macro_rules | `(tactic| cr_call) => `(tactic| apply CR_hErr)

theorem CR_readMemH (σ : TTN.Store) (p l : Nat) : CR σ (readMemH p l) (readMemH p l) := by
  unfold readMemH; cr

macro_rules | `(tactic| cr_call) => `(tactic| apply CR_readMemH)

theorem CR_writeMemH (σ : TTN.Store) (p : Nat) (d : ByteArray) : CR σ (writeMemH p d) (writeMemH p d) := by
  unfold writeMemH; cr

macro_rules | `(tactic| cr_call) => `(tactic| apply CR_writeMemH)

theorem CR_regGetH (σ : TTN.Store) (i : Nat) : CR σ (regGetH i) (regGetH i) := by
  unfold regGetH; cr

macro_rules | `(tactic| cr_call) => `(tactic| apply CR_regGetH)

theorem CR_regSetH (σ : TTN.Store) (i : Nat) (d : ByteArray) (cb : Bool) : CR σ (regSetH i d cb) (regSetH i d cb) := by
  unfold regSetH; cr

macro_rules | `(tactic| cr_call) => `(tactic| apply CR_regSetH)

theorem CR_memOrRegH (σ : TTN.Store) (p l : Nat) : CR σ (memOrRegH p l) (memOrRegH p l) := by
  unfold memOrRegH; cr

macro_rules | `(tactic| cr_call) => `(tactic| apply CR_memOrRegH)

theorem CR_getU128H (σ : TTN.Store) (p : Nat) : CR σ (getU128H p) (getU128H p) := by
  unfold getU128H; cr

macro_rules | `(tactic| cr_call) => `(tactic| apply CR_getU128H)

theorem CR_setU128H (σ : TTN.Store) (p v : Nat) : CR σ (setU128H p v) (setU128H p v) := by
  unfold setU128H; cr

macro_rules | `(tactic| cr_call) => `(tactic| apply CR_setU128H)

theorem CR_logLenExceeded (σ : TTN.Store) {α : Type} (a : Nat) : CR σ ((logLenExceeded a : HM α)) ((logLenExceeded a : HM α)) := by
  unfold logLenExceeded; cr

macro_rules | `(tactic| cr_call) => `(tactic| apply CR_logLenExceeded)

theorem CR_utf8H (σ : TTN.Store) (l p : Nat) : CR σ (utf8H l p) (utf8H l p) := by
  unfold utf8H; cr

macro_rules | `(tactic| cr_call) => `(tactic| apply CR_utf8H)

theorem CR_utf16H (σ : TTN.Store) (l p : Nat) : CR σ (utf16H l p) (utf16H l p) := by
  unfold utf16H; cr

macro_rules | `(tactic| cr_call) => `(tactic| apply CR_utf16H)

theorem CR_checkCanLogH (σ : TTN.Store)  : CR σ (checkCanLogH) (checkCanLogH) := by
  unfold checkCanLogH; cr

macro_rules | `(tactic| cr_call) => `(tactic| apply CR_checkCanLogH)

theorem CR_pushLogH (σ : TTN.Store) (m : String) : CR σ (pushLogH m) (pushLogH m) := by
  unfold pushLogH; cr

macro_rules | `(tactic| cr_call) => `(tactic| apply CR_pushLogH)

theorem CR_guestPanic (σ : TTN.Store) {α : Type} (m : String) : CR σ ((guestPanic m : HM α)) ((guestPanic m : HM α)) := by
  unfold guestPanic; cr

macro_rules | `(tactic| cr_call) => `(tactic| apply CR_guestPanic)

theorem CR_readAccountIdH (σ : TTN.Store) (l p : Nat) : CR σ (readAccountIdH l p) (readAccountIdH l p) := by
  unfold readAccountIdH; cr

macro_rules | `(tactic| cr_call) => `(tactic| apply CR_readAccountIdH)

theorem CR_pushAction (σ : TTN.Store) (a : MAct) : CR σ (pushAction a) (pushAction a) := by
  unfold pushAction; cr

macro_rules | `(tactic| cr_call) => `(tactic| apply CR_pushAction)

theorem CR_pushPromiseH (σ : TTN.Store) (p : PromiseV) : CR σ (pushPromiseH p) (pushPromiseH p) := by
  unfold pushPromiseH; cr

macro_rules | `(tactic| cr_call) => `(tactic| apply CR_pushPromiseH)

theorem CR_promiseReceiptH (σ : TTN.Store) (i : Nat) : CR σ (promiseReceiptH i) (promiseReceiptH i) := by
  unfold promiseReceiptH; cr

macro_rules | `(tactic| cr_call) => `(tactic| apply CR_promiseReceiptH)

theorem CR_payGasKeyAddH (σ : TTN.Store) (sir : Bool) (a b n : Nat) : CR σ (payGasKeyAddH sir a b n) (payGasKeyAddH sir a b n) := by
  unfold payGasKeyAddH; cr

macro_rules | `(tactic| cr_call) => `(tactic| apply CR_payGasKeyAddH)

theorem CR_payActionBaseH (σ : TTN.Store) (f : Fee3) (sir : Bool) : CR σ (payActionBaseH f sir) (payActionBaseH f sir) := by
  unfold payActionBaseH; cr

macro_rules | `(tactic| cr_call) => `(tactic| apply CR_payActionBaseH)

theorem CR_payActionPerByteH (σ : TTN.Store) (f : Fee3) (n : Nat) (sir : Bool) : CR σ (payActionPerByteH f n sir) (payActionPerByteH f n sir) := by
  unfold payActionPerByteH; cr

macro_rules | `(tactic| cr_call) => `(tactic| apply CR_payActionPerByteH)

theorem CR_payNewReceiptH (σ : TTN.Store) (sir : Bool) (d : Array Bool) : CR σ (payNewReceiptH sir d) (payNewReceiptH sir d) := by
  unfold payNewReceiptH; cr

macro_rules | `(tactic| cr_call) => `(tactic| apply CR_payNewReceiptH)

theorem CR_deductBalanceH (σ : TTN.Store) (a : Nat) : CR σ (deductBalanceH a) (deductBalanceH a) := by
  unfold deductBalanceH; cr

macro_rules | `(tactic| cr_call) => `(tactic| apply CR_deductBalanceH)

theorem CR_popArgs (σ : TTN.Store) (n : Nat) : CR σ (popArgs n) (popArgs n) := by
  unfold popArgs; cr

macro_rules | `(tactic| cr_call) => `(tactic| apply CR_popArgs)

theorem CR_pushRet (σ : TTN.Store) (v : Nat) (b : Bool) : CR σ (pushRet v b) (pushRet v b) := by
  unfold pushRet; cr

macro_rules | `(tactic| cr_call) => `(tactic| apply CR_pushRet)

theorem CR_realPutH (σ : TTN.Store) (k : ByteArray) (v : Option ByteArray) : CR σ (realPutH k v) (realPutH k v) := by
  unfold realPutH; cr

macro_rules | `(tactic| cr_call) => `(tactic| apply CR_realPutH)

theorem CR_thenDataIdsH (σ : TTN.Store) (n : Nat) : CR σ (thenDataIdsH n) (thenDataIdsH n) := by
  unfold thenDataIdsH; cr

macro_rules | `(tactic| cr_call) => `(tactic| apply CR_thenDataIdsH)

theorem CR_hashHost (σ : TTN.Store) (a b : Cost) (h : ByteArray → ByteArray) (l p r : Nat) : CR σ (hashHost a b h l p r) (hashHost a b h l p r) := by
  unfold hashHost; cr

macro_rules | `(tactic| cr_call) => `(tactic| apply CR_hashHost)

theorem CR_functionCallActionH (σ : TTN.Store) (i ml mp al ap amt g w : Nat) : CR σ (functionCallActionH i ml mp al ap amt g w) (functionCallActionH i ml mp al ap amt g w) := by
  unfold functionCallActionH; cr

macro_rules | `(tactic| cr_call) => `(tactic| apply CR_functionCallActionH)

theorem CR_readContractIdH (σ : TTN.Store) (b : Bool) (l p : Nat) : CR σ (readContractIdH b l p) (readContractIdH b l p) := by
  unfold readContractIdH; cr

macro_rules | `(tactic| cr_call) => `(tactic| apply CR_readContractIdH)

theorem CR_deployGlobalH (σ : TTN.Store) (a : Vector Nat 3) : CR σ (deployGlobalH a) (deployGlobalH a) := by
  unfold deployGlobalH; cr

macro_rules | `(tactic| cr_call) => `(tactic| apply CR_deployGlobalH)

theorem CR_useGlobalH (σ : TTN.Store) (b : Bool) (a : Vector Nat 3) : CR σ (useGlobalH b a) (useGlobalH b a) := by
  unfold useGlobalH; cr

macro_rules | `(tactic| cr_call) => `(tactic| apply CR_useGlobalH)

theorem CR_stateInitH (σ : TTN.Store) (b : Bool) (a : Vector Nat 4) : CR σ (stateInitH b a) (stateInitH b a) := by
  unfold stateInitH; cr

macro_rules | `(tactic| cr_call) => `(tactic| apply CR_stateInitH)

end ReexecV3D3.Logged.W
